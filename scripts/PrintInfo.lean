import Lean
import Std.Data.HashSet.Basic
import Lean.Data.DeclarationRange
import Lean.Data.Json
import Lean.Data.NameMap
import Batteries.Data.NameSet
import Batteries.Data.BinaryHeap
import ImportGraph.RequiredModules
import Groebner.Defs
import Groebner.Ideal
import Groebner.Basic
import Groebner.Set
import Groebner.Submodule
def mods := #[`Groebner.Defs, `Groebner.Ideal, `Groebner.Basic, `Groebner.Set, `Groebner.Submodule]

open Lean
structure DefInfo where
  name : Name
  docstring : Option String
  statementUses : NameSet
  proofUses : NameSet
  isThm : Bool
  module : Name
  statementSorry : Bool
  proofSorry : Bool
  pos : Option Position

def isOriginal (s : Name) : Bool :=
  !(s.isInternalDetail || s.isImplementationDetail || s.isInternalOrNum || s.isAnonymous)

-- #eval Submodule.add_mem
def getOriginal (s : Name) : Name :=
  if isOriginal s then
    s
  else
    match s with
    | Name.str p _ => getOriginal p
    | Name.num p _ => getOriginal p
    | Name.anonymous => s

partial def expandUses (range : NameSet) (excluded : NameSet) (env: Environment) (used : Name) (s : Name) (statement : Bool) : NameSet :=
  if isOriginal used then
    NameSet.empty.insert used
  else
    let original := getOriginal used
    /- !isOriginal original : deal with _private.... -/
    if original == s || !isOriginal original then
      let excluded := (excluded.insert s).insert used
      match env.find? used with
      | some info =>
        let usedByUsed := if statement then info.type.getUsedConstantsAsSet else info.getUsedConstantsAsSet
        let expanded := (usedByUsed \ range).union <| NameSet.ofList <|
          ((usedByUsed ∩ range) \ excluded).toList.flatMap
          fun x => (expandUses range excluded env x s statement).toList.append
            <| if statement then (expandUses range excluded env x s false).toList else []
        expanded
      | _ => panic! ""
    else
      NameSet.empty.insert original

def defSort (a b : DefInfo) : Bool :=
  match Ord.arrayOrd.compare
    #[mods.findIdx (a.module==·), (a.pos.map (·.line)).getD 0]
    #[mods.findIdx (b.module==·), (b.pos.map (·.line)).getD 0]
    with
    | Ordering.lt => true
    | _ => false

run_meta do
  enableInitializersExecution
  let env ← getEnv
  let consts := env.constants

  -- refer to https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Listing.20all.20identifiers/near/513859402
  -- to exclude compiler constants like `instMonadOption._cstage1`
  let safeConsts := consts.toList.filter fun info => !info.snd.isUnsafe

  let ourDefs := safeConsts.filter fun info =>
    match env.getModuleFor? info.fst with
    | some e => e ∈ mods
    | _ => false

  let names := NameSet.ofList (ourDefs.map fun info => info.fst)
  let defInfos : List DefInfo ←
    (ourDefs.filter fun x =>
      isOriginal x.fst && (x.snd.isDefinition || x.snd.isTheorem) && x.snd.value?.isSome
    ).mapM fun info => do
      let proofUses := NameSet.ofList <|
          (info.snd.getUsedConstantsAsSet ∩ names).toList.flatMap <|
          fun x => (expandUses names {} env x info.fst false).toList
      let proofSorry := (proofUses.find? ``sorryAx).isSome || (info.snd.getUsedConstantsAsSet.find? ``sorryAx).isSome
      let statementUses := NameSet.ofList <|
          (info.snd.type.getUsedConstantsAsSet ∩ names).toList.flatMap <|
          fun x => (expandUses names {} env x info.fst true).toList
      let statementSorry := (statementUses.find? ``sorryAx).isSome ||
        (info.snd.type.getUsedConstantsAsSet.find? ``sorryAx).isSome
      let ourStatementUses := statementUses ∩ names
      pure {
        name := info.fst,
        docstring := ← findDocString? env info.fst,
        statementUses := ourStatementUses,
        proofUses := (proofUses ∩ names) \ ourStatementUses,
        isThm := info.snd.isTheorem,
        module := (env.getModuleFor? info.fst).get!,
        proofSorry := proofSorry
        statementSorry := statementSorry
        pos := (←Lean.findDeclarationRanges? info.fst).map (fun x => x.range.pos)

      }

  let defInfosJson : Json := Json.arr <|
    (defInfos.toArray.heapSort defSort).map <|
    fun d =>
    Json.mkObj [
      ("name", Json.str d.name.toString),
      ("docstring", match d.docstring with | some x => Json.str x | _ => Json.null),
      ("statementUses", Json.arr <| d.statementUses.toArray.map <| fun x => Json.str x.toString),
      ("proofUses", Json.arr <| d.proofUses.toArray.map <| fun x => Json.str x.toString),
      ("isThm", Json.bool d.isThm),
      ("module", Json.str d.module.toString),
      ("proofSorry", Json.bool d.proofSorry),
      ("statementSorry", Json.bool d.statementSorry),
      ("pos", match d.pos with | some p => Json.num p.line | _ => Json.null)
    ]

  IO.FS.writeFile "scripts/defInfos.json" (toString defInfosJson)

  println! defInfosJson
