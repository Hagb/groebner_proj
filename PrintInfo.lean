import Lean
import Std.Data.HashSet.Basic
import Lean.Data.DeclarationRange
import Lean.Data.Json
import Groebner.Defs
import Groebner.Ideal
import Groebner.Basic
import Groebner.Set
import Groebner.Submodule

def mods := [`Groebner.Defs, `Groebner.Ideal, `Groebner.Basic, `Groebner.Set, `Groebner.Submodule]



open Lean

structure DefInfo where
  name : Name
  docstring : Option String
  uses : NameSet
  isThm : Bool
  module : Name
  isSorry : Bool
  pos : Option Position



def isOriginal (s : Name) : Bool := !(s.isInternalDetail || s.isImplementationDetail || s.isInternalOrNum)

-- #eval Submodule.add_mem
def getOriginal (s : Name) : Name :=
  if isOriginal s then
    s
  else
    match s with
    | Name.str p _ => getOriginal p
    | Name.num p _ => getOriginal p
    | Name.anonymous => s

partial def expandUses (range : NameSet) (env: Environment) (used : Name) (s : Name): NameSet :=
  let range := (range.erase s).erase used
  if isOriginal used then
    NameSet.empty.insert used
  else
    let original := getOriginal used
    if original == s then
    match env.find? used with
    | some info =>
      let expanded := NameSet.ofList <|
        (info.getUsedConstantsAsSet ∩ range).toList.flatMap
        fun x => (expandUses range env x s).toList
      if original == s then
        expanded
      else
        expanded.insert original
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
  let env ← getEnv
  let consts := env.constants

  -- to exclude compiler constants like `instMonadOption._cstage1`
  let safeConsts := consts.toList.filter fun info => !info.snd.isUnsafe

  let ourDefs := safeConsts.filter fun info =>
    match env.getModuleFor? info.fst with
    | some e => e ∈ mods && (info.snd.isDef || info.snd.isThm) && info.snd.value?.isSome
    | _ => false

  let names := NameSet.ofList (ourDefs.map fun info => info.fst)
  let defInfos : List DefInfo ←
    (ourDefs.filter fun x => isOriginal x.fst).mapM fun info => do
    return {
      name := info.fst,
      docstring := ← findDocString? env info.fst,
      uses := NameSet.filter isOriginal <| NameSet.ofList <|
        (info.snd.getUsedConstantsAsSet ∩ names).toList.flatMap <|
        fun x => (expandUses names env x info.fst).toList,
      isThm := info.snd.isTheorem,
      module := (env.getModuleFor? info.fst).get!,
      isSorry := (info.snd.getUsedConstantsAsSet.find? ``sorryAx).isSome
      pos := (←Lean.findDeclarationRanges? info.fst).map (fun x => x.range.pos)

    }

  let defInfosJson : Json := Json.arr <|
    (defInfos.toArray.heapSort defSort).map <|
    fun d =>
    Json.mkObj [
      ("name", Json.str d.name.toString),
      ("docstring", match d.docstring with | some x => Json.str x | _ => Json.null),
      ("uses", Json.arr <| d.uses.toArray.map <| fun x => Json.str x.toString),
      ("isThm", Json.bool d.isThm),
      ("module", Json.str d.module.toString),
      ("isSorry", Json.bool d.isSorry),
      ("pos", match d.pos with | some p => Json.num p.line | _ => Json.null)
    ]

  println! defInfosJson
<<<<<<< HEAD

=======
  IO.FS.writeFile "defInfos.json" (toString defInfosJson)
>>>>>>> 6caf977cabe35ded956af765a333267d9614905f

#check ``sorryAx
