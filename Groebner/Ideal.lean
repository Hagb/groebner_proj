import Mathlib -- TODO: should be removed later
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.Data.Set.Finite.Basic
import Groebner.Defs
-- import Groebner.MonomialOrder
import Mathlib.Tactic.RewriteSearch
-- import Mathlib.Data.Set.Basic
import Groebner.Submodule

namespace Ideal

section Ideal
variable {R : Type _} [Semiring R]

theorem fg_span_iff_fg_span_finset_subset (s : Set R) :
  (span s).FG ↔ ∃ (s' : Finset R), s'.toSet ⊆ s ∧ span s = span s' := by
  sorry

-- to Mathlib
@[simp]
lemma span_singleton_zero : span {(0 : R)} = ⊥ :=
  Submodule.span_zero_singleton _

-- to Mathlib
@[simp]
lemma span_insert_zero (s : Set R): span (insert 0 s) = span s :=
  Submodule.span_insert_zero

-- to Mathlib
@[simp]
lemma span_sdiff_singleton_zero (s : Set R): span (s \ {0}) = span s := Submodule.span_sdiff_singleton_zero _ _

end Ideal


section MvPolynomial
open Ideal
open MvPolynomial
open Classical

variable {σ : Type*} {m : MonomialOrder σ} {s : σ →₀ ℕ}
variable {k : Type*} [Field k] variable (p p₁ p₂ : MvPolynomial σ k)
variable (G': Finset (MvPolynomial σ k)) (G'': Set (MvPolynomial σ k))
variable (I I₁ I₂ : Ideal (MvPolynomial σ k))
variable {R : Type _} [CommSemiring R]

open Finsupp
open Finset
open Submodule
open Ideal
open Field

lemma leadingTerm_ideal_span_monomial {G'': Set (MvPolynomial σ R)}
  (hG'' : ∀ p ∈ G'', IsUnit (m.leadingCoeff p)) :
  span (m.leadingTerm '' G'') = span ((fun p => MvPolynomial.monomial (m.degree p) (1 : R)) '' G'') := by
  apply le_antisymm
  · rintro p hl
    simp only [MonomialOrder.leadingTerm, ← submodule_span_eq, mem_span_image_iff_exists_fun] at *
    rcases hl with ⟨t, ht, c, hc⟩
    rw [←hc]
    use t
    split_ands
    · exact ht
    ·
      use fun (p : _) => (MvPolynomial.C (m.leadingCoeff ↑p : R) : MvPolynomial σ R) • c ↑p
      -- simp?
      apply Finset.sum_congr rfl
      simp
      intro a ha
      rw [mul_assoc, mul_left_comm, MvPolynomial.C_mul_monomial, mul_one]
  ·
    rintro p hl
    simp only [MonomialOrder.leadingTerm, ← submodule_span_eq, mem_span_image_iff_exists_fun] at *
    rcases hl with ⟨t, ht, c, hc⟩
    rw [←hc]
    use t
    split_ands
    · exact ht
    ·
      use fun (p : _) => if hp : ↑p ∈ G'' then ((hG'' (↑p) (hp)).unit)⁻¹ • c ↑p else 0
      apply Finset.sum_congr rfl
      ·
        -- simp?
        simp only [univ_eq_attach, mem_attach, smul_eq_mul, Algebra.smul_mul_assoc, forall_const,
          Subtype.forall]
        intro a ha
        simp [Set.mem_of_mem_of_subset ha ht]
        rw [smul_mul_assoc, ←mul_smul_comm, MvPolynomial.smul_monomial, IsUnit.inv_smul]

lemma leadingTerm_ideal_span_monomial' : span (m.leadingTerm '' G'') =
  span ((fun p => MvPolynomial.monomial (m.degree p) (1 : k)) '' (G'' \ {(0 : MvPolynomial σ k)})) := by
  calc
    _ = span (m.leadingTerm '' G'' \ {0}) := (span_sdiff_singleton_zero _).symm
    _ = span (m.leadingTerm '' (G'' \ {0})) := by rw [m.leadingTerm_image_sdiff_singleton_zero]
    _ = _ := by
      apply leadingTerm_ideal_span_monomial
      simp

lemma remainder_mem_ideal_iff {G'': Set (MvPolynomial σ R)} {r : MvPolynomial σ R}
  {I : Ideal (MvPolynomial σ R)} {p : MvPolynomial σ R}
  (hG'' : ∀ g ∈ G'', IsUnit (m.leadingCoeff g))
  (hG''I : G'' ⊆ I) (hpG''r : m.IsRemainder p G'' r) :
  r ∈ I ↔ p ∈ I := by
  sorry -- easy or normal

lemma remainder_mem_ideal_iff' {G'': Set (MvPolynomial σ k)} {r : MvPolynomial σ k}
  {I : Ideal (MvPolynomial σ k)} {p : MvPolynomial σ k}
  (h : G'' ⊆ I) (hpG''r : m.IsRemainder p G'' r) :
  r ∈ I ↔ p ∈ I := by
  refine remainder_mem_ideal_iff (G'':=G''\{0}) (m:=m) ?_ ?_ ?_
  ·sorry -- easy
  ·sorry -- easy
  ·sorry -- easy

lemma remainder_sub_remainder_mem_ideal {R : Type _} [CommRing R]
  {G'': Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)} {p r₁ r₂ : MvPolynomial σ R}
  (hG'' : ∀ g ∈ G'', IsUnit (m.leadingCoeff g))
  (hG''I : G'' ⊆ I) (hr₁ : m.IsRemainder p G'' r₁) (hr₂ : m.IsRemainder p G'' r₂) :
  r₁-r₂ ∈ I := by
  sorry -- normal

lemma remainder_sub_remainder_mem_ideal' {G'': Set (MvPolynomial σ k)} {p r₁ r₂ : MvPolynomial σ k}
  (hG'' : G'' ⊆ I) (hr₁ : m.IsRemainder p G'' r₁) (hr₂ : m.IsRemainder p G'' r₂) :
  r₁-r₂ ∈ I := by
  refine remainder_sub_remainder_mem_ideal (G'':=G''\{0}) (m:=m) (p:=p) (r₁:=r₁) (r₂:=r₂) ?_ ?_ ?_ ?_
  · sorry --easy
  · sorry --easy
  · sorry --easy
  · sorry --easy


end MvPolynomial
end Ideal
