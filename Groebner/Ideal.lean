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
import Mathlib.Tactic.RewriteSearch
-- import Mathlib.Data.Set.Basic



namespace Ideal

section Ideal
variable {R : Type _} [Semiring R]

theorem fg_span_iff_fg_span_finset_subset (s : Set R) :
  (span s).FG ↔ ∃ (s' : Finset R), s'.toSet ⊆ s ∧ span s = span s' := by
  sorry

end Ideal


section MvPolynomial
open Ideal MvPolynomial

variable {σ : Type*} {m : MonomialOrder σ} {s : σ →₀ ℕ}
variable {k : Type*} [Field k] variable (p : MvPolynomial σ k)
variable (G': Finset (MvPolynomial σ k)) (G'': Set (MvPolynomial σ k))
variable (I I₁ I₂ : Ideal (MvPolynomial σ k))
variable {R : Type _} [CommSemiring R]

-- @[simp]
lemma a (c : k) : MvPolynomial.monomial s c =
  MvPolynomial.monomial 0 c * MvPolynomial.monomial s 1 := by
  -- rw_search
  sorry
  -- rw [@MvPolynomial.monomial_zero', @MvPolynomial.C_mul_monomial, @NonAssocRing.mul_one]

open Finsupp


lemma leading_term_ideal_span_monomial : span (m.leadingTerm '' G') =
  span ((fun p => MvPolynomial.monomial (m.degree p) (1 : k)) '' (G'' \ {0})) := by
  -- simp [MonomialOrder.leadingTerm]
  sorry

lemma remainder_mem_ideal_iff {G': Finset (MvPolynomial σ k)} {r : MvPolynomial σ k}
  {I : Ideal (MvPolynomial σ k)}
  (h : G'.toSet ⊆ I) (hG' : m.IsRemainder p G' r) :
  r ∈ I ↔ p ∈ I := by
  sorry

lemma rem_sub_rem_mem_ideal {G': Finset (MvPolynomial σ k)} {p r₁ r₂ : MvPolynomial σ k}
  (hG' : G'.toSet ⊆ I) (hr₁ : m.IsRemainder p G' r₁) (hr₂ : m.IsRemainder p G' r₂) :
  r₁-r₂ ∈ I :=
  sorry


end MvPolynomial
end Ideal
