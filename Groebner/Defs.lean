import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.Ideal.Span


namespace MonomialOrder

open MvPolynomial
variable {σ : Type*} (m : MonomialOrder σ)

section Semiring
variable {R : Type*} [CommSemiring R]

noncomputable def leadingTerm (f : MvPolynomial σ R) : MvPolynomial σ R :=
  monomial (m.degree f) (m.leadingCoeff f)

def IsRemainder (p : MvPolynomial σ R) (G' : Finset (MvPolynomial σ R)) (r : MvPolynomial σ R)
  := ∃ (g : G' →₀ (MvPolynomial σ R)),
      p = Finsupp.linearCombination _ (fun (g' : G') ↦ (g' : MvPolynomial σ R)) g + r ∧
      (∀ (g' : G'), m.degree ((g' : MvPolynomial σ R) * (g g')) ≼[m] m.degree p) ∧
      (∀ c ∈ r.support, ∀ g' ∈ G', ¬ (m.degree g' ≤ c))

lemma lm_eq_zero_iff (p : MvPolynomial σ R): m.leadingTerm p = 0 ↔ p = 0 := by
  simp only [leadingTerm, monomial_eq_zero, leadingCoeff_eq_zero_iff]

lemma leadingTerm_image_sdiff_singleton_zero (m : MonomialOrder σ) (G'' : Set (MvPolynomial σ R)) :
  m.leadingTerm '' (G''\ {0}) = (m.leadingTerm '' G'') \ {0} := by
  apply subset_antisymm
  · intro p
    simp
    intro q hq hq' hpq
    exact ⟨⟨q, hq, hpq⟩, hpq ▸ (m.lm_eq_zero_iff _).not.mpr hq'⟩
  · intro p
    simp
    intro q hq hpq hp
    rw [←hpq, MonomialOrder.lm_eq_zero_iff] at hp
    exact ⟨q, ⟨hq, hp⟩, hpq⟩

end Semiring


section Field

variable {s : σ →₀ ℕ} {k : Type _} [Field k]

noncomputable def SPolynomial (f g : MvPolynomial σ k) : MvPolynomial σ k :=
  monomial (m.degree g - m.degree f) ((m.leadingCoeff f)⁻¹) * f -
  monomial (m.degree f - m.degree g) ((m.leadingCoeff g)⁻¹) * g

def IsGroebnerBasis (G': Finset (MvPolynomial σ k)) (I : Ideal (MvPolynomial σ k)) :=
  G'.toSet ⊆ I ∧
  Ideal.span (m.leadingTerm '' ↑I)
    = Ideal.span (m.leadingTerm '' G'.toSet)
