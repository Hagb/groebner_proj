import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.Ideal.Span


namespace MonomialOrder

open MvPolynomial
variable {σ : Type*} (m : MonomialOrder σ)

section CommSemiring
variable {R : Type*} [CommSemiring R]

noncomputable def leadingTerm (f : MvPolynomial σ R) : MvPolynomial σ R :=
  monomial (m.degree f) (m.leadingCoeff f)

def IsRemainder (p : MvPolynomial σ R) (G'' : Set (MvPolynomial σ R)) (r : MvPolynomial σ R)
  := ∃ (g : G'' →₀ (MvPolynomial σ R)),
      p = Finsupp.linearCombination _ (fun (g' : G'') ↦ (g' : MvPolynomial σ R)) g + r ∧
      (∀ (g' : G''), m.degree ((g' : MvPolynomial σ R) * (g g')) ≼[m] m.degree p) ∧
      (∀ c ∈ r.support, ∀ g' ∈ G'', g' ≠ 0 → ¬ (m.degree g' ≤ c))

lemma lm_eq_zero_iff (p : MvPolynomial σ R): m.leadingTerm p = 0 ↔ p = 0 := by
  simp only [leadingTerm, monomial_eq_zero, leadingCoeff_eq_zero_iff]

lemma leadingTerm_image_sdiff_singleton_zero (G'' : Set (MvPolynomial σ R)) :
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

lemma isRemainder_of_insert_zero_iff_isRemainder (p : MvPolynomial σ R)
  (G'' : Set (MvPolynomial σ R)) (r : MvPolynomial σ R) :
  m.IsRemainder p (insert 0 G'') r ↔ m.IsRemainder p G'' r := by
  sorry  -- normal

lemma isRemainder_of_singleton_zero_iff_isRemainder (p : MvPolynomial σ R)
  (G'' : Set (MvPolynomial σ R)) (r : MvPolynomial σ R) :
  m.IsRemainder p (G'' \ {0}) r ↔ m.IsRemainder p G'' r := by
  -- easy.
  -- tips: refer to the proof of `Submodule.span_sdiff_singleton_zero` in `Submodule.lean`,
  -- and use `isRemainder_of_insert_zero_iff_isRemainder`.
  sorry

end CommSemiring

section CommRing
open Classical
variable {R : Type*} [CommRing R] {s : σ →₀ ℕ}

noncomputable def sPolynomial (f g : MvPolynomial σ R) : MvPolynomial σ R :=
  monomial (m.degree g - m.degree f) (m.leadingCoeff g) * f -
  monomial (m.degree f - m.degree g) (m.leadingCoeff f) * g

def IsGroebnerBasis (G': Finset (MvPolynomial σ R)) (I : Ideal (MvPolynomial σ R)) :=
  G'.toSet ⊆ I ∧
  Ideal.span (m.leadingTerm '' ↑I)
    = Ideal.span (m.leadingTerm '' G'.toSet)

lemma sPolynomial_antisymm (f g : MvPolynomial σ R) :
   m.sPolynomial f g = - m.sPolynomial g f := by sorry -- easy

lemma sPolynomial_eq_zero_of_left_eq_zero (g : MvPolynomial σ R) :
  m.sPolynomial 0 g = 0 := by sorry -- easy

lemma sPolynomial_eq_zero_of_right_eq_zero' (f : MvPolynomial σ R) :
  m.sPolynomial f 0 = 0 := by sorry -- easy

theorem div_set' {G'' : Set (MvPolynomial σ R)}
    (hG : ∀ g ∈ G'', (IsUnit (m.leadingCoeff g) ∨ g = 0)) (p : MvPolynomial σ R) :
    ∃ (r : MvPolynomial σ R), m.IsRemainder p G'' r := by
  -- easy
  -- tips: use `isRemainder_of_singleton_zero_iff_isRemainder` and `MonomialOrder.div_set`
  sorry

end CommRing

section Field

theorem div_set'' {k : Type*} [Field k] {s : σ →₀ ℕ} {G'' : Set (MvPolynomial σ k)}
    (p : MvPolynomial σ k) :
    ∃ (r : MvPolynomial σ k), m.IsRemainder p G'' r := by
  apply div_set'
  simp [em']


end Field
