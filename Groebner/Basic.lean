import Mathlib -- should be removed later
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Finiteness.Basic
import Groebner.Set
import Groebner.Ideal

namespace MonomialOrder

open MvPolynomial
variable {σ : Type*} {m : MonomialOrder σ}

section Semiring
variable {R : Type*} [CommSemiring R]

variable (m) in
noncomputable def leadingTerm (f : MvPolynomial σ R) : MvPolynomial σ R :=
  monomial (m.degree f) (m.leadingCoeff f)
end Semiring


section Field

variable {s : σ →₀ ℕ} {k : Type _} [Field k]
variable (p : MvPolynomial σ k)
variable (G': Finset (MvPolynomial σ k)) (I : Ideal (MvPolynomial σ k))

variable (m) in
def is_groebner_basis : Prop :=
  G'.toSet ⊆ I ∧
  Ideal.span (m.leadingTerm '' ↑I)
    = Ideal.span (m.leadingTerm '' G'.toSet)

set_option diagnostics true
theorem exists_groebner_basis [Finite σ]:
  ∃ G' : Finset (MvPolynomial σ k), is_groebner_basis m G' ↑I := by
  have key : (Ideal.span (α:=MvPolynomial σ k) (m.leadingTerm '' ↑I)).FG :=
    (inferInstance : IsNoetherian _ _).noetherian _
  simp only [Ideal.fg_span_iff_fg_span_finset_subset, Set.subset_image_iff] at key
  rcases key with ⟨s, ⟨G,hGI, hGs⟩, hIs⟩
  obtain ⟨G', hG', hG'G, _⟩ := Set.finset_subset_preimage_of_finite_image (hGs.symm ▸ Finset.finite_toSet s)
  use G'
  constructor
  · exact hG'.trans hGI
  · rw [hIs, hG'G, hGs]

theorem groebner_basis_rem_eq_zero_iff {p : MvPolynomial σ k}
  {G' : Finset (MvPolynomial σ k)} {I : Ideal (MvPolynomial σ k)}
  {r : MvPolynomial σ k}
  (h : is_groebner_basis m G' I)
  (hr: ∃ (g : G' →₀ (MvPolynomial σ k)),
     p = Finsupp.linearCombination _ (fun (g' : G') ↦ (g' : MvPolynomial σ k)) g + r ∧
     (∀ (g' : G'), m.degree ((g' : MvPolynomial σ k) * (g g')) ≼[m] m.degree p) ∧
     (∀ c ∈ r.support, ∀ g' ∈ G', ¬ (m.degree g' ≤ c))
  )
  : r = 0 ↔ p ∈ I := by sorry
