import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.Ideal.Span


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
def IsGroebnerBasis : Prop :=
  G'.toSet ⊆ I ∧
  Ideal.span (m.leadingTerm '' ↑I)
    = Ideal.span (m.leadingTerm '' G'.toSet)

variable (m) in
def IsReminder (G' : Finset (MvPolynomial σ k)) (r : MvPolynomial σ k) : Prop :=
  ∃ (g : G' →₀ (MvPolynomial σ k)),
     p = Finsupp.linearCombination _ (fun (g' : G') ↦ (g' : MvPolynomial σ k)) g + r ∧
     (∀ (g' : G'), m.degree ((g' : MvPolynomial σ k) * (g g')) ≼[m] m.degree p) ∧
     (∀ c ∈ r.support, ∀ g' ∈ G', ¬ (m.degree g' ≤ c))
