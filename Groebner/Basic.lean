import Mathlib
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Basic

namespace MonomialOrder

open MvPolynomial

open scoped MonomialOrder

variable {σ : Type*} {m : MonomialOrder σ}

section Semiring

variable {R : Type*} [CommSemiring R]

variable (m) in
noncomputable def leadingTerm (f : MvPolynomial σ R) : MvPolynomial σ R :=
  monomial (m.degree f) (m.leadingCoeff f)

end Semiring

end MonomialOrder


open MvPolynomial

variable {σ : Type _} {m : MonomialOrder σ} {s : σ →₀ ℕ} {k : Type _} [Field k]
variable (p : MvPolynomial σ k)
variable (G': Finset (MvPolynomial σ k)) (I : Ideal (MvPolynomial σ k))


def is_groebner_basis :=
  G'.toSet ⊆ I ∧
  Ideal.span (m.leadingTerm '' I)
    = Ideal.span (m.leadingTerm '' G'.toSet)
