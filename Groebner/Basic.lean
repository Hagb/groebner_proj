import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

namespace MvPolynomial

open Ideal
open MonomialOrder
open scoped MonomialOrder

variable {σ : Type*} {m : MonomialOrder σ} {k : Type*} [Field k]
variable (I : Ideal (MvPolynomial σ k)) (G' : Finset (MvPolynomial σ k))

/-

-/

/-
Let G‘⊆k[x_i, i∈σ] be a finite set and I be a polynomial ideal. If the finite set G’⊆I and ⟨lt(G)⟩=⟨lt(I)⟩, then G is called a Gröbner basis of I
-/
def IsGroebnerBasis' : Prop :=
  (↑G' ⊆ I) ∧

end MvPolynomial
