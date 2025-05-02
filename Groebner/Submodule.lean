import Mathlib.LinearAlgebra.Span.Basic

namespace Submodule
open Set

variable (R : Type*) {M : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M]
variable (s : Set M)


-- to Mathlib
/--
  $$
    \langle G \rangle = \langle G \setminus \{0\} \rangle
  $$
-/
@[simp]
lemma span_sdiff_singleton_zero._mathlib:
  span R (s \ {0}) = span R s := by
  by_cases h : 0 ∈ s
  ·rw [←span_insert_zero, (by simp [h] : insert 0 (s \ {0}) = s)]
  ·simp [h]

end Submodule
