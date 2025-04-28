-- import Mathlib -- TODO: should be removed later
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

variable {R : Type*} [Semiring R]

theorem mem_span_iff (A : Set R) (p : R) :
p ∈ Ideal.span A ↔ ∃ (s : Finset A)(f : R → R), p = ∑ m in s, f m * m
:=by
  sorry
theorem mem_span_iff' (A : Set R) (p : R) :
p ∈ Ideal.span A ↔ ∃ (s : Finset A)(f : A → R), p = ∑ m in s, f m * m
:= by
  sorry
theorem mem_span_iff'' (A : Set R) (p : R) :
p ∈ Ideal.span A ↔
∃ (s : Finset R) (f : R → R), s.toSet ⊆ A ∧ p = ∑ m in s, f m * m
:= by
  sorry

/--
A subset $s \subseteq R$ has finitely generated span if and only if:
$\exists$ finite $s' \subseteq s$ such that $\mathsf{span}(s) = \mathsf{span}(s')$
-/
theorem fg_span_iff_fg_span_finset_subset (s : Set R) :
  (span s).FG ↔ ∃ (s' : Finset R), s'.toSet ⊆ s ∧ span s = span s' := by
  constructor
  ·
    intro h
    rcases h with ⟨t, ht⟩
    have : ∀ x ∈ t, x ∈ span s := by
      sorry
    sorry
  ·
    rintro ⟨s', hsub, heq⟩
    exact ⟨s', heq.symm⟩

-- to Mathlib

/--
For any ring $R$, the span of the zero singleton set equals the zero submodule:
  $$
    \mathsf{span}_R \{(0 : R)\} = \bot
  $$
-/
@[simp]
lemma span_singleton_zero : span {(0 : R)} = ⊥ :=
  Submodule.span_zero_singleton _

-- to Mathlib

/--
For any subset $s \subseteq R$ of a ring $R$, inserting zero does not change the linear span:
  $$
    \mathsf{span}_R(\{0\} \cup s) = \mathsf{span}_R(s)
  $$
-/
@[simp]
lemma span_insert_zero (s : Set R): span (insert 0 s) = span s :=
  Submodule.span_insert_zero

-- to Mathlib

/--
For any subset $s \subseteq R$ of a ring $R$, removing zero does not change the linear span:
  $$
    \mathsf{span}_R(s \setminus \{0\}) = \mathsf{span}_R(s)
  $$
-/
@[simp]
lemma span_sdiff_singleton_zero (s : Set R): span (s \ {0}) = span s := Submodule.span_sdiff_singleton_zero _ _

end Ideal

namespace MonomialOrder
open Ideal
open MvPolynomial
open Classical

variable {σ : Type*} {m : MonomialOrder σ} {s : σ →₀ ℕ}
variable {k : Type*} [Field k] variable (p p₁ p₂ : MvPolynomial σ k)
variable (G': Finset (MvPolynomial σ k)) (G'': Set (MvPolynomial σ k))
variable (I I₁ I₂ : Ideal (MvPolynomial σ k))
variable {R : Type*} [CommSemiring R]

open Finsupp
open Finset
open Submodule
open Ideal
open Field

/--
Let $G'' \subseteq R[x_1, \dots, x_n]$ be a set of polynomials such that
$$
\forall p \in G'',\ \operatorname{leadingCoeff}(p) \in R^\times.
$$
Then,
$$
\left\langle \operatorname{lt}(G'') \right\rangle = \left\langle x^{\deg(p)} \mid p \in G'' \right\rangle,
$$
-/
lemma leadingTerm_ideal_span_monomial {G'': Set (MvPolynomial σ R)}
  (hG'' : ∀ p ∈ G'', IsUnit (m.leadingCoeff p)) :
  span (m.leadingTerm '' G'') = span ((fun p => MvPolynomial.monomial (m.degree p) (1 : R)) '' G'') := by
  apply le_antisymm
  <;> rintro p hl
  <;> simp only [MonomialOrder.leadingTerm, ← submodule_span_eq, mem_span_image_iff_exists_fun] at *
  <;> rcases hl with ⟨t, ht, c, hc⟩
  <;> rw [←hc]
  <;> use t
  · split_ands
    · exact ht
    ·
      use fun (p : _) => (MvPolynomial.C (m.leadingCoeff ↑p : R) : MvPolynomial σ R) • c ↑p
      -- simp?
      apply Finset.sum_congr rfl
      simp
      intro a ha
      rw [mul_assoc, mul_left_comm, MvPolynomial.C_mul_monomial, mul_one]
  · split_ands
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

/--
$$
\langle \mathrm{lt}(G) \rangle = \left\langle \left\{ x^t : t \in \{ \mathrm{multideg}(p) : p \in G \setminus \{0\} \} \right\} \right\rangle
$$
-/
lemma leadingTerm_ideal_span_monomial' : span (m.leadingTerm '' G'') =
  span ((fun p => MvPolynomial.monomial (m.degree p) (1 : k)) '' (G'' \ {(0 : MvPolynomial σ k)})) := by
  calc
    _ = span (m.leadingTerm '' G'' \ {0}) := (Ideal.span_sdiff_singleton_zero _).symm
    _ = span (m.leadingTerm '' (G'' \ {0})) := by rw [m.leadingTerm_image_sdiff_singleton_zero]
    _ = _ := by
      apply leadingTerm_ideal_span_monomial
      simp

/--
Let $G'' \subseteq R[x_1, \dots, x_n]$, let $I \subseteq R[x_1, \dots, x_n]$ be an ideal,
and let $p, r \in R[x_1, \dots, x_n]$. Suppose that:

  - $G'' \subseteq I$,
  - $r \in I$,
  - $r$ is the remainder of $p$ upon division by $G''$.

Then,
$$
p \in I.
$$
-/
lemma mem_ideal_of_remainder_mem_ideal {G'': Set (MvPolynomial σ R)} {r : MvPolynomial σ R}
  {I : Ideal (MvPolynomial σ R)} {p : MvPolynomial σ R}
  (hG''I : G'' ⊆ I) (hpG''r : m.IsRemainder p G'' r) (hr : r ∈ I) :
  p ∈ I := by
  obtain ⟨⟨f, h_eq, h_deg⟩, h_remain⟩ := hpG''r
  rw[h_eq]
  refine Ideal.add_mem _ ?_ ?_
  ·
    rw [Finsupp.linearCombination_apply]
    apply Ideal.sum_mem
    intro g hg
    exact mul_mem_left _ _ (Set.mem_of_mem_of_subset (by simp) hG''I)
  · exact hr

/--
Let $R$ be a commutative ring, and let $G'' \subseteq R[x_1, \dots, x_n]$, $I \subseteq R[x_1, \dots, x_n]$ be an ideal, and $p, r \in R[x_1, \dots, x_n]$.
Assume that:

  - $G'' \subseteq I$,
  - $r$ is the remainder of $p$ upon division by $G''$.

Then,
$$
r \in I \quad \Longleftrightarrow \quad p \in I.
$$
-/
lemma remainder_mem_ideal_iff {R : Type*} [CommRing R] {G'': Set (MvPolynomial σ R)}
  {r : MvPolynomial σ R} {I : Ideal (MvPolynomial σ R)} {p : MvPolynomial σ R}
  (hG''I : G'' ⊆ I) (hpG''r : m.IsRemainder p G'' r) :
  r ∈ I ↔ p ∈ I := by
  refine ⟨mem_ideal_of_remainder_mem_ideal hG''I hpG''r, ?_⟩
  obtain ⟨⟨f, h_eq, h_deg⟩, h_remain⟩ := hpG''r
  intro hp
  rw [← sub_eq_of_eq_add' h_eq]
  apply Ideal.sub_mem I hp
  -- (optional) to make it clearer: `rw [Finsupp.linearCombination_apply]`
  apply Ideal.sum_mem
  intro g hg
  exact mul_mem_left I _ (Set.mem_of_mem_of_subset (by simp) hG''I)

/--
Let $I \subseteq k[x_i : i \in \sigma]$ be an ideal, and let $G \subseteq I$ be a finite subset.
Suppose that $r_1$ and $r_2$ are generalized remainders of a polynomial $p$ upon division by $G$.
Then,
$$
r_1 - r_2 \in I.
$$
-/
lemma remainder_sub_remainder_mem_ideal {R : Type*} [CommRing R]
  {G'': Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)} {p r₁ r₂ : MvPolynomial σ R}
  (hG''I : G'' ⊆ I) (hr₁ : m.IsRemainder p G'' r₁) (hr₂ : m.IsRemainder p G'' r₂) :
  r₁-r₂ ∈ I := by
  obtain ⟨⟨f₁, h_eq₁, h_deg₁⟩, h_remain₁⟩ := hr₁
  obtain ⟨⟨f₂, h_eq₂, h_deg₂⟩, h_remain₂⟩ := hr₂
  rw [← sub_eq_of_eq_add' h_eq₁, ← sub_eq_of_eq_add' h_eq₂]
  simp
  apply Ideal.sub_mem I
  <;> apply Ideal.sum_mem
  <;> intro g hg
  <;> exact mul_mem_left I _ (Set.mem_of_mem_of_subset (by simp) hG''I)

-- lemma monomial_not_mem_leading_term_ideal{r : MvPolynomial σ k}
--   {G' : Set (MvPolynomial σ k)}
--   (h : ∀ g ∈ G', g ≠ 0 → ∀ s ∈ r.support, ¬ m.degree g ≤ s) :
--   ∀ s ∈ r.support, monomial s (1 : k) ∉ leading_term_ideal m G' := by
--   sorry

-- lemma term_not_mem_leading_term_ideal {r : MvPolynomial σ k}
-- {G' : Set (MvPolynomial σ k)}
-- (h : ∀ g ∈ G', g ≠ 0 → ∀ s ∈ r.support, ¬ m.degree g ≤ s)
-- : ∀ s ∈ r.support, monomial s (r.coeff s) ∉ leading_term_ideal m  G' := by
--   sorry

-- lemma not_mem_leading_term_ideal {r : MvPolynomial σ k}
-- {G' : Set (MvPolynomial σ k)}
-- (h : ∀ g ∈ G', g ≠ 0 → ∀ s ∈ r.support, ¬ m.degree g ≤ s)
-- (hr : r ≠ 0) :
-- r ∉ leading_term_ideal m G' := by
--  sorry

lemma IsRemainder_monomial_not_mem_leading_term_ideal {p r : MvPolynomial σ R}
  {G'' : Set (MvPolynomial σ R)}
  (hG'' : ∀ p ∈ G'', IsUnit (m.leadingCoeff p))
  (h : m.IsRemainder p G'' r):
∀ s ∈ r.support, monomial s 1 ∉ Ideal.span (m.leadingTerm '' G'') := by
  intro s hs
  rw [leadingTerm_ideal_span_monomial hG'', ← Set.image_image (monomial · 1) _ _, mem_ideal_span_monomial_image]
  have h1ne0: (1 : R) ≠ 0 := by
    by_contra h1eq0
    rw [MvPolynomial.mem_support_iff, ← mul_one <| r.coeff s, h1eq0, mul_zero] at hs
    exact hs rfl
  simp [h1ne0]
  intro q hq
  unfold MonomialOrder.IsRemainder at h
  apply h.2 s hs q hq
  by_contra hq0
  specialize hG'' q hq
  simp [hq0, h1ne0.symm] at hG''

lemma IsRemainder_monomial_not_mem_leading_term_ideal' {p r : MvPolynomial σ k}
  {G'' : Set (MvPolynomial σ k)} (h : m.IsRemainder p G'' r):
∀ s ∈ r.support, monomial s 1 ∉ Ideal.span (m.leadingTerm '' G'') := by
  rw [←Ideal.span_sdiff_singleton_zero, ← m.leadingTerm_image_sdiff_singleton_zero]
  apply IsRemainder_monomial_not_mem_leading_term_ideal
  simp
  rwa [←isRemainder_of_singleton_zero_iff_isRemainder] at h

-- lemma rem_monomial_not_mem_leading_term_ideal {p r : MvPolynomial σ k}
-- {G' : Finset (MvPolynomial σ k)} (h : IsRemainder p G' r):
-- ∀ s ∈ r.support, monomial s 1 ∉ leading_term_ideal G'.toSet := by
--   sorry

-- lemma rem_term_not_mem_leading_term_ideal {p r : MvPolynomial σ k}
-- {G' : Finset (MvPolynomial σ k)} (h : is_rem p G' r):
-- ∀ s ∈ r.support, monomial s (r.coeff s) ∉ leading_term_ideal G' := by

-- lemma rem_not_mem_leading_term_ideal {p r : MvPolynomial σ k}
-- {G' : Finset (MvPolynomial σ k)} (h : is_rem p G' r) (hr :r ≠ 0):
-- r ∉ leading_term_ideal G' := by

-- lemma rem_sub_rem_term_not_mem_leading_term_ideal
-- {G' : Finset (MvPolynomial σ k)} {p r₁ r₂ : MvPolynomial σ k}
-- (hr₁ : m.IsRemainder p G' r₁) (hr₂ :  m.IsRemainder p G' r₂) :
-- ∀ s ∈ (r₁-r₂).support, monomial s ((r₁-r₂).coeff s) ∉ leading_term_ideal G'
-- := by

end MonomialOrder
