import Mathlib-- should be removed later
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Finiteness.Basic
import Groebner.Set
import Groebner.Ideal
import Groebner.Defs

namespace MonomialOrder
open MvPolynomial
section Field

set_option linter.unusedTactic false

variable {σ : Type*} {m : MonomialOrder σ}
variable {s : σ →₀ ℕ} {k : Type*} [Field k] {R : Type*} [CommRing R]
variable (p : MvPolynomial σ k)
variable (G': Finset (MvPolynomial σ k)) (I : Ideal (MvPolynomial σ k))

/--
Let $I \subseteq k[x_1, \ldots, x_n]$ be an ideal. Then there exists a finite subset $G = \{g_1, \ldots, g_t\}$ of $I$ such that $G$ is a Gröbner basis for $I$.
-/
theorem exists_groebner_basis [Finite σ] :
  ∃ G' : Finset (MvPolynomial σ k), IsGroebnerBasis m G' ↑I := by
  have key : (Ideal.span (α:=MvPolynomial σ k) (m.leadingTerm '' ↑I)).FG :=
    (inferInstance : IsNoetherian _ _).noetherian _
  simp only [Ideal.fg_span_iff_fg_span_finset_subset, Set.subset_image_iff] at key
  rcases key with ⟨s, ⟨G,hGI, hGs⟩, hIs⟩
  obtain ⟨G', hG', hG'G, _⟩ := Set.finset_subset_preimage_of_finite_image (hGs.symm ▸ Finset.finite_toSet s)
  use G'
  constructor
  · exact hG'.trans hGI
  · rw [hIs, hG'G, hGs]



/--
Let $G = \{g_1, \dots, g_t\}$ be a Gröbner basis for an ideal $I \subseteq k[x_1, \dots, x_n]$ and let $f \in k[x_1, \dots, x_n]$. Then $f \in I$ if and only if the remainder on division of $f$ by $G$ is zero.
-/
theorem groebner_basis_isRemainder_zero_iff_mem_span {p : MvPolynomial σ R}
  {G' : Finset (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}
  {r : MvPolynomial σ R}
  (hG' : ∀ g ∈ G', IsUnit (m.leadingCoeff g))
  (h : m.IsGroebnerBasis G' I)
  (hr : m.IsRemainder p G' r)
  : r = 0 ↔ p ∈ I := by
  constructor
  · intro h_zero
    rw[h_zero] at hr
    obtain ⟨⟨g, h_p, -⟩, -⟩ := hr
    rw [h_p]
    unfold MonomialOrder.IsGroebnerBasis at h
    have h₁: (Finsupp.linearCombination (MvPolynomial σ R) fun g' ↦ ↑g') g ∈ I := by
      rw [Finsupp.linearCombination_apply]
      rw[Finsupp.sum]
      apply Ideal.sum_mem I
      intro a h_a_in_support
      rcases h with ⟨h_G', h_span⟩
      have h₂: ↑a ∈ G' := by
        exact Finset.coe_mem a
      exact Submodule.smul_mem I (g a) (h_G' h₂)
    have h₂: 0 ∈ I := by
      exact Submodule.zero_mem I
    exact (Submodule.add_mem_iff_right I h₁).mpr h₂
  · intro h_p_mem
    by_contra hr_ne_zero
    have h₃: m.leadingTerm r ∉ Ideal.span (m.leadingTerm '' ↑G') := by
      nth_rewrite 1 [leadingTerm]
      apply IsRemainder_term_not_mem_leading_term_ideal hG' hr
      exact (m.degree_mem_support_iff r).mpr hr_ne_zero
    rcases h with ⟨h_G', h_span⟩
    obtain ⟨⟨q, h_p_eq_sum_r, h_r_reduced⟩, h_degree⟩ := hr
    have h₁: (Finsupp.linearCombination (MvPolynomial σ R) fun g' ↦ ↑g') q ∈ I := by
      rw [Finsupp.linearCombination_apply]
      rw[Finsupp.sum]
      apply Ideal.sum_mem I
      intro a h_a_in_support
      have h₂: ↑a ∈ G' := by
        exact Finset.coe_mem a
      exact Submodule.smul_mem I (q a) (h_G' h₂)
    rw[h_p_eq_sum_r] at h_p_mem
    have h₂: r ∈ I := by
      exact (Submodule.add_mem_iff_right I h₁).mp h_p_mem
    have h₄: m.leadingTerm r ∈ Ideal.span (m.leadingTerm '' ↑G') := by
      rw[←h_span]
      apply Ideal.subset_span
      apply Set.mem_image_of_mem
      exact h₂
    exact h₃ h₄

theorem groebner_basis_isRemainder_zero_iff_mem_span' {p : MvPolynomial σ k}
  {G' : Finset (MvPolynomial σ k)} {I : Ideal (MvPolynomial σ k)}
  {r : MvPolynomial σ k}
  (hG' : ∀ g ∈ G', IsUnit (m.leadingCoeff g))
  (h : m.IsGroebnerBasis G' I)
  (hr : m.IsRemainder p G' r)
  : r = 0 ↔ p ∈ I := by
  rw [← m.IsGroebnerBasis_erase_zero] at h
  have _uses := @IsGroebnerBasis_erase_zero.{0,0,0}
  have _uses := @isRemainder_sdiff_singleton_zero_iff_isRemainder.{0,0,0}
  apply groebner_basis_isRemainder_zero_iff_mem_span
  · exact hG'
  · exact (IsGroebnerBasis_erase_zero G' I).mp h
  · exact hr



theorem groebner_basis_zero_isRemainder_iff_mem_span {p : MvPolynomial σ R}
  {G' : Finset (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}
  {r : MvPolynomial σ R}
  (hG' : ∀ g ∈ G', IsUnit (m.leadingCoeff g))
  (h : m.IsGroebnerBasis G' I)
  : m.IsRemainder p G' 0 ↔ p ∈ I := by
  have _uses := @groebner_basis_isRemainder_zero_iff_mem_span.{0,0,0}
  have _uses := @div_set'.{0,0,0}
  sorry

lemma groebner_basis_zero_isRemainder_iff_mem_span' {p : MvPolynomial σ k}
  {G' : Finset (MvPolynomial σ k)} {I : Ideal (MvPolynomial σ k)}
  {r : MvPolynomial σ k}
  (h : m.IsGroebnerBasis G' I) :
  p ∈ I ↔ m.IsRemainder p G' 0 := by
  have _uses := @groebner_basis_isRemainder_zero_iff_mem_span.{0,0,0}
  have _uses := @IsGroebnerBasis_erase_zero.{0,0,0}
  have _uses := @isRemainder_sdiff_singleton_zero_iff_isRemainder.{0,0,0}
  sorry



/--
Let $G = \{g_1, \ldots, g_t\}$ be a finite subset of $k[x_1, \ldots, x_n]$. Then $G$ is a Gröbner basis for the ideal $I = \langle G \rangle$ if and only if  for every $f \in I$, the remainder of $f$ on division by $G$ is zero.
-/
theorem IsGroebnerBasis_iff :
  m.IsGroebnerBasis G' I ↔ G'.toSet ⊆ I ∧ ∀ p ∈ I, m.IsRemainder p G' 0 := by
  -- uses groebner_basis_zero_isRemainder_iff_mem_span'
  have _uses := @groebner_basis_zero_isRemainder_iff_mem_span'.{0,0,0}
  constructor
  · intro h
    constructor
    · unfold MonomialOrder.IsGroebnerBasis at h
      rcases h with ⟨h_G', h_span⟩
      exact h_G'
    · intro p h_p_in_I
      rw[←groebner_basis_zero_isRemainder_iff_mem_span']
      norm_cast
      exact h
      exact p
  · intro h
    rcases h with ⟨h_G', h_remainder⟩
    unfold MonomialOrder.IsGroebnerBasis
    constructor
    · exact h_G'
    · apply le_antisymm
      · intro p h_p_in_I
        sorry
      · intro p h_p_in_I




    -- · have h₁: Ideal.span (m.leadingTerm '' ↑I) ≤ Ideal.span (m.leadingTerm '' (↑G':Set (MvPolynomial σ k))) := by
    --     sorry
    --   have h₂: Ideal.span (m.leadingTerm '' (↑G':Set (MvPolynomial σ k))) ≤ Ideal.span (m.leadingTerm '' ↑I)  := by
    --     sorry



-- theorem IsGroebnerBasis_iff' :
--   m.IsGroebnerBasis G' I ↔
--   G'.toSet ⊆ I ∧ ∀ p ∈ I, ∀ r, m.IsRemainder p G' r → r = 0 := by
--   sorry

/--
Let $G = \{g_1, \ldots, g_t\}$ be a Gröbner basis for an ideal $I \subseteq k[x_1, \ldots, x_n]$. Then $G$ is a basis for the vector space $I$ over $k$.
-/
theorem span_groebner_basis (h : m.IsGroebnerBasis G' I) : I = Ideal.span G' := by
  -- uses IsGroebnerBasis_iff
  have _uses := @IsGroebnerBasis_iff.{0,0,0}
  sorry

/--
A basis $G = \{ g_1, \ldots, g_t \}$ for an ideal $I$ is a Gröbner basis if and only if $S(g_i, g_j) \to_G 0$ for all $i \neq j$.
-/
theorem buchberger_criterion {g₁ g₂ : MvPolynomial σ k}
  (hG: ∀ (g₁ g₂: G'), m.IsRemainder (m.sPolynomial g₁ g₂ : MvPolynomial σ k) G' 0) :
  m.IsGroebnerBasis G' (Ideal.span G') := by
  have _uses := @groebner_basis_isRemainder_zero_iff_mem_span.{0,0,0}
  have _uses := @IsGroebnerBasis_iff.{0,0,0}
  sorry
