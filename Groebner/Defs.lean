import Mathlib
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

-- it may free you from coercion between different kinds of "sets",
-- "finite subsets", "finite subsets" of "sets", ...,
-- when you are dealing with different G''
lemma IsRemainder_def' (p : MvPolynomial σ R) (G'' : Set (MvPolynomial σ R)) (r : MvPolynomial σ R)
  : m.IsRemainder p G'' r ↔ ∃ (g : (MvPolynomial σ R) →₀ (MvPolynomial σ R)),
      ↑g.support ⊆ G'' ∧
      p = Finsupp.linearCombination _ id g + r ∧
      (∀ g' ∈ G'', m.degree ((g' : MvPolynomial σ R) * (g g')) ≼[m] m.degree p) ∧
      (∀ c ∈ r.support, ∀ g' ∈ G'', g' ≠ 0 → ¬ (m.degree g' ≤ c)) := by
  -- probably many tech details
  -- (technologically but not mathematically) normal or hard
  unfold IsRemainder
  constructor
  ·
   rintro ⟨g, h₁, h₂⟩
   sorry
  sorry






lemma IsRemainder_def'' (p : MvPolynomial σ R) (G'' : Set (MvPolynomial σ R)) (r : MvPolynomial σ R)
  : m.IsRemainder p G'' r ↔
  ∃ (g : (MvPolynomial σ R) → (MvPolynomial σ R))(G' : Finset (MvPolynomial σ R)),
      ↑G' ⊆ G'' ∧
      p = G'.sum (fun x => x * g x) + r ∧
      (∀ g' ∈ G', m.degree ((g' : MvPolynomial σ R) * (g g')) ≼[m] m.degree p) ∧
      (∀ c ∈ r.support, ∀ g' ∈ G'', g' ≠ 0 → ¬ (m.degree g' ≤ c)) := by
  -- probably many tech details
  -- (technologically but not mathematically) normal
  rw [IsRemainder_def']
  sorry

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

open Classical

@[simp]
lemma zero_le (a : m.syn) : 0 ≤ a := by
  exact bot_le

  -- sorry

lemma isRemainder_of_insert_zero_iff_isRemainder (p : MvPolynomial σ R)
  (G'' : Set (MvPolynomial σ R)) (r : MvPolynomial σ R) :
  m.IsRemainder p (insert 0 G'') r ↔ m.IsRemainder p G'' r := by
  constructor
  ·
    by_cases hG'' : 0 ∈ G''; simp only [Set.insert_eq_of_mem hG'', imp_self]
    rw [IsRemainder_def'', IsRemainder_def'']
    intro ⟨g, G', hG', h₁, h₂, h₃⟩
    use g, (G'.erase 0)
    split_ands
    · simp [hG']
    ·
      rw [h₁]
      congr 1
      by_cases hG'0 : 0 ∈ G'
      ·
        nth_rw 1 [← Finset.insert_erase hG'0]
        rw [Finset.sum_insert_zero (a:=0)]
        simp
      ·
        rw [Finset.erase_eq_self.mpr hG'0]

    ·
      intro g' hg'
      simp at hg'
      exact h₂ g' hg'.2
    ·
      intro n hn g' hg'G' hg'
      exact h₃ n hn g' (by simp [hg'G']) hg'

    -- -- original partial proof without IsRemainder_def''. i keep it at this time in case i need it again elsewhere.
    -- by_cases hG'' : 0 ∈ G''; simp only [Set.insert_eq_of_mem hG'', imp_self]
    -- rw [IsRemainder_def', IsRemainder_def']
    -- intro ⟨g, hg, h₁, h₂, h₃⟩
    -- by_cases hg' : 0 ∈ g.support
    -- ·
    --   use g.filter (·≠ 0)
    --   -- use f
    --   -- rw [this]

    --   -- have := Finset.sum_insert_zero (a:=0) (s:=f.support) (by simp : (fun (x : MvPolynomial σ R) => (g x • id x)) 0 = 0)

    --   -- rw []
    --   split_ands
    --   ·
    --     simp
    --     intro x
    --     simp
    --     intro hgx hx
    --     apply (Finsupp.mem_support_toFun g x).mpr at hgx
    --     exact (Set.mem_insert_iff.mp (Set.mem_of_mem_of_subset hgx hg)).resolve_left hx
    --   ·
    --     rw [h₁, Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum]
    --     congr 1
    --     have : g.support = insert 0 (g.filter (·≠ 0)).support := by
    --       simp [hg']
    --       apply subset_antisymm
    --       · intro x hx
    --         -- ↓ WHY doesn't it give me a simple `p = 0 ∨ ¬ p = 0` if i don't feed it `or_not` the law of excluded middle????
    --         simp [hx, or_not]
    --       · intro x hx
    --         simp at hx
    --         simp only [Finsupp.mem_support_iff, ne_eq]
    --         cases' hx with hx hx
    --         ·exact hx.symm ▸ Finsupp.mem_support_iff.mp hg'
    --         ·exact hx.1

    --     rw [this]
    --     generalize hgxx : (fun (x : MvPolynomial σ R) => (g x * id x)) = gx_mul_x at *
    --     rw [Finset.sum_insert_zero (a:=0) (s:=(g.filter (·≠ 0)).support) (by simp [←hgxx]: gx_mul_x 0 = 0)]
    --     apply Finset.sum_congr rfl
    --     simp [←hgxx]
    --     intro x _ hx
    --     simp [hx]
    --   ·
    --     intro g'' hg''
    --     simp [(ne_of_mem_of_not_mem hg'' hG'' : g'' ≠ 0)]
    --     exact h₂ g'' (by simp [hg''])
    --   ·
    --     intro n hn g'' hg''G hg''
    --     exact h₃ n hn
    --     sorry
    -- ·
    --   -- rw [IsRemainder_def', IsRemainder_def']
    --   use g
    --   split_ands
    --   · exact (Set.subset_insert_iff_of_not_mem hg').mp hg
    --   · exact h₁
    --   · intro g'' hg''
    --     exact h₂ g'' (by simp[hg''])
    --   · intro n hn g'' hg''G hg''
    --     exact h₃ n hn g'' (by simp [hg''G]) hg''
  ·
    rw [IsRemainder_def', IsRemainder_def']
    intro ⟨g, hg, h₁, h₂, h₃⟩
    use g
    split_ands
    · exact subset_trans hg (Set.subset_insert _ _)
    · exact h₁
    · intro g' hg'
      by_cases hg'₁ : g' = 0
      · simp only [hg'₁, zero_mul, degree_zero, map_zero, zero_le]
      · exact h₂ g' ((Set.mem_insert_iff.mp hg').resolve_left hg'₁)
    ·
      intro c hc g' hg' hg'₁
      exact h₃ c hc g' ((Set.mem_insert_iff.mp hg').resolve_left hg'₁) hg'₁

lemma isRemainder_of_singleton_zero_iff_isRemainder (p : MvPolynomial σ R)
  (G'' : Set (MvPolynomial σ R)) (r : MvPolynomial σ R) :
  m.IsRemainder p (G'' \ {0}) r ↔ m.IsRemainder p G'' r := by
  -- tips: refer to the proof of `Submodule.span_sdiff_singleton_zero` in `Submodule.lean`,
  -- and use `isRemainder_of_insert_zero_iff_isRemainder`.
  by_cases h : 0 ∈ G''
  · rw[←isRemainder_of_insert_zero_iff_isRemainder,
        (by simp [h] : insert 0 (G'' \ {0}) = G'')]
  · have h' : G'' \ {0} = G'' := by
      ext x
      simp [h]
    rw [h']

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
   m.sPolynomial f g = - m.sPolynomial g f := by
   unfold sPolynomial
   exact
     Eq.symm
       (neg_sub ((monomial (m.degree f - m.degree g)) (m.leadingCoeff f) * g)
         ((monomial (m.degree g - m.degree f)) (m.leadingCoeff g) * f))


lemma sPolynomial_eq_zero_of_left_eq_zero (g : MvPolynomial σ R) :
  m.sPolynomial 0 g = 0 := by
  unfold sPolynomial
  simp only [zero_mul, sub_zero, leadingCoeff_zero, monomial_zero]
  exact CommMonoidWithZero.mul_zero ((monomial (m.degree g - m.degree 0)) (m.leadingCoeff g))

lemma sPolynomial_eq_zero_of_right_eq_zero' (f : MvPolynomial σ R) :
  m.sPolynomial f 0 = 0 := by
  rw [sPolynomial_antisymm, sPolynomial_eq_zero_of_left_eq_zero, neg_zero]

theorem div_set' {G'' : Set (MvPolynomial σ R)}
    (hG : ∀ g ∈ G'', (IsUnit (m.leadingCoeff g) ∨ g = 0)) (p : MvPolynomial σ R) :
    ∃ (r : MvPolynomial σ R), m.IsRemainder p G'' r := by
  -- tips: use `isRemainder_of_singleton_zero_iff_isRemainder` and `MonomialOrder.div_set`
  let G := G'' \ {0}

  have hG' : ∀ g ∈ G, IsUnit (m.leadingCoeff g) := by
    intro g hg
    obtain ⟨hg₁, hg₂⟩ := hg  -- hg₁: g ∈ G'', hg₂: g ≠ 0
    obtain (h1 | h2) := hG g hg₁
    · exact h1
    · contradiction
  obtain ⟨g, r, h⟩ := MonomialOrder.div_set hG' p
  exists r
  refine (isRemainder_of_singleton_zero_iff_isRemainder m p G'' r).mp ?_
  rcases h with ⟨h₁, h₂, h₃⟩
  simp at *
  unfold IsRemainder
  use g
  split_ands
  · exact h₁
  · exact fun g' ↦ h₂ (↑g') g'.property
  · intro c hc g hg g_neq0
    have hg' : g ∈ G := by
      obtain ⟨hg₁, hg₂⟩ := hg
      exact ⟨hg₁, hg₂⟩
    have hc': ¬coeff c r = 0 := by
      exact mem_support_iff.mp hc
    have h₃_applied := h₃ c hc'
    have h₃_g := h₃_applied g hg'
    exact h₃_g
end CommRing

section Field

theorem div_set'' {k : Type*} [Field k] {s : σ →₀ ℕ} {G'' : Set (MvPolynomial σ k)}
    (p : MvPolynomial σ k) :
    ∃ (r : MvPolynomial σ k), m.IsRemainder p G'' r := by
  apply div_set'
  simp [em']


end Field
