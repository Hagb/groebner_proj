import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic

namespace Set

lemma finset_subset_preimage_of_finite_image {α : Type _} {β : Type _}
    {s : Set α} {f : α → β} (h : (f '' s).Finite) :
    ∃ (s' : Finset α), s'.toSet ⊆ s ∧ f '' s' = f '' s ∧ s'.card = h.toFinset.card := by
  have := s.mem_image f
  rw [←h.coe_toFinset] at this
  by_cases h' : s = ∅
  · use ∅; simp [h']
  ·
    classical
    cases' Set.nonempty_iff_ne_empty.mpr h' with a ha
    let s' := h.toFinset.image fun (x : β) =>
      if hx : x ∈ h.toFinset
        then ((this x).mp (hx)).choose
        else a
    have hs' : s'.toSet ⊆ s := by
      intro x hx
      simp [s'] at hx
      let ⟨y, hy, hy'⟩ := hx
      rw [←hy']
      have hxy: ∃ x ∈ s, f x = f y := by use y, hy
      simp [hxy, hxy.choose_spec]
    use s'
    constructor
    ·exact hs'
    constructor
    ·
      apply Set.eq_of_subset_of_subset
      ·exact Set.image_subset _ hs'
      ·
        intro y hy
        simp at hy
        let ⟨x,hx, hxy⟩ := hy
        simp [s']
        use x
        simp [hx, hxy, hy, hy.choose_spec]
    ·
      simp_rw [s', Finset.card_image_iff, Set.InjOn]
      intro x₁ hx₁ x₂ hx₂
      simp at hx₁ hx₂
      simp [hx₁, hx₂]
      intro hx₁x₂
      rw [←hx₂.choose_spec.2, ←hx₁.choose_spec.2, hx₁x₂]
