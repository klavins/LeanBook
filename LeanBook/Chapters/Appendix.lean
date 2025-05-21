import Mathlib

universe u v

/- # Useful Theorems -/

theorem not_empty_to_exists {A : Type u} {S : Set A} : S ≠ ∅ → ∃ x, x ∈ S := by
   intro h
   by_contra h'
   simp at h'
   exact h (Set.eq_empty_iff_forall_not_mem.mpr h')

theorem not_empty_set_diff {A : Type u} {X Y : Set A} (h : ¬X ⊆ Y)
  : X \ Y ≠ ∅ := by
  simp[Set.instSDiff,Set.diff]
  by_contra hx
  simp at hx
  exact h hx
