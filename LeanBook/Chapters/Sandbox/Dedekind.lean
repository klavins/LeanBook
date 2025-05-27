
import Mathlib
import LeanBook.Chapters.Ordering.Completions
import LeanBook.Chapters.Ordering.Reals
import LeanBook.Chapters.Appendix

universe u v

namespace LeanBook.Ordering
open LeanBook.Ordering

/-

  A Dedekind cut is a pair (A,B) where A is downward closed and complete.

  Given an element X of DM ℚ we have two cases:

  - X contains its max x. Then we take A = X \ {x}
  - X doesn't contain its max. Then we take A = X

  The issue is that for an arbitary X, there s no obvious way to determine which
  of these two cases holds.

-/
def finite (A : Set ℚ) := A ≠ ∅ ∧ A ≠ Set.univ

def slower {P : Type u} [Poset P] (A : Set P) : Set P :=
 { x | ∀ a ∈ A, x < a }

theorem lt_simp (x y : ℚ) : x < y ↔ lt_inst.lt x y := by
  simp[lt_inst,Poset.le]
  exact lt_iff_le_and_ne

@[ext]
structure DCut where
  A : Set ℚ
  non_empty : ∃ q, q ∈ A
  non_full : ∃ q, q ∉ A
  down_closed : ∀ x y, x ≤ y ∧ y ∈ A → x ∈ A
  nice_and_open : ∀ x ∈ A, ∃ y ∈ A, x < y

theorem is_slower_alt {A : Set ℚ} {x : ℚ} (hx : x ∈ slower (upper A))
  : x-1 ∈ slower (upper A) := by
  simp[slower] at hx ⊢
  intro a ha
  simp[upper] at ha
  have := hx a ha
  rw[←lt_simp] at this ⊢
  linarith

theorem slower_lower {A : Set ℚ} : slower (upper A) ⊆ lower (upper A) := by
  intro x hx
  simp[slower] at hx
  intro a ha
  have := hx a ha
  simp[le_inst,lt_inst,Poset.le] at this ⊢
  linarith


theorem lower_partition {A : Set ℚ} {x : ℚ} (hx : x ∈ lower (upper A))
  : (∀ y ∈ lower (upper A), y ≤ x) → lower (upper A) = slower (upper A) ∪ {x} := by
  intro h
  ext q
  constructor

  . intro hq
    by_cases hqx : q = x
    . rw[lower] at hq
      rw[slower]
      simp[lt_simp]
      exact Or.inl hqx
    . simp
      apply Or.inr
      have hq' := h q hq
      rw[lower] at hq
      rw[slower]
      simp at hq ⊢
      intro a ha
      have h1 := hq a ha
      have hqx : q < x := by exact lt_of_le_of_ne (h q hq) hqx
      have hxa : x ≤ a := by exact hx a ha
      simp[lt_inst,le_inst,Poset.le]
      exact ⟨ h1, by linarith ⟩

  . intro hq
    simp at hq ⊢
    apply Or.elim hq
    . intro hl
      rw[hl]
      exact hx
    . intro hr
      rw[slower] at hr
      rw[lower]
      simp
      intro a ha
      have h1 := hr a ha
      simp[lt_inst,le_inst,Poset.le] at h1 ⊢
      exact h1.left

-- theorem lu_same {A : Set ℚ} {x : ℚ}
--   : x ∈ lower (upper A) → x ∈ upper A → ∀ y ∈ lower (upper A), y ≤ x := by
--   intro hxlu hxu y hy
--   sorry

theorem thing {A : Set ℚ} {a y : ℚ}
  : y ∈ upper A → y ≤ a → a ∈ upper A :=  by
  intro hy hya
  intro x hx
  have := hy x hx
  linarith


theorem slu_open {A : Set ℚ} {hA : A = lower (upper A)}
  : ∀ x ∈ slower (upper A), ∃ y ∈ slower (upper A), x < y := by

  intro x hx
  by_contra h
  simp[lt_inst] at h -- so x is a max of slower (upper A.val)
  have h0 : x ∈ lower (upper A) := by apply slower_lower hx

  have h1 : x ∈ upper A := by
    intro a ha
    by_cases h1 : a ∈ slower (upper A)
    . exact h a h1
    . simp at h1
      rw[hA] at ha
      --have h2' : ∀ t ∈ slower (lower A), t ≤ a := sorry

      simp[slower] at h1


      obtain ⟨ y, ⟨ hy, hay ⟩ ⟩ := h1
      have h2 := hy x (by rw[←hA] at h0; exact h0)
      have h3 : y ≤ a := by
        simp[lt_inst] at hay
        exact Eq.ge (hay (ha y hy))
      have h4 : x ≤ a := by exact Poset.trans x y a (h0 y hy) h3
      have h5 : a ∈ upper A := by apply thing hy h3

      -- a is a lub
      have alub : ∀ b ∈ upper A, a ≤ b := by
        intro b hb
        apply hb a
        rw[hA]
        exact ha

      by_cases hxla : x < a
      . let s := (x+a)/2
        have hxs : x < s := by exact left_lt_add_div_two.mpr hxla
        have hsa : s < a := by exact add_div_two_lt_right.mpr hxla


        have hts : ∀ t ∈ slower (upper A), t < s  := by
          intro t ht
          have := h t ht
          exact lt_of_le_of_lt (h t ht) hxs

        apply h a
        intro q hq
        have := alub q hq

        sorry

      . exact Rat.not_lt.mp hxla

  have h2 := hx x h1
  simp[lt_inst] at h2



example (x m : ℚ ) : (x < m ∧ ∀ y < m, y ≤ x) → False := by
  intro ⟨ h1, h2 ⟩

  sorry

example (m: ℚ) : ∀ x < m, ∃ y < m, x < y := by
  intro x hx
  use (x+m)/2
  apply And.intro
  . linarith
  . linarith

example (m : ℚ) : ∀ x ∈ slower {m}, ∃ y ∈ slower {m}, x < y := by
  intro x hx
  use (x+m)/2
  simp_all[slower,lt_inst,le_inst,Poset.le]
  obtain ⟨ h1, h2 ⟩ := hx
  apply And.intro
  . apply And.intro
    . linarith
    . intro h
      exact h2 (by linarith)
  . have : x < m := by exact lt_of_le_of_ne h1 h2
    linarith




-- def to_cut (A : DM ℚ) (ha : finite A.val) : DCut := ⟨
--   slower (upper A.val),
--   sorry,
--   sorry,
--   by
--     intro x y ⟨ hxy, hy ⟩ q hq
--     have := hy q hq
--     rw[←lt_simp] at this ⊢
--     exact lt_of_le_of_lt hxy this,
--   by
--     intro x hx
--     by_contra h
--     simp[←lt_simp] at h -- so x is a max of slower (upper A.val)

--     have hx' : x ∈ lower (upper A.val) := by
--       exact slower_lower hx

--     sorry


--     -- x ∈ (-∞, a)
--     -- ∀ y ∈ (-∞, a), y ≤ x
--     -- (-∞, a) = (-∞, x]


--     -- should be able to show slu A.val ∩ u A.val = ∅
-- ⟩

-- theorem fin_down_to_up {A : Set ℚ} : finite A ↔ finite (upper A) := sorry

-- theorem fin_down_to_neg_up {A : Set ℚ} : finite A ↔ finite { x | -x ∈ upper A } := sorry

-- -- theorem a_upper_a_disjoint' {A : DM ℚ} {nf : finite A.val}
-- --   : ∀ a ∈ A.val, ∀ b ∈ upper A.val, a < b := by
-- --   intro a ha b hb
-- --   rw[←A.h] at ha
-- --   simp[lower] at ha
-- --   have := ha b hb

-- --   sorry

-- theorem a_upper_a_disjoint {A : DM ℚ} {nf : finite A.val}
--   : A.val ∩ upper (A.val) = ∅ := by
--     ext x
--     constructor
--     . intro ⟨ h1, h2 ⟩
--       rw[←A.h] at h1
--       simp_all[lower,upper]
--       have ⟨ q, hq ⟩ := not_empty_to_exists nf.left
--       have := h2 q hq

--       sorry
--     . simp

-- theorem upper_open {A : DM ℚ} {nf : finite A.val}
--   : ∀ y ∈ upper A.val, ∃ x ∈ upper A.val, x < y := by
--   intro y hy
--   have ⟨ q, hq ⟩ := not_empty_to_exists nf.left
--   have hA := A.h
--   by_contra h
--   simp at h
--   have h1 : ∀ a ∈ A.val, a ≤ y := by
--     intro a ha
--     exact hy a ha

--   have h2 : y ∈ A.val := by
--     rw[←A.h]
--     intro z hz
--     exact h z hz

--   --simp[upper] at hy





--   sorry



-- def to_cut (A : DM ℚ) (ha : finite A.val) : DCut := ⟨
--   { x | -x ∈ upper A.val },
--   not_empty_to_exists (fin_down_to_neg_up.mp ha).left,
--   not_full_to_not_exists (fin_down_to_neg_up.mp ha).right,
--   by
--     intro x y ⟨ hxy, hy ⟩
--     rw[←A.h] at hy ⊢
--     simp[lower] at hy ⊢
--     intro a ha
--     have := hy a ha
--     linarith,
--   by
--     intro x hx
--     simp_all

--     use (1+x)
--     sorry
-- ⟩
