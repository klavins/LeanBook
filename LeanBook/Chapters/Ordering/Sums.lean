/-

This code is here for me to try to check whether if A+B is defined without lu then
A+B = lu A+B. After a day of trying to prove this, I can't figure it out. Perhaps
it isn't true?

-/


import Mathlib
import LeanBook.Chapters.Ordering.Completions
import LeanBook.Chapters.Ordering.Properties
import LeanBook.Chapters.Ordering.Reals

universe u v

namespace LeanBook.Ordering
open LeanBook.Ordering

def sum (A B : DM ℚ) := { c : ℚ | ∃ x ∈ A.val, ∃ y ∈ B.val, c = x + y }

theorem lu_expand {A : DM ℚ} {c : ℚ}
  : c ∈ lower (upper A.val) ↔ (∀ q : ℚ, (∀ y ∈ A.val, y ≤ q) → c ≤ q) := by
  simp[lower,upper]

theorem lu_sum_expand {A B: DM ℚ} {c : ℚ}
  : c ∈ lower (upper (sum A B)) ↔ (∀ (q : ℚ), (∀ y ∈ sum A B, y ≤ q) → c ≤ q) := by
  simp[lower,upper]

theorem sum_sub_lu_sum (A B : DM ℚ) : sum A B ⊆ lower (upper (sum A B)) := by
  simp[lower,upper]
  apply sub_lu

theorem sum_down_closed {A B : DM ℚ} : ∀ c ∈ sum A B, ∃ x ∈ sum A B, x ≤ c := by
  intro c hc
  use c-1
  apply And.intro
  . simp_all[sum]
    obtain ⟨ x, ⟨ hx, ⟨ b, ⟨ hb, h2 ⟩ ⟩ ⟩ ⟩ := hc
    use x
    apply And.intro
    . exact hx
    . use b-1
      apply And.intro
      . rw[←B.h]
        intro b' hb'
        have := hb' b hb
        linarith
      . linarith
  . linarith

theorem down_closed_alt {A : DM ℚ} : ∀ c ∈ A.val, ∀ x ≥ 0, c-x ∈ A.val := by
  intro c hc x hx
  rw[←A.h] at hc ⊢
  simp_all[lower,upper]
  intro q hq
  exact le_add_of_le_of_nonneg (hc q hq) hx

theorem sum_in_ab {A B : DM ℚ} {a b : ℚ}
  : a ∈ A.val → b ∈ B.val → a+b ∈ sum A B := by
  intro ha hb
  use a
  exact ⟨ ha, by use b ⟩

theorem in_lu {A : DM ℚ} {a : ℚ} : a ∈ A.val → a ∈ lower (upper A.val) := by
  intro ha
  rw[←A.h] at ha
  exact ha

theorem sum_ub {A B : DM ℚ} {a b : ℚ}
  : a ∈ upper A.val → b ∈ upper B.val → a+b ∈ upper (sum A B) := by
  intro ha hb
  simp[upper,sum]
  intro y a' ha' b' hb' hab'
  have h1 : a' ≤ a := by
    apply ha a'
    exact ha'
  have h2 : b' ≤ b := by
    apply hb b'
    exact hb'
  linarith

theorem sum_of_uppers {A B : DM ℚ} {a b c : ℚ}
  : a ∈ upper A.val → b ∈ upper B.val → c ∈ lower (upper (sum A B)) → c ≤ a + b := by
  intro ha hb hc
  rw[lu_sum_expand] at hc  -- hc says that if q is any upper bound for sum A B, then
                           -- c is less than or equal to q
  have hx := sum_ub ha hb
  apply hc (a+b)
  intro y hy
  exact hx y hy




theorem sum_bot_left {x : DM ℚ} : sum bot x = bot.val := by
  simp[sum,bot]

theorem sum_bot_right {x : Real} : sum x bot = bot.val := by
  simp[sum,bot]

theorem sum_top_left {x : Real} (hx : x ≠ bot) : sum top x = top.val := by
  simp[sum,top,bot]
  apply Set.eq_of_subset_of_subset
  . intro a b
    exact trivial
  . intro y hy
    simp[sum,bot,lower,upper]
    obtain ⟨ v, hv ⟩ := not_bot_nonempty hx
    use (y-v)
    use v
    apply And.intro
    . exact hv
    . linarith

theorem radd_comm {a b : Real} : sum a b = sum b a := by
  simp[sum]
  apply Set.eq_of_subset_of_subset
  . intro c hc
    simp_all
    obtain ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, h ⟩ ⟩ ⟩ ⟩ := hc
    use y
    exact ⟨ hy, ⟨ x, ⟨ hx, by linarith ⟩ ⟩ ⟩
  . sorry

theorem sum_top_right {x : Real} (hx : x ≠ bot): sum x top = top.val := by
  rw[radd_comm]
  exact sum_top_left hx

theorem all_sum_parts {A B : DM ℚ}
  : ∀ c ∈ sum A B, ∃ a ∈ A.val, ∃ b ∈ B.val, c=a+b := by
  intro c hc
  simp[sum] at hc
  exact hc

example {A B : DM ℚ} : lower (upper (sum A B)) ⊆ sum A B := by

  intro c hc

  by_cases h1 : A = bot
  . rw[h1,sum_bot_left,bot] at hc ⊢
    simp[lower,upper,bot] at hc
    have := hc (c-1)
    linarith
  by_cases h2 : B = bot
  . rw[h2,sum_bot_right,bot] at hc ⊢
    simp[lower,upper] at hc
    have := hc (c-1)
    linarith
  by_cases h3 : A = top
  . rw[h3,sum_top_left] at hc ⊢
    simp_all[top]
    repeat exact h2
  by_cases h4 : B = top
  . rw[h4,sum_top_right] at hc ⊢
    simp_all[top]
    repeat exact h1

  -- assuming c ∈ lower (upper (sum A B))
  --   ≡ c is less than all upper bounds for sum A B
  -- show c ∈ sum A B

  -- the least upper bound of all elements less than sum A B
  -- is the join.
  let club := DM.join { C : DM ℚ | C.val ⊆ sum A B }

  have : sum A B ⊆ club.val := by
    intro c hc
    simp[club,DM.join,DM.inter,DM.union]
    intro T hT
    sorry



  have : c ∈ club.val := by
    simp[club,DM.join,DM.inter,DM.union]
    intro T hT
    have : c ∈ {x | ∃ T : DM ℚ, T.val ⊆ sum A B ∧ x ∈ T.val} := by
      simp

      sorry
    sorry


  sorry
