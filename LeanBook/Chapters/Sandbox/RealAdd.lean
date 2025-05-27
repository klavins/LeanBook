--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.

import Mathlib
import LeanBook.Chapters.Ordering.Completions
import LeanBook.Chapters.Ordering.Reals
import LeanBook.Chapters.Appendix

universe u v

namespace LeanBook.Ordering
open LeanBook.Ordering

/- ### Addition -/

def set_sum (A B : Set ℚ) : Set ℚ :=
  lower ( upper { c : ℚ | ∃ x ∈ A, ∃ y ∈ B, c = x + y })

theorem set_sum_lu (A B : Set ℚ)
  : lower (upper (set_sum A B)) = set_sum A B := by
  simp[set_sum]
  rw[←up_ulu]

def add (A B : Real) : Real :=
 ⟨ set_sum A.val B.val, set_sum_lu A.val B.val ⟩

instance hadd_inst : HAdd Real Real Real := ⟨ add ⟩

instance add_inst : Add Real := ⟨ add ⟩


/- #### Addtiion is Commutative -/

theorem set_sum_comm_aux {A B : Set ℚ}
  : {c | ∃ x ∈ A, ∃ y ∈ B, c = x + y} = {c | ∃ x ∈ B, ∃ y ∈ A, c = x + y} := by
  ext q
  simp
  constructor
  repeat
  . intro ⟨ a, ⟨ ha, ⟨ b, ⟨ hb, hq ⟩ ⟩ ⟩ ⟩
    use b
    simp[hb]
    use a
    simp[ha]
    linarith

theorem set_sum_comm {A B : Set ℚ} : set_sum A B = set_sum B A := by
  simp_all[set_sum,set_sum_comm_aux]

theorem add_comm {x y : Real} : x + y = y + x := by
  simp[hadd_inst,add]
  apply set_sum_comm

instance add_comm_inst : AddCommMagma Real := ⟨ @add_comm ⟩



/- #### Zero is an Additive Identity -/

theorem add_zero_right {X : Real} : X + 0 = X := by
  obtain ⟨ S, h ⟩ := X
  simp[hadd_inst,add,set_sum]
  rw[←h]
  congr!
  ext c; constructor
  . intro ⟨ s, ⟨ hs, ⟨ t, ⟨ ht, hst ⟩ ⟩ ⟩ ⟩
    have ht' : t ≤ 0 := ht
    rw[←h]
    intro a ha
    have := hs a ha
    linarith
  . intro hc; rw[←h] at hc
    use c; constructor
    . exact hc
    . use 0
      exact ⟨ rfl, Eq.symm (Rat.add_zero c) ⟩

theorem add_zero_left {X : Real} : 0 + X = X := by
  rw[add_comm,add_zero_right]

instance add_zero_inst : AddZeroClass Real :=
  ⟨ @add_zero_left, @add_zero_right ⟩

example : (ofRat 1) + (ofRat 1) = (ofRat 2) := by
  simp[hadd_inst,ofRat,DM.make,add,set_sum]
  nth_rewrite 3 [←DM.down_is_dm]
  congr!
  ext x
  constructor
  . simp
    intro a ha b hb hab
    simp_all[down]
    linarith
  . intro hx
    simp_all
    use (x-1)
    apply And.intro
    . simp_all[down]
      linarith
    . use 1
      simp_all[down]

example (x y z : ℚ) (h: x + y = z) : (ofRat x) + (ofRat y) = (ofRat z) := by

  simp[hadd_inst,ofRat,DM.make,add,set_sum]
  nth_rewrite 3 [←DM.down_is_dm]
  congr!
  ext s
  simp_all[down]

  constructor

  . simp
    intro a ha b hb hab
    linarith

  . intro hq
    rw[←h] at hq
    use x-(z-s)
    apply And.intro
    . simp_all
    . use y
      apply And.intro
      . simp
      . linarith

theorem add_op {x y x' y': Real} : x ≤ x' → y ≤ y' → x+y ≤ x'+y' := by
  intro hxx hyy
  simp_all[hadd_inst,add,le_inst,Poset.le,set_sum]
  apply sub_low
  apply sub_up
  simp
  intro z a ha b hb hab
  use a
  apply And.intro
  . exact hxx ha
  . use b
    exact ⟨ hyy hb, hab ⟩

#check DM.inter_sub

/- ### Addition with Top and Bot -/

theorem sum_bot_left {x : Real} : bot + x = bot := by
  simp[hadd_inst,add,bot]
  simp[set_sum,lower,upper]
  apply Set.eq_of_subset_of_subset
  . intro y hy
    simp at hy
    have := hy (y-1)
    linarith
  . exact Set.empty_subset {x | ∀ (a : ℚ), x ≤ a}

theorem sum_bot_right {x : Real} : x + bot = bot := by
  rw[add_comm]
  exact sum_bot_left

theorem sum_top_left {x : Real} (hx : x ≠ bot): top + x = top := by
  simp[hadd_inst,add,top,bot]
  apply Set.eq_of_subset_of_subset
  . intro _ _
    exact trivial
  . intro y hy
    simp[set_sum,lower,upper]
    intro q hq
    obtain ⟨ v, hv ⟩ := not_bot_nonempty hx
    have := hq y (y-v) v hv
    simp_all

theorem sum_top_right {x : Real} (hx : x ≠ bot): x + top = top := by
  rw[add_comm]
  exact sum_top_left hx

/- #### Addition is Associative -/

theorem add_assoc (S T U : Real) : (S+T)+U = S+(T+U) := by

  simp_all[hadd_inst,add]
  nth_rw 1 [set_sum]
  nth_rw 2 [set_sum]
  apply congr rfl
  apply congr rfl
  ext q
  simp

  constructor

  . intro ⟨ st, ⟨ hst, ⟨ u, ⟨ hu, hq ⟩ ⟩ ⟩ ⟩
    have : ∃ s ∈ S.val, ∃ t ∈ T.val, st = s+t := by
      -- this may not be true. st ∈ lu set_sum A B, which may
      -- in general contain points not in the sum
      sorry
    have ⟨ s, ⟨ hs, ⟨ t, ⟨ ht, h ⟩ ⟩ ⟩ ⟩ := this
    use s
    apply And.intro
    . exact hs
    . use t+u
      apply And.intro
      . simp[set_sum]
        intro c hc
        simp[upper] at hc
        exact  hc (t+u) t ht u hu (by linarith)
      . linarith


  . intro ⟨ s, ⟨ hs, ⟨ tu, ⟨ htu, hq ⟩ ⟩ ⟩ ⟩
    sorry

theorem add_assoc' (S T U : Real) : (S+T)+U = S+(T+U) := by

  simp_all[hadd_inst,add]
  nth_rw 1 [set_sum]
  nth_rw 2 [set_sum]
  ext q

  constructor

  . intro hq
    simp_all[lower]
    intro c hc
    apply hq c
    simp_all[upper]
    intro z st hst u hu h

    simp[set_sum,lower] at hst

    sorry


  . intro hq
    sorry








-- ------------------------------------------

@[ext]
structure DCut where
  A : Set ℚ
  ne : ∃ q, q ∈ A
  nu : ∃ q, q ∉ A
  dcl : ∀ x y, x ≤ y ∧ y ∈ A → x ∈ A

  -- egt : ∀ x ∈ A, ∃ y ∈ A, x < y     -- this condition prevents down q
                                       -- from being converted to a cut.
                                       -- it is okay, but less traditional,
                                       -- to leave it out, simply moving
                                       -- limit points from A to B

def DCut.B (c : DCut) : Set ℚ := Set.univ \ c.A

def finite (A : DM ℚ) := A.val ≠ ∅ ∧ A.val ≠ Set.univ

theorem not_full_to_not_exists {A : Type u} {S : Set A}
  : S ≠ Set.univ → ∃ x, x ∉ S := by
  intro h
  exact (Set.ne_univ_iff_exists_not_mem S).mp h

def to_cut (A : DM ℚ) (ha : finite A) : DCut := ⟨
  A.val,
  not_empty_to_exists ha.left,
  not_full_to_not_exists ha.right,
  by
    intro x y ⟨ hxy, hy ⟩
    rw[←A.h] at hy ⊢
    simp[lower] at hy ⊢
    intro a ha
    have := hy a ha
    linarith
⟩

def from_cut (c : DCut) : DM ℚ := ⟨ lower (upper c.A), by
  have hc := c.dcl
  obtain ⟨ q, hq ⟩ := c.ne
  rw[←up_ulu]
⟩

theorem from_to_cut {A : DM ℚ} {ha: finite A} : from_cut (to_cut A ha) = A := by
  simp[from_cut,to_cut]
  ext x
  constructor
  . simp
    intro hx
    rw[←A.h]
    exact hx
  . apply sub_lu

theorem lu_all {A : Set ℚ} : lower (upper A) = Set.univ → upper A = ∅ := by
  intro ha
  have ha' : ∀ x, x ∈ lower (upper A) := by
    rw[ha]
    exact fun x ↦ trivial
  ext x
  constructor
  . intro hx
    have h1 : upper A ≠ ∅ := by exact ne_of_mem_of_not_mem' hx fun a ↦ a
    have h2 : ∀ q, q ≤ x := by
      intro q
      have h3 := ha' q
      simp[lower] at h3
      exact h3 x hx
    have := h2 (x+1)
    linarith
  . intro h
    exact False.elim h

theorem to_from_cut (c : DCut) : to_cut (from_cut c) (by
  simp[finite,from_cut]
  apply And.intro
  . intro h
    have ⟨ q, hq ⟩ := c.ne
    have : q ∈ lower (upper c.A)
    apply sub_lu
    exact hq
    simp_all only [Set.mem_empty_iff_false]
  . intro h
    have h1 := lu_all h
    have ⟨ q, hq ⟩ := c.nu
    have h3 : q ∈ upper c.A := by
      by_contra nope
      simp[upper] at nope
      have ⟨ x, ⟨ hx, hqx ⟩ ⟩ := nope
      have := c.dcl q x ⟨ by linarith, hx ⟩
      exact hq this
    simp_all only [and_imp, Set.mem_empty_iff_false]
  ) = c := by
  simp[to_cut,from_cut]
  ext q
  constructor
  . intro hq -- q is less than every upper bound of c.A
    simp_all
    have ⟨ r, hr ⟩ := c.ne
    have dcl := c.dcl q
    -- this doesn't work. q ∈ c.A only if c.A is lu closed.

    sorry
  . apply sub_lu

def dsum (a b : DCut) : DCut := ⟨

  { z | ∃ x ∈ a.A, ∃ y ∈ b.A, x+y=z },

  by
    obtain ⟨ x, hx ⟩ := a.ne
    obtain ⟨ y, hy ⟩ := b.ne
    exact ⟨ x+y, ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, by linarith ⟩ ⟩ ⟩ ⟩ ⟩,

  sorry,

  by
    intro s t ⟨ h1, h2 ⟩
    simp_all
    obtain ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, h ⟩ ⟩ ⟩ ⟩ := h2

    have hyts : y - (t - s) ∈ b.A := by
      have h3 : 0 ≤ t-s := by linarith
      have h4 : y - (t-s) ≤ y := by linarith
      exact b.dcl (y-(t-s)) y ⟨h4,hy⟩

    exact ⟨ x, ⟨ hx, ⟨ y - (t-s), ⟨ hyts, by linarith ⟩ ⟩ ⟩ ⟩

⟩

theorem dcut_sum_assoc {a b c : DCut} : dsum (dsum a b) c = dsum a (dsum b c) := by
  simp[dsum]
  ext q
  constructor
  . intro hq
    simp_all
    obtain ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, ⟨ z, ⟨ hz, hsum ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ := hq
    exact ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, ⟨ z, ⟨ hz, by linarith ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  . intro hq
    simp_all
    obtain ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, ⟨ z, ⟨ hz, hsum ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ := hq
    exact ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, ⟨ z, ⟨ hz, by linarith ⟩ ⟩ ⟩ ⟩ ⟩ ⟩



theorem finite_sum {A B : DM ℚ} : finite A → finite B → finite (A + B) := by
  intro ha hb
  simp[hadd_inst,add,finite]
  apply And.intro
  . intro h

    sorry
  . sorry

theorem dm_sum_same {A B : DM ℚ} {ha : finite A} {hb : finite B}
  : A+B = from_cut ( dsum (to_cut A ha) (to_cut B hb) ) := by
  apply DM.ext
  simp[hadd_inst,add,from_cut,to_cut,dsum,set_sum]
  apply congr
  simp
  apply congr
  simp
  aesop

theorem from_cut_finite {c : DCut} : finite (from_cut c) := by
  have ha := c.ne
  simp[finite,from_cut]
  apply And.intro
  . intro h
    obtain ⟨ q, hq ⟩ := ha
    have : q ∈ lower (upper c.A) := by
      apply sub_lu
      exact hq
    simp_all only [Set.mem_empty_iff_false]
  . intro h
    obtain ⟨ r, hr ⟩ := c.nu
    obtain ⟨ q, hq ⟩ := ha

    have dcl := c.dcl



    have ane : c.A ≠ ∅ := by exact ne_of_mem_of_not_mem' hq fun a ↦ a
    have aup : ∃ x, x ∈ upper c.A := by
      simp[upper]
      use q
      sorry
    have uane : upper c.A ≠ ∅ := by exact Set.nonempty_iff_ne_empty.mp aup

    sorry


example {A B C : DM ℚ} {ha : finite A} {hb : finite B}  {hc : finite C}
  : A + (B + C) = (A + B) + C  := by
  have hab := @finite_sum A B
  have hcn := @finite_sum B C
  have sbc := @dm_sum_same B C hb hc
  rw[sbc]
  have sab := @dm_sum_same A B ha hb
  rw[sab]
  rw[dm_sum_same]
  rw[dm_sum_same]
  apply congr rfl
  simp[to_from_cut]
  rw[←dcut_sum_assoc]
  sorry
