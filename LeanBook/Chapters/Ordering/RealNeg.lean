--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.

import Mathlib
import LeanBook.Chapters.Ordering.Completions
import LeanBook.Chapters.Ordering.Reals
import LeanBook.Chapters.Ordering.RealAdd

universe u v

namespace LeanBook.Ordering
open LeanBook.Ordering

/- ### Negation and Subtraction -/

def set_negate (A : Set ℚ) : Set ℚ :=
  { b : ℚ | -b ∈ (upper A) }

theorem set_negate_lu (A: Set ℚ)
  : lower (upper (set_negate A)) = set_negate A := by
  simp[set_negate]
  ext x
  constructor
  . simp_all[lower,upper]
    intro hx a ha
    have := hx (-a) ?_
    . linarith
    . intro b hb
      exact le_neg_of_le_neg (hb a ha)
  . intro q b hb
    exact hb x q

def negate (A : Real) : Real:=
 ⟨ set_negate A.val, set_negate_lu A.val ⟩

instance neg_inst : Neg Real := ⟨ negate ⟩

def sub (A B : Real) : Real := A + (-B)

instance hsub_inst : HSub Real Real Real:= ⟨ sub ⟩

instance sub_inst : Sub Real := ⟨ sub ⟩

instance dmq_total_order : TotalOrder (DM ℚ) :=
  ⟨ by apply dm_total_order ⟩

theorem add_inv_le_zero {A : Real} : A - A ≤ ofRat (0:ℚ) := by

  simp[hsub_inst,sub,hadd_inst,add,set_sum,ofRat,DM.make,le_inst,Poset.le]
  rw[←DM.down_is_dm]
  apply sub_low
  apply sub_up

  intro q hq
  obtain ⟨ a, ⟨ ha, ⟨ b, ⟨ hb, hqab ⟩ ⟩ ⟩ ⟩ := hq
  simp[down]
  have : b = q-a := by linarith
  rw[this] at hb
  simp[neg_inst,negate,set_negate,lower,upper] at hb
  have h1 := hb a ?h -- TODO: Write this without
  . linarith
  . exact ha

theorem add_inv {A : Real} {hninf : A ≠ top} {hnninf : A ≠ bot}
  : A - A = ofRat (0:ℚ) := by

  simp[hsub_inst,sub,hadd_inst,add,set_sum,ofRat,DM.make]
  apply Set.eq_of_subset_of_subset
  . apply add_inv_le_zero

  . have h : down 0 ⊆ {c | ∃ x ∈ A.val, ∃ y ∈ (-A).val, c = x + y} := by
      intro c hc
      simp_all[down]
      rw[←top_simp] at hninf -- next line needs top expressed in terms of Semilattice
      obtain ⟨ b, hb ⟩ := DM.not_top_is_bounded hninf
      simp[le_inst,Poset.le,ofRat,DM.make,down] at hb
      sorry

    have := sub_low (sub_up h)
    rw[DM.down_is_dm] at this
    exact this



/- ### Negation is an Order-Preserving Involution -/

theorem neg_neg {x : Real} : - -x = x := by

  simp[neg_inst]
  apply DM.ext
  nth_rewrite 1 [negate]
  simp[set_negate]
  ext q
  constructor

  . intro hq
    simp at hq
    simp[negate,set_negate] at hq
    rw[upper] at hq
    nth_rewrite 1 [upper] at hq
    simp at hq
    rw[←x.h]
    intro y hy
    have := hq (-y)
    simp at this
    exact this hy

  . intro hq
    simp
    intro y hqy
    simp[negate,set_negate] at hqy
    rw[upper] at hqy
    simp at hqy
    have := hqy q hq
    linarith

example (x y : Real) : x ≤ y → -y ≤ -x := by
  intro h
  intro q h1
  intro r hr
  exact h1 r (h hr)

theorem neg_top_eq_bot : -top = bot := by

  simp[top,bot,neg_inst,negate,set_negate]
  apply Set.eq_of_subset_of_subset

  . intro q hq
    simp[lower,upper] at hq
    have := hq (1-q)
    linarith

  . intro q hq
    exact False.elim hq

theorem neg_bot_eq_top : -bot = top := by
  rw[←@neg_neg top,neg_top_eq_bot]










/- ## Exercises -/

example : -(ofRat 0) = ofRat 0 := by

  simp[hadd_inst,add,neg_inst,ofRat,DM.make,negate]
  simp[set_negate]

  apply Set.eq_of_subset_of_subset

  . intro x hx
    simp_all[down,lower,upper]
    exact neg_nonneg.mp (hx 0 rfl)

  . intro x hx y hy
    simp_all[down]
    linarith


example : -ofRat 1 = ofRat (-1) := by
  simp[ofRat,neg_inst,DM.make,negate,set_negate]
  ext x
  simp_all[down,upper]
  constructor

  . intro h
    have := h 1 (by exact rfl)
    exact le_neg_of_le_neg (h 1 rfl)

  . intro hx a ha
    linarith

example (q : ℚ) : -ofRat q = ofRat (-q) := by
  simp[ofRat,neg_inst,DM.make,negate,set_negate]
  ext x
  simp_all[down,upper]
  constructor

  . intro h
    have := h q (by exact Poset.refl q)
    exact le_neg_of_le_neg this

  . intro hx a ha
    linarith

example (q : ℚ) : ofRat q - ofRat q = ofRat 0 := by

  simp[ofRat,neg_inst,hsub_inst,sub,hadd_inst,add,DM.make,negate,set_negate]

  simp[set_sum,down]
  ext x
  constructor

  . simp[lower,upper]
    intro hx
    apply hx 0
    intro y z hz r hr h
    have := hr q (by exact Poset.refl q)
    linarith

  . intro hx p hp
    simp[upper] at hp
    apply hp x q (by apply Poset.refl) (x-q) ?_ (by linarith)
    intro a a_1
    simp_all only [Set.mem_setOf_eq, neg_sub]
    linarith


def join (A : Real) : Real := ⟨
    (DM.join {A}).val,
    by apply DM.union_in_dm
  ⟩

example (A : Real) : A ≤ join A := by
  apply DM.join_ub
  simp
