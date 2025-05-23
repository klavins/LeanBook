--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.

import Mathlib

def R1' (x y : Fin 4) := match x,y with
  | 0,0 => True
  | 0,1 => True
  | 1,0 => True
  | 1,1 => True
  | 2,3 => True
  | 3,0 => True
  | 3,3 => True
  | _,_ => False

def R1 (x y : Fin 4) := match x with
  | 0 => y = 0 ∨ y = 1
  | 1 => y = 0 ∨ y = 1
  | 2 => y = 3
  | 3 => y = 0 ∨ y = 3

-- def R1' : Set (List ℕ):= {[0,0], [0,0]}

universe u

def my_refl {A : Type u} (r : A → A → Prop)
  := ∀ x : A, r x x

example : ¬(my_refl R1) := by
  intro h
  simp[my_refl,R1] at h
  have := h 2
  simp at this

------------------

def my_le (x y: Nat) := ∃ c, x = y+c

example : my_refl my_le := by
  unfold my_refl my_le
  intro x
  use 0
  exact rfl


def my_div (x y : Nat) := ∃ k, y = k*x

example : my_refl my_div := by
  unfold my_refl my_div
  intro x
  use 1
  simp

theorem test2 {i : ℕ}
              {V : Finset (Fin i → ℂ)}
              (M : Matrix (Fin i) (Fin i) ℂ)
  : ∑ v : V, Matrix.mulVec M v = Matrix.mulVec M (∑ v : V, v) := by
  let L := Finset.toList V
  match L with
  | [] => sorry
  | v :: L' => sorry

#check Fintype.sum_eq_add_sum_subtype_ne
#check Finset.toList
