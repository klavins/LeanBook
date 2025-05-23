
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Ordering/RealAdd.lean'>Code</a> for this chapter</span>
 ### Addition 
```lean
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
```
 #### Addtiion is Commutative 
```lean
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
```
 #### Zero is an Additive Identity 
```lean
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
```
 ### Addition with Top and Bot 
```lean
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
```
 #### Addition is Associative 
```lean
theorem add_assoc (S T U : Real) : (S+T)+U = S+(T+U) := by

  simp_all[hadd_inst,add]
  nth_rw 1 [set_sum]
  nth_rw 2 [set_sum]
  apply congr rfl
  apply congr rfl
  ext q
  simp

  constructor

  . intro ⟨ st, ⟨ hst, ⟨ u, ⟨ hu, hq ⟩ ⟩ ⟩  ⟩
    sorry

  . intro ⟨ s, ⟨ hs, ⟨ tu, ⟨ htu, hq ⟩ ⟩ ⟩ ⟩
    sorry
```

<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
