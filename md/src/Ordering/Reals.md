
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Ordering/Reals.lean'>Code</a> for this chapter</span>
 ## The Dedekind-MacNielle Reals 
```lean
instance rat_poset : Poset ℚ :=
  ⟨ λ x y => x ≤ y,
    by simp,
    by intro x y h1 h2; linarith,
    by intro x y z h1 h2; linarith ⟩

instance rat_total_order : TotalOrder ℚ := ⟨ @Rat.le_total ⟩

abbrev Real := DM ℚ
```
 ### Making Numbers 
```lean
def ofRat (q : ℚ) : Real := DM.make q

instance real_zero : Zero Real := ⟨ ofRat (0:ℚ) ⟩

instance real_one : One Real := ⟨ ofRat 1 ⟩
```
 ### Top and Bottom 
```lean
def bot : Real := ⟨ ∅, by
  simp[lower,upper]
  ext x
  constructor
  . intro h
    simp at h
    have := h (x-1)
    linarith
  . intro h
    exact False.elim h
  ⟩

def top : Real := ⟨ Set.univ, by
  simp[lower,upper]
  ext x
  constructor
  . intro _
    exact trivial
  . intro h y hy
    exact hy x
  ⟩

theorem neginf_le (S : Real) : bot ≤ S := by
  simp[le_inst,Poset.le,bot]

theorem posinf_ge (S : Real) : S ≤ top := by
  simp[le_inst,Poset.le,top]


theorem not_top_is_bounded {x : Real} : x ≠ top → ∃ q : ℚ, x ≤ ofRat q := by

  intro ht
  simp[top] at ht

  have h1 : x.val ≠ Set.univ := by
    by_contra h
    exact ht (DM.ext h)

  have ⟨ q, hq ⟩ : ∃ q, q ∈ Set.univ \ x.val := by
    by_contra h
    simp at h
    exact h1 (Set.eq_univ_iff_forall.mpr h)

  have h2 : ¬q ∈ x.val := by exact Set.not_mem_of_mem_diff hq

  rw[←x.h] at h2
  simp[upper,lower] at h2
  obtain ⟨ r, ⟨ hr, hrq ⟩ ⟩ := h2

  use r
  simp[ofRat,DM.make,down,le_inst,Poset.le]

  intro y hy
  simp
  exact hr y hy

theorem not_bot_to_exists {x : Real} : x ≠ bot → ∃ v, v ∈ x.val := by
  intro h
  apply Set.nonempty_iff_ne_empty.mpr
  intro hxb
  exact h (DM.ext hxb)
```
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
```
 ### Negation and Subtraction 
```lean
def set_negate (A : Set ℚ) : Set ℚ :=
  lower ( upper { b : ℚ | -b ∈ (upper A) } )

theorem set_negate_lu (A: Set ℚ)
  : lower (upper (set_negate A)) = set_negate A := by
  simp[set_negate]
  rw[←up_ulu]

def negate (A : Real) : Real:=
 ⟨ set_negate A.val, set_negate_lu A.val ⟩

instance neg_inst : Neg Real := ⟨ negate ⟩

def sub (A B : Real) : Real := A + (-B)

instance hsub_inst : HSub Real Real Real:= ⟨ sub ⟩

instance sub_inst : Sub Real := ⟨ sub ⟩

instance dmq_total_order : TotalOrder (DM ℚ) :=
  ⟨ by apply dm_total_order ⟩

theorem add_inv {A : Real} {hninf : A ≠ top} {hnninf : A ≠ bot}
  : A - A = ofRat (0:ℚ) := by

  simp[hsub_inst,sub,hadd_inst,add,
       set_sum,ofRat,DM.make]

  apply Set.eq_of_subset_of_subset

  . rw[←DM.down_is_dm]
    apply sub_low
    apply sub_up
    intro q hq
    obtain ⟨ a, ⟨ ha, ⟨ b, ⟨ hb, hqab ⟩ ⟩ ⟩ ⟩ := hq
    simp[down]
    have : b = q-a := by linarith
    rw[this] at hb
    simp[neg_inst,negate,set_negate,lower] at hb
    have := hb (-a) ?h
    . linarith
    . intro x hx
      apply le_neg_of_le_neg
      exact hx a ha

  . apply Or.elim (TotalOrder.comp (-A) A)

    . intro h              -- Can I use -A ⊆ down 0, down 0 ⊆ A?
                           -- Note: Can't use sub_low/sub_up because
                           -- when q=0 and A ≠ down x it doesn't work

      intro q hq
      simp[down] at hq
      simp[lower]
      intro ab hab
      simp[upper] at hab

      have hqinA : q ∈ A.val := sorry
      have hza : 0 ∈ A.val := sorry

      have hab' := hab q


      by_cases hqma : q ∈ (-A).val
      . have := hab q 0 hza q hqma (by linarith)
        exact this
      . have hw : q ∈ A.val \ (-A).val := by
          exact Set.mem_diff_of_mem hqinA hqma
        obtain ⟨ h1, h2 ⟩ := hw
        simp[neg_inst,negate,set_negate] at h2

        have := hab q
        sorry

      apply hab q (q-ab) ?_ ab ?_ (by linarith)


      sorry

    . sorry
```
 ### Negation is an Order-Preserving Involution 
```lean
theorem neg_neg {x : Real} : - -x = x := by

  simp[neg_inst]
  apply DM.ext
  nth_rewrite 1 [negate]
  simp[set_negate]
  rw[←x.h]
  congr!

  ext q
  constructor

  . intro hq
    simp at hq
    simp[negate,set_negate] at hq
    rw[←up_ulu] at hq
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
    nth_rewrite 2 [upper] at hqy
    simp at hqy
    apply hqy (-q)
    simp[upper]
    intro z hz
    have := hz q hq
    linarith

example (x y : Real) : x ≤ y → -y ≤ -x := by
  intro h
  apply sub_low
  apply sub_up
  intro q h1
  intro r hr
  exact h1 r (h hr)
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
    obtain ⟨ v, hv ⟩ := not_bot_to_exists hx
    have := hq y (y-v) v hv
    simp_all

theorem sum_top_right {x : Real} (hx : x ≠ bot): x + top = top := by
  rw[add_comm]
  exact sum_top_left hx

-- theorem not_top_is_bounded (x:Real) : x ≠ top → ∃ y ≠ top, x ≤ y := by
--   intro h
--   use x
--   exact ⟨ h, Poset.refl x⟩

theorem not_top_is_bounded' (x:Real) : x ≠ top → ∃ q, ∀ v ∈ x.val, v ≤ q := by
  intro h
  by_contra h'
  simp at h'
  have : x.val = Set.univ := by
    apply Set.eq_of_subset_of_subset
    . intro q hq
      trivial
    . intro q hq
      have ⟨ v, ⟨ hv, hqv ⟩  ⟩ := h' q
      rw[←x.h]
      simp[lower,upper]
      intro a ha
      have := ha v hv
      linarith
  have : x = top := by exact DM.ext this
  exact h this

theorem neg_top_eq_bot : -top = bot := by

  simp[top,bot,neg_inst,negate,set_negate]
  apply Set.eq_of_subset_of_subset

  . intro q hq
    simp[lower,upper] at hq
    have := hq (q-1) (by
      intro x hx
      have := hx (-q+1)
      linarith
    )
    linarith

  . intro q hq
    exact False.elim hq

theorem neg_bot_eq_top : -bot = top := by
  rw[←@neg_neg top,neg_top_eq_bot]
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
 ## Exercises 
```lean
example : set_negate (down 0) = down 0 := by

  simp[set_negate]
  nth_rewrite 2 [←DM.down_is_dm]
  congr!

  apply Set.eq_of_subset_of_subset

  . intro x hx
    simp_all[down,lower,upper]
    exact neg_nonneg.mp (hx 0 rfl)

  . intro x hx y hy
    simp_all[down]
    linarith

example : -(ofRat 0) = ofRat 0 := by

  simp[hadd_inst,add,neg_inst,ofRat,DM.make,negate]
  simp[set_negate]
  nth_rewrite 2 [←DM.down_is_dm]
  congr!

  apply Set.eq_of_subset_of_subset

  . intro x hx
    simp_all[down,lower,upper]
    exact neg_nonneg.mp (hx 0 rfl)

  . intro x hx y hy
    simp_all[down]
    linarith


example : -ofRat 1 = ofRat (-1) := by
  simp[ofRat,neg_inst,DM.make,negate,set_negate]
  nth_rewrite 2 [←DM.down_is_dm]
  congr!
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
  nth_rewrite 2 [←DM.down_is_dm]
  congr!
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

  simp[set_sum]
  nth_rewrite 3 [←DM.down_is_dm]
  congr!
  ext x
  constructor

  . intro ⟨ y, ⟨ hy, ⟨ z, ⟨ hz, hyz ⟩ ⟩ ⟩ ⟩
    simp[down] at hy ⊢
    have h1 : z ≤ -q := by
      simp[lower,upper] at hz
      apply hz (-q)
      intro a ha
      have := ha q (by simp[down])
      linarith
    linarith

  . intro hx
    use q
    apply And.intro
    . simp[down]
    . simp[down] at hx
      use x-q
      apply And.intro
      . simp[lower]
        intro a ha
        have := ha (x-q)
        simp at this
        apply this
        simp[upper,down]
        intro b hb
        linarith
      . linarith

def join (A : Real) : Real := ⟨
    (DM.join {A}).val,
    by apply DM.union_in_dm
  ⟩

example (A : Real) : A ≤ join A := by
  apply DM.join_ub
  simp
```

<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
