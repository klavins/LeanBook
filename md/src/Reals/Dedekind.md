
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Reals/Dedekind.lean'>Code</a> for this chapter</span>
 # The Dedekind Reals

We have seen that te natural numbers may be defined inductively, that the integers can be constructed from the natural numbers, and that this rational numbers can be constructed from the natural numbers and the real numbers. Here, we construct the real numbers from the rational numbers. There are several methods of doing this. For example, Mathlib defines the real numbers as a quotient space of Cauchy Sequences. As an exercise, we provde an alternative definition using Dedekind cuts.

Dedekind's representation of a real number `r` is as a pair `(A,B)` where `A ⊆ ℚ` is the set of all rational numbers less than `r` and `B = ℚ \ A`. The idea is that `A` approximates `r` from below and `B` approximates `r` from above. In the case that `r ∈ ℚ`, then `A = (∞,r)` and `B = [r,∞)`. Since `A` completely determines the cut, we work mainly with it, only occasionally referring to `B`.

That this definition satisfies the properties of the real numbers needs to be proved, which is what this chapter is about. Specifically, we will prove that

  - The set of cuts is totally ordered
  - The set of cuts form a _field_
  - Every bounded, non-empty set of cuts has a least upper bound

The last property distinguishes the real numbers from the rationals.

A standard reference for Dedekind cuts is Rudin's Principles of Mathematics. In the 3rd edition, cuts are defined on pages 17-21.

## Definition

First, we define a structure to capture the precise definition of a cut `A ⊆ ℚ`. We require that A is nonempty, that it is not ℚ, that it is downward closed, and that is interval. 
```lean
@[ext]
structure DCut where
  A : Set ℚ
  ne : ∃ q, q ∈ A                   -- not empty
  nf : ∃ q, q ∉ A                   -- not ℚ
  dc : ∀ x y, x ≤ y ∧ y ∈ A → x ∈ A -- downward closed
  op : ∀ x ∈ A, ∃ y ∈ A, x < y      -- open

open DCut

def DCut.B (c : DCut) : Set ℚ := Set.univ \ c.A

theorem not_in_a_in_b {c :DCut} {q : ℚ} : q ∉ c.A → q ∈ c.B := by simp[B]
```
 ## Making Rationals into Reals

All rational numbers are also real numbers via the map that identifies a rational `q` with the interval `(∞,q)` of all rationals less than `q`. We call this set `odown q`, where `odown` is meant to abbreviate `open, downward closed`. 
```lean
def odown (q : ℚ) : Set ℚ := { y | y < q }
```
 To prove that `odown q` is a Dedekind cut requires we show it is nonempty, not `ℚ` itself, downward closed, and open. For the first two theorems we use use the facts that `q-1 ∈ (∞,q)` and `q+1 ∉ (∞,q)`. 
```lean
theorem odown_ne {q : ℚ} : ∃ x, x ∈ odown q := by
  use q-1
  simp[odown]

theorem odown_nf {q : ℚ} : ∃ x, x ∉ odown q := by
  use q+1
  simp[odown]
```
 That `odown` q is downward closed follows from the definitions. 
```lean
theorem odown_dc {q : ℚ} : ∀ x y, x ≤ y ∧ y ∈ odown q → x ∈ odown q := by
  intro x y ⟨ hx, hy ⟩
  simp_all[odown]
  linarith
```
 To prove `odown q` is open, we are given `x ∈ odown` and need to supply `y ∈ odown q` with `x < y`. Since `q` is the least upper bound of `odown q`, we choose `(x+q)/2`.
```lean
theorem odown_op {q : ℚ} : ∀ x ∈ odown q, ∃ y ∈ odown q, x < y:= by
  intro x hx
  use (x+q)/2
  simp_all[odown]
  apply And.intro
  repeat linarith
```
 With these theorems we define the map `ofRat : ℚ → DCut` that embeds the rationals into the Dedekind cuts. 
```lean
def ofRat (q : ℚ) : DCut :=
  ⟨ odown q, odown_ne, odown_nf, odown_dc, odown_op ⟩
```
 With this map we can define 0 and 1. 
```lean
instance zero_inst : Zero DCut := ⟨ ofRat 0 ⟩
instance one_inst : One DCut := ⟨ ofRat 1 ⟩

theorem zero_rw : A 0 = odown 0 := by rfl

theorem one_rw : A 1 = odown 1 := by rfl
```
 ## Simple Properties of Cuts

Here we define some simple properties that wil make subsequent proofs less cumbersome. The first says for `x in A` and `y in B`, that `x < y`.

```lean
theorem b_gt_a {c : DCut} {x y : ℚ} : x ∈ c.A → y ∈ c.B → x < y := by
  intro hx hy
  simp[B] at hy
  by_contra h
  exact  hy (c.dc y x ⟨ Rat.not_lt.mp h, hx ⟩)
```
 An alternate for of this same theorem, in which `B` is characterized as `ℚ \ A` is also useful. 
```lean
theorem a_lt_b {c : DCut} {x y : ℚ }: x ∈ c.A → y ∉ c.A → x < y := by
  intro hx hy
  exact b_gt_a hx (not_in_a_in_b hy)
```
 Since `A` is downward closed, one can easily show `B` is upward closed. 
```lean
theorem not_in_a_gt {c : DCut} {a b: ℚ} : a ∉ c.A → a ≤ b → b ∉ c.A := by
  intro h1 h2 h3
  exact h1 (c.dc a b ⟨ h2, h3 ⟩)
```
 ## Ordering

Next we show that cuts are totally ordered by the subset relation. First, we define and instantiate the less than and less than or equal relations on cuts. 
```lean
instance lt_inst : LT DCut := ⟨ λ x y => x ≠ y ∧ x.A ⊆ y.A ⟩
instance le_inst : LE DCut := ⟨ λ x y => x.A ⊆ y.A ⟩
```
 To check these definitions make sense, we verify them with rational numbers. 
```lean
example {x y : ℚ} : x = y → (ofRat x) ≤ (ofRat y) := by
  intro h
  simp_all[ofRat,odown,le_inst]
```
 It is useful to be able to rewrite the less than relation `<` in terms of inequality and `≤`, and to rewrite `≤` in terms of equality and `<`.  
```lean
theorem DCut.lt_of_le {x y: DCut} : x < y ↔ x ≠ y ∧ x ≤ y := by
  exact Eq.to_iff rfl

theorem DCut.le_of_lt {x y: DCut} : x ≤ y ↔ x = y ∨ x < y := by
  simp_all[le_inst,lt_inst]
  constructor
  . intro h
    simp[h]
    exact Classical.em (x=y)
  . intro h
    cases h with
    | inl h1 => exact Eq.subset (congrArg A h1)
    | inr h1 => exact h1.right
```
 Next we prove that cuts form a total order, and instantiate this fact with the TotalOrder class from Mathlib. 
```lean
theorem total {x y : DCut} : x ≤ y ∨ y ≤ x := by
  by_cases h : x ≤ y
  . exact Or.inl h
  . apply Or.inr
    simp_all[le_inst]
    intro b hb
    rw[Set.subset_def] at h
    simp at h
    obtain ⟨ a, ⟨ ha1, ha2 ⟩ ⟩ := h
    exact x.dc b a ⟨ le_of_lt (a_lt_b hb ha2), ha1 ⟩

instance total_inst : IsTotal DCut (· ≤ ·) := ⟨ @total ⟩
```
 The total order property allows crisply define positive and negative numbers. 
```lean
def isPos (x : DCut) : Prop := 0 < x
def isNeg (x : DCut) : Prop := x < 0
```
 We can also use the total order property to prove that `DCut` is _Trichotomous_, that is, that for all `x` and `y`, either `x ≤ y`, `y ≤ x`, or `x=y`. 
```lean
theorem trichotomy (x y: DCut) : x ≤ y ∨ x = y ∨ y ≤ x := by
  apply Or.elim (@total x y)
  . intro h
    rw[DCut.le_of_lt] at h
    cases h with
    | inl h1 => exact Or.inr (Or.inl h1)
    | inr h1 =>
      rw[DCut.lt_of_le] at h1
      exact Or.inl (h1.right)
  . intro h
    exact Or.inr (Or.inr h)

theorem trichotomy_lt (x y: DCut) : x < y ∨ x = y ∨ y < x := by
  have := trichotomy x y
  simp[le_of_lt] at this
  aesop

instance trichotomous_inst : IsTrichotomous DCut (· ≤ ·) := ⟨ trichotomy ⟩

theorem zero_in_pos {a : DCut} (ha : 0 < a) : 0 ∈ a.A := by
  obtain ⟨ h1, h2 ⟩ := ha
  simp at h1
  rw[DCut.ext_iff] at h1
  have h21 := Set.ssubset_iff_subset_ne.mpr ⟨h2, h1⟩
  have ⟨ x, ⟨ hx1, hx2 ⟩ ⟩ := (Set.ssubset_iff_of_subset h2).mp h21
  simp[zero_rw,odown] at hx2
  exact a.dc 0 x ⟨ hx2, hx1 ⟩

theorem non_neg_in_pos {a : DCut} (ha : 0 < a) : ∃ x ∈ a.A, 0 < x := by
  have h0 := zero_in_pos ha
  exact a.op 0 h0

theorem zero_notin_neg {a : DCut} (ha : a < 0) : 0 ∉ a.A := by
  intro h
  simp[lt_inst] at ha
  have ⟨ h1, h2 ⟩ := ha
  have : 0 ∈ A 0 := h2 h
  simp[zero_rw,odown] at this

@[simp]
theorem zero_lt_one : (0:DCut) < 1 := by
  simp[lt_inst]
  apply And.intro
  . intro h
    simp[DCut.ext_iff,zero_rw,one_rw,odown,Set.ext_iff] at h
    have := h 0
    simp_all
  . intro q hq
    simp_all[zero_rw,one_rw,odown]
    linarith

@[simp]
theorem zero_le_one : (0:DCut) ≤ 1 := by
  simp[le_inst]
  intro q hq
  simp_all[zero_rw,one_rw,odown]
  linarith

theorem not_gt_to_le {a : DCut} : ¬0<a ↔ a ≤ 0 := by
  constructor
  . have := trichotomy_lt 0 a
    apply Or.elim this
    . intro h1 h2
      simp_all
    . intro h1 h2
      simp_all
      apply le_of_lt.mpr
      rw[Eq.comm]
      exact h1
  . intro h1 h2
    apply le_of_lt.mp at h1
    simp_all[DCut.ext_iff,lt_inst]
    have ⟨ h3, h4 ⟩ := h2
    simp_all
    apply Or.elim h1
    . intro h
      exact h3 (id (Eq.symm h))
    . intro ⟨ h5, h6 ⟩
      have : A 0 = a.A := by exact Set.Subset.antisymm h4 h6
      exact h3 this
```
 TODO : Instantiate as a partial order 
 **Exercise**: Show that `ofRat` is indeed an order embedding, that is `x ≤ y → ofRat x ≤ ofRat y` for all rational numbers `x` and `y`. 

<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
