
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
```
 ## Making Rationals into Reals

All rational numbers are also real numbers via the map that identifies a rational `q` with the intergal `(∞,q)` of all rationals less than `q`. We call this set `odown q`, where `odown` is meant to abbreviate `open, downward closed`. 
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
 To prove `odown q` is open, we are given `x ∈ odown` and need supply `y ∈ odown q` with `x < y`. Since `q` is the least upper bound of `odown q`, we can simply choose `(x+q)/2`.
```lean
theorem odown_op {q : ℚ} : ∀ x ∈ odown q, ∃ y ∈ odown q, x < y:= by
  intro x hx
  use (x+q)/2
  simp_all[odown]
  apply And.intro
  repeat linarith
```
 With these theorems we can then define a map `ofRat : ℚ → DCut` that embeds the rationals into the Dedekind cuts. 
```lean
def ofRat (q : ℚ ) : DCut :=
  ⟨ odown q, odown_ne, odown_nf, odown_dc, odown_op ⟩
```
 With this map we can define 0 and 1. 
```lean
instance zero_inst : Zero DCut := ⟨ ofRat 0 ⟩
instance one_inst : One DCut := ⟨ ofRat 1 ⟩

theorem b_gt_a {c : DCut} {x y : ℚ}: x ∈ c.A → y ∈ c.B → x < y := by
  intro hx hy
  simp[B] at hy
  have hdc := c.dc
  by_contra h
  simp at h
  exact  hy (hdc y x ⟨ h, hx ⟩)

theorem not_in_a_in_b {c :DCut} {q : ℚ} : q ∉ c.A → q ∈ c.B := by
  simp[B]

theorem not_in_a_gt {c : DCut} {a b: ℚ} : a ∉ c.A → a ≤ b → b ∉ c.A := by
  intro h1 h2 h3
  have := c.dc a b ⟨ h2, h3 ⟩
  exact h1 this

theorem not_in_a {c :DCut} {q : ℚ} : q ∉ c.A → ∀ a ∈ c.A, a < q := by
  intro hq a ha
  by_contra haq
  have haq' : q ≤ a := by exact Rat.not_lt.mp haq
  have := not_in_a_gt hq haq'
  exact this ha

theorem a_lt_b {c : DCut} {x y : ℚ }: x ∈ c.A → y ∉ c.A → x < y := by
  intro hx hy
  by_contra h
  exact hy (c.dc y x ⟨ by linarith, hx ⟩ )
```
 ## Ordering 
```lean
def le (x y: DCut) : Prop := x.A ⊆ y.A

example {x y : ℚ}: x ≤ y → le (ofRat x) (ofRat y) := by
  intro h a ha
  simp_all[ofRat,odown]
  linarith

instance lt_inst : LT DCut := ⟨ λ x y => x ≠ y ∧ le x y ⟩
instance le_inst : LE DCut := ⟨ le ⟩

theorem DCut.lt_of_le {x y: DCut} : x < y ↔ x ≠ y ∧ x ≤ y := by
  exact Eq.to_iff rfl

theorem DCut.le_of_lt {x y: DCut} : x ≤ y ↔ x = y ∨ x < y := by
  constructor
  . intro h
    simp_all[le_inst,le,lt_inst]
    apply Classical.em (x=y)
  . simp_all[le_inst,le,lt_inst]
    intro h
    apply Or.elim h
    intro h
    . exact Eq.subset (congrArg A h)
    . intro h1
      exact h1.right

example {x y : ℚ} : x = y → (ofRat x) ≤ (ofRat y) := by
  intro h
  simp_all[ofRat,odown,le_inst,le]

theorem total {x y : DCut} : x ≤ y ∨ y ≤ x := by
  by_cases h : x ≤ y
  . exact Or.inl h
  . apply Or.inr
    simp_all[le_inst,le]
    intro b hb
    rw[Set.subset_def] at h
    simp at h
    obtain ⟨ a, ⟨ ha1, ha2 ⟩ ⟩ := h
    exact x.dc b a ⟨ le_of_lt (a_lt_b hb ha2), ha1 ⟩

def isPos (x : DCut) : Prop := 0 < x
def isNeg (x : DCut) : Prop := x < 0

theorem trichotomy (x : DCut) : isPos x ∨ x = (ofRat 0) ∨ isNeg x := by
  simp[isPos,isNeg]
  apply Or.elim (@total x (ofRat 0))
  . intro h
    rw[DCut.le_of_lt] at h
    exact Or.symm (Or.intro_left (0 < x) h)
  . intro h
    rw[DCut.le_of_lt] at h
    apply Or.elim h
    . intro h1
      apply Or.inr (Or.inl (Eq.symm h1))
    . intro h1
      apply Or.inl h1
```
 ## Addition 
```lean
def presum (a b : DCut) :=  { z | ∃ x ∈ a.A, ∃ y ∈ b.A, x+y=z }

theorem presum_ne {a b : DCut} :  ∃ q, q ∈ presum a b := by
  obtain ⟨ x, hx ⟩ := a.ne
  obtain ⟨ y, hy ⟩ := b.ne
  exact ⟨ x+y, ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, by linarith ⟩ ⟩ ⟩ ⟩ ⟩

theorem presum_nf {a b : DCut} : ∃ q, q ∉ presum a b := by
    obtain ⟨ x, hx ⟩ := a.nf
    obtain ⟨ y, hy ⟩ := b.nf
    use x+y
    intro h
    obtain ⟨ s, ⟨ hs, ⟨ t, ⟨ ht, hst ⟩ ⟩ ⟩ ⟩ := h
    have hs' := b_gt_a hs (not_in_a_in_b hx)
    have ht' := b_gt_a ht (not_in_a_in_b hy)
    linarith

theorem presum_op {a b : DCut}
  : ∀ x ∈ presum a b, ∃ y ∈ presum a b, x < y := by
  intro c hc
  simp_all[presum]
  obtain ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, h ⟩ ⟩ ⟩ ⟩ := hc
  have hao := a.op
  have hbo := b.op
  obtain ⟨ x', hx', hxx' ⟩ := hao x hx
  obtain ⟨ y', hy', hyy' ⟩ := hbo y hy
  use x'
  apply And.intro
  . exact hx'
  . use y'
    apply And.intro
    . exact hy'
    . linarith

theorem presum_dc {a b : DCut }
  : ∀ (x y : ℚ), x ≤ y ∧ y ∈ presum a b → x ∈ presum a b := by
  intro s t ⟨ h1, h2 ⟩
  simp_all[presum]
  obtain ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, h ⟩ ⟩ ⟩ ⟩ := h2

  have hyts : y - (t - s) ∈ b.A := by
    have h3 : 0 ≤ t-s := by linarith
    have h4 : y - (t-s) ≤ y := by linarith
    exact b.dc (y-(t-s)) y ⟨h4,hy⟩

  exact ⟨ x, ⟨ hx, ⟨ y - (t-s), ⟨ hyts, by linarith ⟩ ⟩ ⟩ ⟩

def sum (a b : DCut) : DCut :=
  ⟨ presum a b, presum_ne, presum_nf, presum_dc, presum_op ⟩

instance hadd_inst : HAdd DCut DCut DCut:= ⟨ sum ⟩

instance add_inst : Add DCut := ⟨ sum ⟩
```
 ## Associative Property Of Addition 
```lean
theorem sum_assoc {a b c : DCut} : (a+b)+c = a + (b+c) := by
  simp[hadd_inst,sum]
  ext q
  constructor
  . intro hq
    simp_all[presum]
    obtain ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, ⟨ z, ⟨ hz, hsum ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ := hq
    exact ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, ⟨ z, ⟨ hz, by linarith ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  . intro hq
    simp_all[presum]
    obtain ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, ⟨ z, ⟨ hz, hsum ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ := hq
    exact ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, ⟨ z, ⟨ hz, by linarith ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

instance addsemigroup_inst : AddSemigroup DCut := ⟨ @sum_assoc ⟩
```
 ## Commutativity 
```lean
theorem sum_comm {a b : DCut} : a + b = b + a := by
  simp[hadd_inst,sum]
  ext q
  constructor
  repeat
  . intro ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, h ⟩ ⟩ ⟩ ⟩
    exact ⟨ y, ⟨ hy, ⟨ x, ⟨ hx, by linarith ⟩ ⟩ ⟩ ⟩
```
 ## Adding Zero 
```lean
theorem sum_zero_left {a : DCut} : 0 + a = a := by
  ext c
  simp[hadd_inst,sum,zero_inst]
  constructor
  . intro ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, h ⟩ ⟩ ⟩ ⟩
    have : x < 0 := hx
    apply a.dc c y
    apply And.intro
    . linarith
    . exact hy
  . intro h
    obtain ⟨ x, ⟨ hx1, hx2 ⟩ ⟩ := a.op c h
    have h1 : c-x < 0 := by linarith
    exact ⟨ c-x, ⟨ h1, ⟨ x, ⟨ hx1, by linarith ⟩ ⟩ ⟩ ⟩

theorem sum_zero_right {a : DCut} : a + 0 = a := by
  rw[sum_comm,sum_zero_left]

instance add_zero_inst : AddZeroClass DCut :=
  ⟨ @sum_zero_left, @sum_zero_right ⟩
```
 ## Subtraction 
```lean
def preneg (c : DCut) : Set ℚ := { x | ∃ a < 0, ∃ b ∉ c.A, x = a-b }

theorem preneg_rat {p : ℚ} : preneg (ofRat p) = (ofRat (-p)).A := by
  simp[preneg,ofRat,odown]
  ext q
  constructor
  . simp_all
    intro a ha x hx hq
    linarith
  . simp_all
    intro hq
    exact ⟨ q+p, ⟨ by linarith, ⟨ p, ⟨ by linarith, by linarith ⟩ ⟩ ⟩ ⟩

theorem predeg_ne {c : DCut} : ∃ q, q ∈ preneg c := by
  simp[preneg]
  have ⟨ q, hq ⟩ := c.nf
  use -q-2
  have h1 : q + 1 ∉ c.A := by
    apply not_in_a_gt hq
    linarith
  exact  ⟨ -1, ⟨ by linarith, ⟨ q+1, ⟨ h1, by linarith ⟩ ⟩ ⟩ ⟩

theorem predeg_nf {c : DCut} : ∃ q, q ∉ preneg c := by
  simp[preneg]
  have ⟨ q, hq ⟩ := c.ne
  use -q
  intro x hx y hy h
  have h2 : y ≤ q := by linarith
  have h3 : q ∉ c.A := by
    intro h1
    exact not_in_a_gt hy h2 hq
  exact h3 hq

theorem predeg_dc {c : DCut}
  : ∀ (x y : ℚ), x ≤ y ∧ y ∈ preneg c → x ∈ preneg c := by
  intro x y ⟨ hxy, ⟨ a, ⟨ ha, ⟨ b, ⟨ hb, h ⟩ ⟩ ⟩ ⟩ ⟩
  exact ⟨ a - (y-x), ⟨ by linarith, ⟨ b, ⟨ hb, by linarith ⟩ ⟩ ⟩ ⟩

theorem predeg_op {c : DCut}
  : ∀ x ∈ preneg c, ∃ y ∈ preneg c, x < y := by
  simp[preneg]
  intro q x hx y hy hxy
  have := c.op
  use q-x/2
  apply And.intro
  . simp[hxy]
    exact ⟨ x/2, ⟨ by linarith, ⟨ y, ⟨ hy, by linarith ⟩ ⟩ ⟩ ⟩
  . linarith

def neg (c : DCut) : DCut :=
  ⟨ preneg c, predeg_ne, predeg_nf, predeg_dc, predeg_op ⟩

instance neg_inst : Neg DCut := ⟨ neg ⟩

theorem neg_rat {p : ℚ} : -ofRat p = ofRat (-p) := by
  simp[neg_inst,neg]
  apply DCut.ext
  simp
  rw[preneg_rat]
```
 ## Negation 
```lean
def sub (a b : DCut) : DCut := a + (-b)

instance hsub_inst : HSub DCut DCut DCut := ⟨ sub ⟩

instance sub_inst : Sub DCut := ⟨ sub ⟩

theorem add_neg (a b : DCut) : a + -b = a - b := by
  simp[hsub_inst,sub]
```
 Let's check this definition works for rationals. The forward direction is easy. For the reverse direction, we are given q < 0. We need to choose x and y so that

  - x < 1
  - y < -1
  - x + y = q

Since q < 0, we know q-1 < -1. For y, we take the point halfway between q-1 and -1, which is y = ((q-1) + (-1))/2 = (q-2)/2.

Then x = q-y = (q+2)/2 will work as long as x < 1. We have

```
  q < 0
  q+2 < 2
  (q+2)/2 < 1
```

If -1 ≥ q, the situation looks like this

```
 ((-∞    q-1    y    -1]     q    0     x    1]
```

If q < -1, the situation looks like this

```
 ((-∞    q-1  q     y      -1]    0     x    1]
         -4  -3            -1
                  -5/2                -1/2
```
or
```
((-∞    q-1    y      q      -1]    0     x    1]
        -2           -1      -1
             -3/2
```


```lean
example : ofRat 1 - ofRat 1 = ofRat 0 := by
  simp[hsub_inst,sub,neg_rat]
  ext q
  simp[hadd_inst,sum,ofRat,presum,odown]
  constructor
  . intro ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, h ⟩ ⟩ ⟩ ⟩
    linarith
  . intro hq
    exact ⟨ (q+2)/2, ⟨ by linarith, ⟨ (q-2)/2, ⟨ by linarith, by linarith ⟩ ⟩ ⟩ ⟩

theorem cut_element (c : DCut) (s t : ℚ) (hs : s < 0)
  : ∃ n : ℕ, t + n * s ∈ c.A := by
  obtain ⟨q, hq⟩ := c.ne
  let n := ⌈(q-t)/s⌉₊
  use n
  have hdiv : (q-t)/s ≤ n := Nat.le_ceil ((q - t) / s)
  have hcalc : t + n * s ≤ q := by
    have : (q-t) ≥ n * s := (div_le_iff_of_neg hs).mp hdiv
    simp_all
    linarith
  exact c.dc _ q ⟨hcalc, hq⟩

def Svals (c : DCut) (s t : ℚ) : Set ℕ := {n : ℕ | t + n * s ∈ c.A}

noncomputable
instance s_dec {c : DCut} {s t : ℚ}  : DecidablePred (· ∈ Svals c s t) := by
    intro n
    apply Classical.propDecidable

theorem min_element (S : Set ℕ) [DecidablePred (· ∈ S)] (h : ∃ x, x ∈ S)
  : ∃ m, m ∈ S ∧ (∀ k < m, k ∉ S) := by
  have hsne : S.Nonempty := h
  let m := Nat.find hsne
  have hm : m ∈ S := Nat.find_spec hsne
  have hm_min : ∀ k < m, k ∉ S := λ k => Nat.find_min hsne
  exact ⟨ m, hm, hm_min ⟩

theorem archimedean {c : DCut} {s t : ℚ} (ht : t ∉ c.A) (hs : s < 0)
  : ∃ n : ℤ, t+n*s ∉ c.A ∧ t+(n+1)*s ∈ c.A := by

  let S := Svals c s t
  have ⟨ m, hm, hm_min ⟩ := min_element S (cut_element c s t hs)

  by_cases h : m = 0

  · simp [h, S, Svals] at hm
    contradiction

  · use m - 1
    have hm' : m > 0 := Nat.zero_lt_of_ne_zero h

    apply And.intro
    · have := hm_min (m-1) (Nat.sub_one_lt_of_lt hm')
      simp_all[S,Svals]
    · simp
      assumption
```

These don't work directly because of the edge case where c is a principal cut
      -c.A                 b        c.A   -a
        )    q    0    t + (n+1)q    )   t + nq
       -2   -1         4-3=1         2   4-2=2


But we can find z greater than t + (n+1)q and which is still in c.A
        )    q    0    t + (n+1)q     )   t + nq
                                   ∧
                                   z

And then take ε = z - (t + (n+1)q) to get
  a            -c.A                b         c.A
 -t - nq - ε     )    q    0    t + (n+1)q+ε  )   t + nq + ε
 -2.5           -2   -1         1.5           2   2.5

 
```lean
theorem neg_add_cancel_right {c : DCut} : c - c = 0 := by

  ext q
  constructor

  . simp[hsub_inst,neg_inst,neg,sub,hadd_inst,sum,preneg]
    intro ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, hxy ⟩ ⟩ ⟩ ⟩
    obtain ⟨ a, ⟨ ha, ⟨ b, ⟨ hb, hab ⟩ ⟩ ⟩ ⟩ := hy
    have h1 : q ∈ A 0 ↔ q < 0 := Set.mem_def
    simp[h1]
    have h2 := a_lt_b hx hb
    linarith

  . intro hq
    have hq : q < 0 := hq
    obtain ⟨ t, ht ⟩ := c.nf
    obtain ⟨ n, ⟨ hn1, hn2 ⟩ ⟩ := archimedean ht hq

    let b' := t + (n+1)*q
    let a' := -n*q-t

    obtain ⟨ z, ⟨ hz, hbz ⟩ ⟩ := c.op b' hn2
    let ε := z - b'
    have hε : 0 < ε := by simp[ε]; linarith

    let b := z
    let a := -n*q-t-ε

    have hab : z+a = q := by
      simp[a,a',b,b',ε]
      linarith

    have ha : a ∈ (-c).A := by
      use -ε
      apply And.intro
      . linarith
      . use -a-ε
        apply And.intro
        . simp[a]
          exact hn1
        . linarith

    exact ⟨ z, ⟨ hz, ⟨ a, ⟨ ha, hab ⟩ ⟩ ⟩ ⟩

theorem neg_add_cancel_left {c : DCut} : -c + c = 0 := by
 rw[sum_comm,add_neg,neg_add_cancel_right]
```

<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
