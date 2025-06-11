
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Reals/Multiply.lean'>Code</a> for this chapter</span>
 # Multiplication

Multiplication of Dedekind cuts is straightfoward, but also fairly involved, or as Rudin says: "bothersome". The issue is dealing with both positive and negative cuts. Following Rudin, the development of the definitions proceeds as follows:

- Define multiplication on positive cuts.
- Extend multiplciation on positive cuts to non-negative cuts, building on the previous step by handling the cases in which either or both of the cuts is zero.
- Extend multiplication on non-negative cuts to all cuts.

For each of the above definitions of multiplication, we also prove the properties required to show that multiplication forms a commutiative group on cuts:
- 0 is an identity: `0*x = 0`
- Multiplication is commutative: `x*y = y*x`
- Associativity: `x*(y*z) = (x*y)*z`
The last property is particularly challenging, because to relate arbitary reals with positive reals, one has to deal with an abundance of cases, preferably gracefully. Thus, along the way we will prove several intermediate results which allow us to make the proof more concise.


 ## Definitions

### Multiplication of Positive Cuts

Given two positive cuts `0 < a` and `0 < b`, their product is the set of points `z` such that for some `x ∈ a` and `y ∈ b`, `z < x*y`. This basic definition underlies the entire framework for multiplication, after which we simply have to deal with various combinations of non-negative and negative numbers. 
```lean
def pre_mul (a b : DCut) :=
  { z | ∃ x ∈ a.A, ∃ y ∈ b.A, 0 < x ∧ 0 < y ∧ z < x*y }
```
 To prove that this definition results in a cut, we need to prove as usual that it is non-empty, not equal to ℚ, downward closed, and open.  
```lean
theorem pre_mul_ne {a b : DCut} (ha : 0 < a) (hb : 0 < b) : ∃ q, q ∈ pre_mul a b := by

  have ⟨ x, ⟨ hx1, hx2 ⟩ ⟩ := a.op 0 (zero_in_pos ha)
  have ⟨ y, ⟨ hy1, hy2 ⟩ ⟩ := b.op 0 (zero_in_pos hb)
  have hxy : 0 < x * y := Left.mul_pos hx2 hy2
  use -1, x, hx1, y, hy1, hx2, hy2
  exact gt_of_gt_of_ge hxy rfl

theorem pre_mul_nf {a b : DCut} (ha : 0 < a) (_ : 0 < b)
  : ∃ q, q ∉ pre_mul a b := by

  obtain ⟨ x, hx ⟩ := a.nf
  obtain ⟨ y, hy ⟩ := b.nf
  use x*y

  have hxpos : 0 < x := a_lt_b (zero_in_pos ha) hx
  have hx' : ∀ q ∈ a.A, q < x := by intro q hq; exact a_lt_b hq hx
  have hy' : ∀ q ∈ b.A, q < y := by intro q hq; exact a_lt_b hq hy

  simp[pre_mul]
  intro s hs t ht hsp htp
  apply @_root_.le_of_lt
  exact mul_lt_mul_of_pos' (hx' s hs) (hy' t ht) htp hxpos

theorem pre_mul_dc {a b : DCut} : ∀ x y, x ≤ y ∧ y ∈ (pre_mul a b) → x ∈ (pre_mul a b) := by
  intro x y ⟨ hxy, hy ⟩
  obtain ⟨ s, ⟨ hs, ⟨ t, ⟨ ht, ⟨ hsp, ⟨ htp, hyst ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ := hy
  exact ⟨ s, ⟨ hs, ⟨ t, ⟨ ht, ⟨ hsp, ⟨ htp, lt_of_le_of_lt hxy hyst ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

theorem pre_mul_op {a b : DCut} : ∀ x ∈ (pre_mul a b), ∃ y ∈ (pre_mul a b), x < y := by
  intro x ⟨ s, ⟨ hs, ⟨ t, ⟨ ht, ⟨ hsp, ⟨ htp, hyst ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  have ⟨ s', ⟨ hs', hss' ⟩ ⟩ := a.op s hs
  have ⟨ t', ⟨ ht', htt' ⟩ ⟩ := b.op t ht
  have h: s*t < s'*t' := mul_lt_mul_of_pos' hss' htt' htp (by linarith)
  use s*t
  apply And.intro
  . exact ⟨ s', ⟨ hs', ⟨ t', ⟨ ht', ⟨ by linarith, ⟨ by linarith, h ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  . linarith
```
 Grouping these properties together we get: 
```lean
def mul_pos (a b : DCut) (ha : 0 < a) (hb : 0 < b) : DCut :=
  ⟨ pre_mul a b, pre_mul_ne ha hb, pre_mul_nf ha hb, pre_mul_dc, pre_mul_op ⟩
```
 We will need the following property to extend multiplication from positive numbers to non-negative numbers stating that the product of two positive numbers is again positive. Thus, the definition `pre_mul` operates exclusively on the positive reals. 
```lean
theorem mul_is_pos {a b : DCut} (ha : 0 < a) (hb : 0 < b) : 0 < mul_pos a b ha hb := by
  simp[lt_inst,mul_pos,DCut.ext_iff]
  have ⟨ x, ⟨ hx1, hx2 ⟩ ⟩ := non_neg_in_pos ha
  have ⟨ y, ⟨ hy1, hy2 ⟩ ⟩ := non_neg_in_pos hb
  apply And.intro
  . intro h
    simp[Set.Subset.antisymm_iff] at h
    have ⟨ h1, h2 ⟩ := h
    simp[pre_mul,zero_rw,odown] at h2
    have := h2 0 x hx1 y hy1 hx2 hy2 (Left.mul_pos hx2 hy2)
    simp_all
  . simp[pre_mul,zero_rw,odown]
    intro q hq
    have : q < x*y := gt_trans (Left.mul_pos hx2 hy2) hq
    exact ⟨ x, ⟨ hx1, ⟨ y, ⟨ hy1, ⟨ hx2, ⟨ hy2, this ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
```
 ### Multiplication on Non-negative Cuts

We now extend the definition to non-negative reals, essentially dealing with the cases in which either cut is zero, in which case the resulting product is zero. Indeed, if one of `a` and `b` is zero, then `pre_mul a b = ∅`. 
```lean
@[simp]
theorem zero_mul_empty {a b : DCut} (h : 0 = a ∨ 0 = b) : pre_mul a b = ∅ := by
  apply Or.elim h
  repeat
  . intro h'
    simp[DCut.ext_iff,zero_rw] at h'
    simp[pre_mul,←h',odown]
    ext q
    simp
    intro x hx y hy h1 h2
    linarith
```
 Since `∅` is not a valid cut, we use `pre_mul a b ∪ odown 0` to represent the product of two non-negative cuts. The remaining theorems are required to show that the result is a cut. We simply, and laboriously, have to deal with the possible cases. 
```lean
theorem mul_nneg_ne {a b : DCut}
  : ∃ q, q ∈ pre_mul a b ∪ odown 0 := by
  use -1
  apply Or.inr
  simp[odown]

theorem mul_nneg_nf {a b : DCut} (ha : 0 ≤ a) (hb : 0 ≤ b)
  : ∃ q, q ∉ pre_mul a b ∪ odown 0 := by
  by_cases h0 : 0 < a ∧ 0 < b
  . have ⟨ q, hq ⟩ := pre_mul_nf h0.left h0.right
    use q
    intro h1
    simp_all
    exact hq ((mul_is_pos h0.left h0.right).right h1)
  . have hab : 0 = a ∨ 0 = b := by
      simp_all[lt_of_le]
      exact Or.symm (or_iff_not_imp_right.mpr h0)
    simp[hab,odown]
    exact ⟨ 1, rfl ⟩

theorem mul_nneg_dc {a b : DCut} {x y : ℚ}
  : x ≤ y ∧ y ∈ pre_mul a b ∪ odown 0 → x ∈ pre_mul a b ∪ odown 0 := by
  intro ⟨ h1, h2 ⟩
  apply Or.elim h2
  . intro hy
    exact Or.inl (pre_mul_dc x y ⟨ h1, hy ⟩)
  . intro hy
    apply Or.inr
    simp_all[odown]
    linarith

theorem mul_nneg_op {a b : DCut} (x : ℚ) :
  x ∈ pre_mul a b ∪ odown 0 → ∃ y ∈ pre_mul a b ∪ odown 0, x < y := by
  intro h
  apply Or.elim h
  . intro hx
    have ⟨ q, ⟨ hq1, hq2 ⟩ ⟩ := pre_mul_op x hx
    exact ⟨ q, ⟨ Or.inl hq1, hq2 ⟩  ⟩
  . intro hx
    simp[odown] at hx ⊢
    exact ⟨ x/2, ⟨ by apply Or.inr; linarith, by linarith ⟩ ⟩

def mul_nneg (a b : DCut) (ha : 0 ≤ a) (hb : 0 ≤ b) : DCut :=
  ⟨ pre_mul a b ∪ odown 0,
    mul_nneg_ne,
    mul_nneg_nf ha hb,
    @mul_nneg_dc a b,
    @mul_nneg_op a b ⟩
```
 ### Mulitiplication on Arbitrary Cuts

Finally, we extend multiiplcation to arbitrary cuts. This step uses the fact that every cut `a` can be written as the difference `max 0 a - max 0 (-a)`. If `0 ≤ a` then
```hs
max 0 a - max 0 (-a) = a + 0
```
and if `a < 0` then
```hs
max 0 a - max 0 (-a) = 0 + -a
```
both of which are non-negative, and we can therefore use the previous definition of multiplication on non-negative cuts.

```lean
def mul (a b : DCut) : DCut :=
  let ap := maximum 0 a
  let an := maximum 0 (-a)
  let bp := maximum 0 b
  let bn := maximum 0 (-b)
  (mul_nneg ap bp (max_gz _) (max_gz _)) +
  (mul_nneg an bn (max_gz _) (max_gz _)) -
  (mul_nneg ap bn (max_gz _) (max_gz _)) -
  (mul_nneg an bp (max_gz _) (max_gz _))
```
 We may now instantiate the notation classes for multiplcation. 
```lean
instance hmul_inst : HMul DCut DCut DCut := ⟨ mul ⟩
instance mul_inst : Mul DCut := ⟨ mul ⟩

example : (1:DCut) * 0 = 0 := by
  simp[hmul_inst,mul]
```
 ## Multiplication by 0

For non-negative cuts, it is useful to know that `0*a = 0` and `a*0 = 0`, as these properties allow us to reason about the zero cases in the non-negative commutativity proof. These properties also allow us to show that `0` is the multiplicative identity, which is needed for proving cuts with multiplication form a group. 
```lean
@[simp]
theorem mul_nneg_zero_left {a : DCut} (ha: 0 ≤ a)
  : mul_nneg 0 a (λ _ a => a) ha = 0 := by
  simp[mul_nneg,DCut.ext_iff,pre_mul,zero_rw]
  intro q hq
  simp_all[odown]
  obtain ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, h ⟩ ⟩ ⟩ ⟩ := hq
  linarith

@[simp]
theorem mul_nneg_zero_right {a : DCut} (ha: 0 ≤ a)
  : mul_nneg a 0 ha (λ _ a => a) = 0 := by
  simp[mul_nneg,DCut.ext_iff,pre_mul,zero_rw]
  intro q hq
  simp_all[odown]
  obtain ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, h ⟩ ⟩ ⟩ ⟩ := hq
  linarith
```
 These two theorems allow us to prove that the multiple of two non-negative cuts is again non-negative. 
```lean
@[simp]
theorem mul_is_nneg {a b : DCut} (ha : 0 ≤ a) (hb : 0 ≤ b)
  : 0 ≤ mul_nneg a b ha hb := by
  by_cases h : 0 < a ∧ 0 < b
  . have := mul_is_pos h.left h.right
    simp[lt_inst,mul_pos] at this
    have ⟨ h1, h2 ⟩ := this
    simp[le_inst,mul_nneg]
    exact Set.subset_union_right
  . by_cases hb0 : 0 = a
    . simp[←hb0]
    . simp_all[lt_of_le]
      simp[←h]
```
 We can extend these properties to arbitrary reals. 
```lean
@[simp]
theorem mul_zero_left {a : DCut} : 0 * a = 0 := by
  simp[hmul_inst,mul]

@[simp]
theorem mul_zero_right {a : DCut} : a * 0 = 0 := by
  simp[hmul_inst,mul]
```
 ## Multiplication by 1 
```lean
@[simp]
theorem mul_pos_id_left {a : DCut} (ha: 0 < a)
  : mul_pos 1 a zero_lt_one ha = a := by
  simp[DCut.ext_iff,mul_pos,pre_mul,one_rw,odown]
  ext q
  constructor
  . intro ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, ⟨ hx0, ⟨ hy0, hqxy ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    have hxy : x*y < y := mul_lt_of_lt_one_left hy0 hx
    have hxy' := a.dc (x*y) y ⟨ by linarith, hy ⟩
    exact a.dc q (x*y) ⟨ by linarith, hxy' ⟩
  . intro hq
    by_cases h : 0 < q
    . have ⟨s, ⟨ hs1, hs2 ⟩ ⟩ := a.op q hq
      have ⟨t, ⟨ ht1, ht2 ⟩ ⟩ := a.op s hs1
      use q/s
      have hs3 : 0 < s := by linarith
      apply And.intro
      . exact Bound.div_lt_one_of_pos_of_lt hs3 hs2
      . use t
        have hts : t/s > 1 := (one_lt_div hs3).mpr ht2
        have h1 : q*(t/s) > q := (lt_mul_iff_one_lt_right h).mpr hts
        have h2 : q*(t/s) = q / s * t := Eq.symm (mul_comm_div q s t)
        exact ⟨ ht1, ⟨ div_pos h hs3, ⟨ by linarith, by linarith ⟩ ⟩ ⟩
    . have ⟨s, ⟨ hs1, hs2 ⟩ ⟩ := a.op 0 (zero_in_pos ha)
      use 1/2
      apply And.intro
      . linarith
      . exact ⟨ s, ⟨ hs1, ⟨ by linarith, ⟨ hs2, by linarith ⟩ ⟩ ⟩ ⟩

@[simp]
theorem mul_nneg_id_left {a : DCut} (ha: 0 ≤ a)
  : mul_nneg 1 a zero_le_one ha = a := by
    rw[le_of_lt] at ha
    apply Or.elim ha
    intro ha0
    . simp[←ha0]
    . intro ha'
      have := mul_pos_id_left ha'
      simp_all[mul_pos,DCut.ext_iff,mul_nneg,DCut.ext_iff]
      exact ha
```
 ## Commutativity

For positive cuts, commutativity is straightfoward, as it simply amounts to reordering x and y in the definition of `pre_mul`. 
```lean
theorem mul_pos_comm {a b : DCut} (ha : 0 < a) (hb : 0 < b)
  : mul_pos a b ha hb = mul_pos b a hb ha  := by
  ext q
  constructor
  repeat
  . intro ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, ⟨ h1, ⟨ h2, h3 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    exact ⟨ y, ⟨ hy, ⟨ x, ⟨ hx, ⟨ h2, ⟨ h1, by linarith ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
```
 Proving commutativity for non-negative cuts amounts to three cases, where `a` and `b` are both positive and where one or the other is negative. 
```lean
theorem mul_nneg_comm {a b : DCut} (ha : 0 ≤ a) (hb : 0 ≤ b)
  : mul_nneg a b ha hb = mul_nneg b a hb ha := by
  by_cases h : 0 < a ∧ 0 < b
  . simp[mul_nneg]
    have := mul_pos_comm h.left h.right
    simp_all[mul_pos]
  . simp[lt_of_le] at h
    by_cases hb0 : 0 = b
    . simp[←hb0]
    . simp_all
      simp[←h]
```
 The proof of commutativity for arbitrary cuts requires us to reason about every possible combination of non-negative and negative cuts. We do this with the theorem `two_ineqs_true` which enuerates all four cases. For each case, the same (somewhat massive) simplificiation works. 
```lean
theorem mul_comm {a b : DCut}: a*b = b*a := by
  rcases two_ineqs a b with ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩
  repeat
  simp[ha,hb,hmul_inst,mul,mul_nneg_comm,neg_le.mp]
```
 Commutativity makes it easy to prove similar versions of theorems for which the one side has already been established. For example: 
```lean
@[simp]
theorem mul_nneg_id_right {a : DCut} (ha: 0 ≤ a)
  : mul_nneg a 1 ha zero_le_one = a := by
  rw[mul_nneg_comm,mul_nneg_id_left]
```
 And similarly, 
```lean
@[simp]
theorem mul_id_right {a : DCut} : a * 1 = a := by
  simp only[hmul_inst,mul]
  by_cases ha : 0 < a
  . simp[ha]
  . simp
    rw[not_gt_to_le] at ha
    simp[ha]

@[simp]
theorem mul_id_left {a : DCut} : 1 * a = a := by
  simp[mul_comm]
```
 ## Associativity 
```lean
theorem mul_pos_assoc {a b c : DCut} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  : mul_pos a (mul_pos b c hb hc) ha (mul_is_pos hb hc) =
    mul_pos (mul_pos a b ha hb) c (mul_is_pos ha hb) hc  := by

  ext q
  constructor

  . intro ⟨ x, ⟨ hx, ⟨ yz, ⟨ ⟨ y, ⟨ hy, ⟨ z, ⟨ hz, ⟨ hy0, ⟨ hz0, h3 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩, ⟨ hx0, ⟨ hyz0, h2 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    have hxyz' : x * yz < x * (y*z) := by exact (mul_lt_mul_left hx0).mpr h3 -- helps linarith
    have ⟨ x', ⟨ hx', hxx' ⟩  ⟩ := a.op x hx
    have h : x * y < x' * y := by exact (mul_lt_mul_iff_of_pos_right hy0).mpr hxx'
    exact ⟨ x*y, ⟨ ⟨ x', ⟨ hx', ⟨ y, ⟨ hy, ⟨ by linarith, ⟨ hy0,h ⟩ ⟩ ⟩ ⟩ ⟩ ⟩, ⟨ z, ⟨ hz, ⟨ Left.mul_pos hx0 hy0, ⟨ hz0, by linarith ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

  . rintro ⟨ xy, ⟨ x, hx, y, hy, hx0, hy0, hxy ⟩, z, hz, hxy', hz0, hxyz ⟩
    have ⟨ z', ⟨ hz', hzz' ⟩ ⟩ := c.op z hz
    have hxyz' : xy * z < (x * y) * z := by exact (mul_lt_mul_iff_of_pos_right hz0).mpr hxy
    have hxy0 : 0 < y * z := by exact Left.mul_pos hy0 hz0
    have : y * z < y * z' := by exact (mul_lt_mul_left hy0).mpr hzz'
    exact ⟨ x, ⟨ hx, ⟨ y*z, ⟨ ⟨ y, ⟨ hy, ⟨ z', ⟨ hz', ⟨ hy0, ⟨ by linarith, this ⟩ ⟩ ⟩ ⟩ ⟩ ⟩, ⟨ hx0, ⟨ hxy0, by linarith ⟩  ⟩ ⟩ ⟩ ⟩  ⟩

@[simp]
theorem pre_mul_with_pos {a b : DCut} (ha : 0 < a) (hb : 0 < b)
  : pre_mul a b ∪ odown 0 = pre_mul a b := by
    have := mul_is_pos ha hb
    simp_all[mul_pos,lt_inst,zero_rw]

@[simp]
theorem mul_nneg_assoc {a b c : DCut} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
  : mul_nneg a (mul_nneg b c hb hc) ha (mul_is_nneg hb hc) =
    mul_nneg (mul_nneg a b ha hb) c (mul_is_nneg ha hb) hc := by

  by_cases h : 0 < a ∧ 0 < b ∧ 0 < c
  . have h1 := mul_pos_assoc h.left h.right.left h.right.right
    simp[mul_pos] at h1
    simp[mul_nneg,h1,h]

  by_cases h1 : 0 = a
  . simp[←h1]
  by_cases h2 : 0 = b
  . simp[←h2]
  by_cases h3 : 0 = c
  . simp[←h3]

  simp_all[lt_of_le]
```

When a ≤ 0 while 0 ≤ b and 0 ≤ c then
```hs
(a*b)*c = a*(b*c)
```
becomes
```hs
-((-a)*b)*c = -((-a)*(b*c))
```
and then use mul_assoc_all_nn. Similarly, we can do all the other cases this way.

```lean
@[simp]
theorem mul_neg_dist_left {a b : DCut} : a*(-b) = -(a*b) := by
  simp[hmul_inst,mul]
  rcases two_ineqs a b with ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩
  repeat
  simp[ha,hb,neg_le.mp]

@[simp]
theorem mul_neg_dist_right {a b : DCut} : (-a)*b = -(a*b) := by
  simp only[hmul_inst,mul]
  rcases two_ineqs a b with ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩
  repeat
  simp[ha,hb,neg_le.mp]

theorem mul_assoc_all_nn {a b c : DCut} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
  : a * (b * c) = (a * b) * c := by
  simp[hmul_inst,mul]
  simp[ha,hb,hc,neg_le.mp] -- uses mul_nneg_assoc

theorem flip {a : DCut} (ha: a < 0) : 0 ≤ -a := neg_le'.mp (lt_imp_le ha)

theorem mul_assoc {a b c : DCut} : a * (b * c) = (a * b) * c := by
  rcases three_ineqs a b c with ⟨ ha, hb, hc ⟩ | ⟨ ha, hb, hc ⟩ |
                                ⟨ ha, hb, hc ⟩ | ⟨ ha, hb, hc ⟩ |
                                ⟨ ha, hb, hc ⟩ | ⟨ ha, hb, hc ⟩ |
                                ⟨ ha, hb, hc ⟩ | ⟨ ha, hb, hc ⟩
  . exact mul_assoc_all_nn ha hb hc
  . simpa using mul_assoc_all_nn (flip ha) hb hc
  . simpa using mul_assoc_all_nn ha (flip hb) hc
  . simpa using mul_assoc_all_nn ha hb (flip hc)
  . simpa using mul_assoc_all_nn (flip ha) (flip hb) hc
  . simpa using mul_assoc_all_nn (flip ha) hb (flip hc)
  . simpa using mul_assoc_all_nn ha (flip hb) (flip hc)
  . simpa using mul_assoc_all_nn (flip ha) (flip hb) (flip hc)
```
 ## Instantiating Multiplication Classes 
```lean
instance mul_zero_inst : MulZeroClass DCut := ⟨
    @mul_zero_left,
    @mul_zero_right
  ⟩

instance mul_one_inst : MulOneClass DCut := ⟨
  @mul_id_left,
  @mul_id_right
⟩

instance semigroup_inst : Semigroup DCut := ⟨
  λ x y z => Eq.symm (@mul_assoc x y z)
⟩

instance semigroup_w_zero_inst : SemigroupWithZero DCut := ⟨ -- is this auotgenerated?
  @mul_zero_left,
  @mul_zero_right
⟩

instance mul_zo_inst : MulZeroOneClass DCut := ⟨  -- is this auotgenerated?
  @mul_zero_left,
  @mul_zero_right
⟩

instance comm_magma_inst : CommMagma DCut := ⟨ @mul_comm ⟩

instance comm_semigroup_inst : CommSemigroup DCut := ⟨ @mul_comm ⟩

example {x y z :DCut} : (x+y)*z = z*(y+x) := by
  rw[@_root_.mul_comm] -- This is mathlib's CommMagma mul_com
  abel_nf
```
 ## Natural Powers and Monoid Instance 
```lean
def npow (n: ℕ) (x : DCut) : DCut := match n with
  | Nat.zero => 1
  | Nat.succ k => x * (npow k x)

theorem npow_zero {x : DCut} : npow 0 x = 1 := by rfl

theorem npow_succ {n : ℕ} {x : DCut} : npow (n+1) x = npow n x * x := by
  simp[npow,mul_comm]

instance monoid_inst : Monoid DCut := ⟨
  @mul_id_left,
  @mul_id_right, -- why does this need to be here if this is already a MulOneClass?
  npow,
  @npow_zero,
  @npow_succ
⟩

instance com_monoid_inst : CommMonoid DCut := ⟨
  @mul_comm
⟩

instance monoid_wz_inst : MonoidWithZero DCut := ⟨
  @mul_zero_left,
  @mul_zero_right
⟩

instance comm_monoid_wz_inst : CommMonoidWithZero DCut := ⟨
  @mul_zero_left,
  @mul_zero_right
⟩


example (x : DCut) : x^2 = x*x := by
  exact pow_two x --> pow_two is a theorem about monoids from Mathlib
```

<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
