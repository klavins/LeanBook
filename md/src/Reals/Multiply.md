
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
 ## Multiplication of Positive Reals 
```lean
def pre_mul (a b : DCut) :=
  { z | ∃ x ∈ a.A, ∃ y ∈ b.A, 0 < x ∧ 0 < y ∧ z < x*y } -- Rudin's definition

theorem pre_mul_ne {a b : DCut} (ha : 0 < a) (hb : 0 < b) : ∃ q, q ∈ pre_mul a b := by

  have ⟨ x, ⟨ hx1, hx2 ⟩ ⟩ := a.op 0 (zero_in_pos ha)
  have ⟨ y, ⟨ hy1, hy2 ⟩ ⟩ := b.op 0 (zero_in_pos hb)
  have hxy : 0 < x * y := Left.mul_pos hx2 hy2
  use -1
  exact ⟨ x, ⟨ hx1, ⟨ y, ⟨ hy1, ⟨ hx2, ⟨ hy2, gt_of_gt_of_ge hxy rfl ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

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
  intro x hx
  obtain ⟨ s, ⟨ hs, ⟨ t, ⟨ ht, ⟨ hsp, ⟨ htp, hyst ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ := hx
  have ⟨ s', ⟨ hs', hss' ⟩ ⟩ := a.op s hs
  have ⟨ t', ⟨ ht', htt' ⟩ ⟩ := b.op t ht
  have h: s*t < s'*t' := mul_lt_mul_of_pos' hss' htt' htp (by linarith)
  use s*t
  apply And.intro
  . exact ⟨ s', ⟨ hs', ⟨ t', ⟨ ht', ⟨ by linarith, ⟨ by linarith, h ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  . linarith

def mul_pos (a b : DCut) (ha : 0 < a) (hb : 0 < b) : DCut :=
  ⟨ pre_mul a b, pre_mul_ne ha hb, pre_mul_nf ha hb, pre_mul_dc, pre_mul_op ⟩
```
 ## Properties 
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

theorem mul_pos_id_left {a : DCut} (ha: 0 < a)
  : mul_pos 1 a zero_lt_one ha = a := by
  simp[DCut.ext_iff,mul_pos,pre_mul,one_rw,odown]
  ext q
  simp
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
    . -- case q ≤ 0
      have := zero_in_pos ha
      have ⟨s, ⟨ hs1, hs2 ⟩ ⟩ := a.op 0 this
      use 1/2
      apply And.intro
      . linarith
      . use s
        exact ⟨ hs1, ⟨ by linarith, ⟨ hs2, by linarith ⟩ ⟩ ⟩

theorem mul_pos_comm {a b : DCut} (ha : 0 < a) (hb : 0 < b)
  : mul_pos a b ha hb = mul_pos b a hb ha  := by
  ext q
  constructor
  repeat
  . intro ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, ⟨ h1, ⟨ h2, h3 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    exact ⟨ y, ⟨ hy, ⟨ x, ⟨ hx, ⟨ h2, ⟨ h1, by linarith ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

theorem mul_pos_assoc {a b c : DCut} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  : mul_pos a (mul_pos b c hb hc) ha (mul_is_pos hb hc) =
    mul_pos (mul_pos a b ha hb) c (mul_is_pos ha hb) hc  := by

  simp[mul_pos,pre_mul]
  ext q
  simp
  constructor

  . intro ⟨ x, ⟨ hx, ⟨ yz, ⟨ ⟨ y, ⟨ hy, ⟨ z, ⟨ hz, ⟨ hy0, ⟨ hz0, h3 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩, ⟨ hx0, ⟨ hyz0, h2 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    have hxyz' : x * yz < x * (y*z) := by exact (mul_lt_mul_left hx0).mpr h3
    have ⟨ x', ⟨ hx', hxx' ⟩  ⟩ := a.op x hx
    have h : x * y < x' * y := by exact (mul_lt_mul_iff_of_pos_right hy0).mpr hxx'
    exact ⟨ x*y, ⟨ ⟨ x', ⟨ hx', ⟨ y, ⟨ hy, ⟨ by linarith, ⟨ hy0,h ⟩ ⟩ ⟩ ⟩ ⟩ ⟩, ⟨ z, ⟨ hz, ⟨ Left.mul_pos hx0 hy0, ⟨ hz0, by linarith ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

  . rintro ⟨ xy, ⟨ x, hx, y, hy, hx0, hy0, hxy ⟩, z, hz, hxy', hz0, hxyz ⟩
    have ⟨ z', ⟨ hz', hzz' ⟩ ⟩ := c.op z hz
    have hxyz' : xy * z < (x * y) * z := by exact (mul_lt_mul_iff_of_pos_right hz0).mpr hxy
    have hxy0 : 0 < y * z := by exact Left.mul_pos hy0 hz0
    have hqxyz : q < x * (y * z) := by linarith
    have : y * z < y * z' := by exact (mul_lt_mul_left hy0).mpr hzz'
    exact ⟨ x, ⟨ hx, ⟨ y*z, ⟨ ⟨ y, ⟨ hy, ⟨ z', ⟨ hz', ⟨ hy0, ⟨ by linarith, this ⟩ ⟩ ⟩ ⟩ ⟩ ⟩, ⟨ hx0, ⟨ hxy0, hqxyz ⟩  ⟩ ⟩ ⟩ ⟩  ⟩
```
 ## Mulitiplication of Non-negative Reals 
```lean
theorem zero_mul_empty (a b : DCut) (h : 0 = a ∨ 0 = b) : pre_mul a b = ∅ := by
  apply Or.elim h
  repeat
  . intro h'
    simp[DCut.ext_iff,zero_rw] at h'
    simp[pre_mul,←h',odown]
    ext q
    simp
    intro x hx y hy h1 h2
    linarith

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
    have := zero_mul_empty a b hab
    simp[this,odown]
    use 1
    exact rfl

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

theorem mul_nneg_comm {a b : DCut} (ha : 0 ≤ a) (hb : 0 ≤ b)
  : mul_nneg a b ha hb = mul_nneg b a hb ha  := by
  sorry

theorem mul_nneg_id_left {a : DCut} (ha: 0 ≤ a)
  : mul_nneg 1 a zero_le_one ha = a := by sorry -- use mul_pos_id_left

theorem mul_nneg_id_right {a : DCut} (ha: 0 ≤ a)
  : mul_nneg a 1 ha zero_le_one = a := by sorry -- use mul_pos_id_left

theorem mul_nneg_zero_left {a : DCut} (ha: 0 ≤ a)
  : mul_nneg 0 a (λ _ a => a) ha = 0 := by
  simp[mul_nneg,DCut.ext_iff,pre_mul,zero_rw]
  intro q hq
  simp_all[odown]
  obtain ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, h ⟩ ⟩ ⟩ ⟩ := hq
  linarith

theorem mul_nneg_zero_right {a : DCut} (ha: 0 ≤ a)
  : mul_nneg a 0 ha (λ _ a => a) = 0 := by
  simp[mul_nneg,DCut.ext_iff,pre_mul,zero_rw]
  intro q hq
  simp_all[odown]
  obtain ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, h ⟩ ⟩ ⟩ ⟩ := hq
  linarith

theorem mul_is_nneg {a b : DCut} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ mul_nneg a b ha hb := sorry

theorem mul_nneg_assoc {a b c : DCut} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
  : mul_nneg a (mul_nneg b c hb hc) ha (mul_is_nneg hb hc) =
    mul_nneg (mul_nneg a b ha hb) c (mul_is_nneg ha hb) hc := by sorry
```
 ## Mulitiplication of Arbitrary Reals 
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

instance hmul_inst : HMul DCut DCut DCut := ⟨ mul ⟩

instance mul_inst : Mul DCut := ⟨ mul ⟩

theorem mul_assoc {a b c : DCut} : a * (b * c) = (a * b) * c := sorry

theorem mul_comm {a b : DCut} : a*b = b*a := sorry

theorem mul_id_left {a : DCut} : a * 1 = a := by
  simp[hmul_inst,mul]
  by_cases ha : 0 < a
  . simp[max_pos.mp]
    simp[max_pos_to_neg, max_pos_lt, ha]
    simp[mul_nneg_zero_left,mul_nneg_zero_right,mul_nneg_id_right]
  . simp at ha
    simp[max_pos_to_neg,zero_lt_one,max_pos.mp]
    simp[mul_nneg_zero_left,mul_nneg_zero_right,mul_nneg_id_right]
    rw[not_gt_to_le] at ha
    simp[max_neg.mp,neg_max_zero_neg,ha]
```

<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
