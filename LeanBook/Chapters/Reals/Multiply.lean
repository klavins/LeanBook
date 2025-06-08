import Mathlib
import LeanBook.Chapters.Appendix
import LeanBook.Chapters.Reals.Dedekind
import LeanBook.Chapters.Reals.Add
import LeanBook.Chapters.Reals.Subtract
import LeanBook.Chapters.Reals.Max

universe u v

namespace LeanBook.Ordering
open LeanBook.Ordering

open DCut

/- # Multiplication

Multiplication of Dedekind cuts is straightfoward, but also fairly involved, or as Rudin says: "bothersome". The issue is dealing with positive and negative cutes. Following Rudin, the development of the definitions proceeds as follows:

- Define multiplication on two positive cuts `0 < x₁` and `0 < x₂` as the set of points `c` such that for some `a ∈ x₁` and `b ∈ x₂`, `c < ab`.
- Extend multiplciation on positive cuts to non-negative cuts `0 ≤ x₁` and `0 ≤ x₂` building on the previous step by handling the case in which either or both of the cuts is zero.
- Extend multiplication on non-negative cuts to all cuts. This step requires noting that every cut `x` can be written as the different `max 0 x - max 0 (-x)` between two non-negative cuts.

For each of the above definitions of multiplication, we also prove the properties required to show that multiplication forms a commutiative group on cuts:
- 0 is an identity: 0x = 0.
- Multiplication is commutative: xy = yx.
- Associativity: x(yz) = (xy)z
The last property is particularly challenging. In priciple, one has to reason about 27 differen cases where each of x, y and z are either positive, negative or zero. Thus, along the way we will prove several intermediate results which allow us to make the proof more concise.

-/

/- ## Multiplication of Positive Reals -/

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

/- ## Properties -/

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

/- ## Mulitiplication of Non-negative Reals -/

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

theorem mul_nneg_comm {a b : DCut} (ha : 0 ≤ a) (hb : 0 ≤ b)
  : mul_nneg a b ha hb = mul_nneg b a hb ha := by
  by_cases h : 0 < a ∧ 0 < b
  . simp[mul_nneg]
    have := mul_pos_comm h.left h.right
    simp_all[mul_pos]
  . simp[lt_of_le] at h
    by_cases hb0 : 0 = b
    . simp[←hb0,mul_nneg_zero_right,mul_nneg_zero_left]
    . simp_all
      simp[←h,mul_nneg_zero_right,mul_nneg_zero_left]

theorem mul_is_nneg {a b : DCut} (ha : 0 ≤ a) (hb : 0 ≤ b)
  : 0 ≤ mul_nneg a b ha hb := by
  by_cases h : 0 < a ∧ 0 < b
  . have := mul_is_pos h.left h.right
    simp[lt_inst,mul_pos] at this
    have ⟨ h1, h2 ⟩ := this
    simp[le_inst,mul_nneg]
    exact Set.subset_union_right
  . by_cases hb0 : 0 = a
    . simp[←hb0,mul_nneg_zero_right,mul_nneg_zero_left]
    . simp_all[lt_of_le]
      simp[←h,mul_nneg_zero_right,mul_nneg_zero_left]

theorem mul_nneg_id_left {a : DCut} (ha: 0 ≤ a)
  : mul_nneg 1 a zero_le_one ha = a := by
    rw[le_of_lt] at ha
    apply Or.elim ha
    intro ha0
    . simp[←ha0,mul_nneg_zero_right]
    . intro ha'
      have := mul_pos_id_left ha'
      simp_all[mul_pos,DCut.ext_iff,mul_nneg,DCut.ext_iff]
      exact ha

theorem mul_nneg_id_right {a : DCut} (ha: 0 ≤ a)
  : mul_nneg a 1 ha zero_le_one = a := by
  rw[mul_nneg_comm,mul_nneg_id_left]

theorem mul_nneg_assoc {a b c : DCut} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
  : mul_nneg a (mul_nneg b c hb hc) ha (mul_is_nneg hb hc) =
    mul_nneg (mul_nneg a b ha hb) c (mul_is_nneg ha hb) hc := by
  by_cases h : 0 < a ∧ 0 < b ∧ 0 < c
  . have h1 := mul_pos_assoc h.left h.right.left h.right.right
    simp[mul_pos] at h1
    simp[mul_nneg]
    have h2 : pre_mul b c ∪ odown 0 = pre_mul b c := by
      have := mul_is_pos h.right.left h.right.right
      simp[mul_pos,lt_inst,zero_rw] at this
      simp_all
    have h3 : pre_mul a b ∪ odown 0 = pre_mul a b := by
      have := mul_is_pos h.left h.right.left
      simp[mul_pos,lt_inst,zero_rw] at this
      simp_all
    simp[h1,h2,h3]
  by_cases h1 : 0 = a
  . simp[←h1,mul_nneg_zero_left]
  by_cases h2 : 0 = b
  . simp[←h2,mul_nneg_zero_right,mul_nneg_zero_left]
  by_cases h3 : 0 = c
  . simp[←h3,mul_nneg_zero_right,mul_nneg_zero_left]
  . simp_all[lt_of_le]

/- ## Mulitiplication of Arbitrary Reals -/

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

theorem mul_id_right {a : DCut} : a * 1 = a := by
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

theorem mul_zero_left {a : DCut} : 0 * a = 0 := by
  simp[hmul_inst,mul]

theorem mul_zero_right {a : DCut} : a * 0 = 0 := by
  simp[hmul_inst,mul]


theorem mul_comm_pp {a b : DCut} (ha : 0 ≤ a) (hb : 0 ≤ b) : a*b = b*a := by
  have ha' : -a ≤ 0 := by exact neg_le.mp ha
  have hb' : -b ≤ 0 := by exact neg_le.mp hb
  simp[hmul_inst,mul]
  simp[max_pos.mp,ha,hb,max_pos_lt,max_neg.mp,max_neg_lt,ha',hb']
  simp[mul_nneg_zero_left,mul_nneg_zero_right,mul_nneg_id_right]
  simp[mul_nneg_comm]

theorem mul_comm_pn {a b : DCut} (ha : 0 ≤ a) (hb : b ≤ 0) : a*b = b*a := by
  have ha' : -a ≤ 0 := by exact neg_le.mp ha
  have hb' : 0 ≤ -b := by exact neg_le'.mp hb
  simp[hmul_inst,mul]
  simp[max_pos.mp,ha,hb,max_pos_lt,max_neg.mp,max_neg_lt,ha',hb']
  simp[mul_nneg_zero_left,mul_nneg_zero_right,mul_nneg_id_right]
  simp[mul_nneg_comm]

theorem mul_comm_np {a b : DCut} (ha : a ≤ 0) (hb : 0 ≤ b) : a*b = b*a := by
  have ha' : 0 ≤ -a := by exact neg_le'.mp ha
  have hb' : -b ≤ 0 := by exact neg_le.mp hb
  simp[hmul_inst,mul]
  simp[max_pos.mp,ha,hb,max_pos_lt,max_neg.mp,max_neg_lt,ha',hb']
  simp[mul_nneg_zero_left,mul_nneg_zero_right,mul_nneg_id_right]
  simp[mul_nneg_comm]

theorem mul_comm_nn {a b : DCut} (ha : a ≤ 0) (hb : b ≤ 0) : a*b = b*a := by
  have ha' : 0 ≤ -a := by exact neg_le'.mp ha
  have hb' : 0 ≤ -b := by exact neg_le'.mp hb
  simp[hmul_inst,mul]
  simp[max_pos.mp,ha,hb,max_pos_lt,max_neg.mp,max_neg_lt,ha',hb']
  simp[mul_nneg_zero_left,mul_nneg_zero_right,mul_nneg_id_right]
  simp[mul_nneg_comm]

theorem mul_comm {a b : DCut}: a*b = b*a := by
  by_cases h1 : 0 ≤ a ∧ 0 ≤ b
  . exact mul_comm_pp h1.left h1.right
  by_cases h2 : 0 ≤ a ∧ b ≤ 0
  . exact mul_comm_pn h2.left h2.right
  by_cases h3 : a ≤ 0 ∧ 0 ≤ b
  . exact mul_comm_np h3.left h3.right
  by_cases h4 : a ≤ 0 ∧ b ≤ 0
  . exact mul_comm_nn h4.left h4.right
  . have hat := trichotomy a 0
    have hbt := trichotomy b 0
    apply Or.elim (trichotomy a 0)
    . intro h
      simp_all[mul_zero_left,mul_zero_right]
    . intro h
      apply Or.elim h
      . intro h
        simp_all[mul_zero_left,mul_zero_right]
      . intro h
        simp_all[mul_zero_left,mul_zero_right]

theorem mul_id_left {a : DCut} : 1 * a = a := by
  rw[mul_comm,mul_id_right]

theorem mul_neg_dist_left {a b : DCut} : a*(-b) = -(a*b) := by
  simp[hmul_inst,mul]
  rcases @two_ineqs_true a b with ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩
  repeat (
    simp[max_pos.mp,ha,hb,max_pos_lt,max_neg.mp,max_neg_lt,neg_le.mp]
    simp[mul_nneg_zero_left,mul_nneg_zero_right,mul_nneg_id_right]
  )

theorem mul_neg_dist_right {a b : DCut} : (-a)*b = -(a*b) := by
  simp[hmul_inst,mul]
  rcases @two_ineqs_true a b with ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩
  repeat (
    simp[max_pos.mp,ha,hb,max_pos_lt,max_neg.mp,max_neg_lt,neg_le.mp]
    simp[mul_nneg_zero_left,mul_nneg_zero_right,mul_nneg_id_right]
  )

theorem mul_assoc_az {a b c : DCut} (ha : 0 = a)
  : a * (b * c) = (a * b) * c := by
  simp[←ha,mul_zero_left]

theorem mul_assoc_bz {a b c : DCut} (hb : 0 = b)
  : a * (b * c) = (a * b) * c := by
  simp[←hb,mul_zero_right,mul_zero_left]

theorem mul_assoc_cz {a b c : DCut} (hc : 0 = c)
  : a * (b * c) = (a * b) * c := by
  simp[←hc,mul_zero_right]

theorem mul_assoc_all_nn {a b c : DCut} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
  : a * (b * c) = (a * b) * c := by

  have ha' : -a ≤ 0 := by exact neg_le.mp ha
  have hb' : -b ≤ 0 := by exact neg_le.mp hb
  have hc' : -c ≤ 0 := by exact neg_le.mp hc

  have hab : 0 ≤ mul_nneg a b ha hb := by exact mul_is_nneg ha hb
  have hab' : -mul_nneg a b ha hb ≤ 0 := by exact neg_le.mp hab
  have hbc : 0 ≤ mul_nneg b c hb hc := by exact mul_is_nneg hb hc
  have hbc' : -mul_nneg b c hb hc ≤ 0 := by exact neg_le.mp hbc

  simp[hmul_inst,mul]
  simp[max_pos.mp,ha,hb,hc,max_pos_lt,max_neg.mp,max_neg_lt,ha',hb',hc']
  simp[mul_nneg_zero_left,mul_nneg_zero_right,mul_nneg_id_right]
  simp[max_pos.mp,hbc,hab,max_neg.mp,hab',hbc']
  simp[mul_nneg_zero_left,mul_nneg_zero_right,mul_nneg_id_right]
  simp[mul_nneg_assoc]

/-
When a ≤ 0 while 0 ≤ b and 0 ≤ c then

   (a*b)*c = a*(b*c)

becomes

   -((-a)*b)*c = -((-a)*(b*c))

and then use mul_assoc_all_nn. Similarly, we can do all the other cases this way.
-/

/- ### One Non-Positive Value -/

theorem ta {a b c : DCut} (ha : a ≤ 0) (hb : 0 ≤ b) (hc : 0 ≤ c)
  : a*(b*c) = (a*b)*c := by
  calc a*(b*c)
  _ = -((-a)*(b*c)) := by simp[mul_neg_dist_left,mul_neg_dist_right]
  _ = -(((-a)*b)*c) := congrArg Neg.neg (mul_assoc_all_nn (neg_le'.mp ha) hb hc)
  _ = (a*b)*c       := by simp[mul_neg_dist_right]

theorem tb {a b c : DCut} (ha : 0 ≤ a) (hb : b ≤ 0) (hc : 0 ≤ c)
  : a*(b*c) = (a*b)*c := by
  calc a*(b*c)
  _ = -(a*((-b)*c)) := by simp[mul_neg_dist_left,mul_neg_dist_right]
  _ = -((a*(-b))*c) := congrArg Neg.neg (mul_assoc_all_nn ha (neg_le'.mp hb) hc)
  _ = (a*b)*c       := by simp[mul_neg_dist_left,mul_neg_dist_right]

theorem tc {a b c : DCut} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : c ≤ 0)
  : a*(b*c) = (a*b)*c := by
  calc a*(b*c)
  _ = -(a*(b*(-c))) := by simp[mul_neg_dist_left,mul_neg_dist_right]
  _ = -((a*b)*(-c)) := congrArg Neg.neg (mul_assoc_all_nn ha hb (neg_le'.mp hc))
  _ = (a*b)*c       := by simp[mul_neg_dist_left,mul_neg_dist_right]

/- ### Two Non-Positive Values -/

theorem tab {a b c : DCut} (ha : a ≤ 0) (hb : b ≤ 0) (hc : 0 ≤ c) : a*(b*c) = (a*b)*c := by
  calc a*(b*c)
  _ = (-a)*((-b)*c) := by simp[mul_neg_dist_left,mul_neg_dist_right]
  _ = ((-a)*(-b))*c := mul_assoc_all_nn (neg_le'.mp ha) (neg_le'.mp hb) hc
  _ = (a*b)*c       := by simp[mul_neg_dist_left,mul_neg_dist_right]

theorem tac {a b c : DCut} (ha : a ≤ 0) (hb : 0 ≤ b) (hc : c ≤ 0) : a*(b*c) = (a*b)*c := by
  calc a*(b*c)
  _ = (-a)*(b*(-c)) := by simp[mul_neg_dist_left,mul_neg_dist_right]
  _ = ((-a)*b)*(-c) := mul_assoc_all_nn (neg_le'.mp ha) hb (neg_le'.mp hc)
  _ = (a*b)*c       := by simp[mul_neg_dist_left,mul_neg_dist_right]

theorem tbc {a b c : DCut} (ha : 0 ≤ a) (hb : b ≤ 0) (hc : c ≤ 0) : a*(b*c) = (a*b)*c := by
  calc a*(b*c)
  _ = a*((-b)*(-c)) := by simp[mul_neg_dist_left,mul_neg_dist_right]
  _ = (a*(-b))*(-c) := mul_assoc_all_nn ha (neg_le'.mp hb) (neg_le'.mp hc)
  _ = (a*b)*c       := by simp[mul_neg_dist_left,mul_neg_dist_right]

/- ### Three Non-Positive Values -/

theorem tabc {a b c : DCut} (ha : a ≤ 0) (hb : b ≤ 0) (hc : c ≤ 0) : a*(b*c) = (a*b)*c := by
  calc a*(b*c)
  _ = -((-a)*((-b)*(-c))) := by simp[mul_neg_dist_left,mul_neg_dist_right]
  _ = -(((-a)*(-b))*(-c)) := congrArg Neg.neg (mul_assoc_all_nn (neg_le'.mp ha) (neg_le'.mp hb) (neg_le'.mp hc))
  _ = (a*b)*c             := by simp[mul_neg_dist_left,mul_neg_dist_right]


theorem mul_assoc {a b c : DCut} : a * (b * c) = (a * b) * c := by
  rcases @three_ineqs_true a b c with ⟨ ha, hb, hc ⟩ | ⟨ ha, hb, hc ⟩ |
                                      ⟨ ha, hb, hc ⟩ | ⟨ ha, hb, hc ⟩ |
                                      ⟨ ha, hb, hc ⟩ | ⟨ ha, hb, hc ⟩ |
                                      ⟨ ha, hb, hc ⟩ | ⟨ ha, hb, hc ⟩
  . exact mul_assoc_all_nn ha hb hc
  . exact ta (lt_imp_le ha) hb hc
  . exact tb ha (lt_imp_le hb) hc
  . exact tc ha hb (lt_imp_le hc)
  . exact tab (lt_imp_le ha) (lt_imp_le hb) hc
  . exact tac (lt_imp_le ha) hb (lt_imp_le hc)
  . exact tbc ha (lt_imp_le hb) (lt_imp_le hc)
  . exact tabc (lt_imp_le ha) (lt_imp_le hb) (lt_imp_le hc)

/- ## Instantiating Multiplication Classes -/

instance mul_one_inst : MulOneClass DCut := ⟨
  @mul_id_left,
  @mul_id_right
⟩

instance semigroup_inst : Semigroup DCut := ⟨
  λ x y z => Eq.symm (@mul_assoc x y z)
⟩

instance comm_magma_inst : CommMagma DCut := ⟨ @mul_comm ⟩

instance comm_semigroup_inst : CommSemigroup DCut := ⟨ @mul_comm ⟩

example {x y z :DCut} : (x+y)*z = z*(y+x) := by
  rw[@_root_.mul_comm] -- This is mathlib's CommMagma mul_com
  abel_nf


/- ## Natural Powers and Monoid Instance -/

def npow (n: ℕ) (x : DCut) : DCut := match n with
  | Nat.zero => 1
  | Nat.succ k => x * (npow k x)

theorem npow_zero {x : DCut} : npow 0 x = 1 := by rfl

theorem npow_succ {n : ℕ} {x : DCut} : npow (n+1) x = npow n x * x := by
  simp[npow]
  rw[mul_comm]

instance monoid_inst : Monoid DCut := ⟨
  @mul_id_left,
  @mul_id_right, -- why does this need to be here if this is already a MulOneClass?
  npow,
  @npow_zero,
  @npow_succ
⟩

example (x : DCut) : x^2 = x*x := by
  exact pow_two x --> pow_two is a theorem about monoids from Mathlib

set_option trace.Meta.synthInstance true
set_option synthInstance.maxHeartbeats 400
set_option trace.Meta.synthInstance.answer true

#synth Field ℝ

#print Field
