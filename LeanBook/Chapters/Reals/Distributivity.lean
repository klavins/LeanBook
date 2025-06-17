import Mathlib
import LeanBook.Chapters.Appendix
import LeanBook.Chapters.Reals.Dedekind
import LeanBook.Chapters.Reals.Add
import LeanBook.Chapters.Reals.Subtract
import LeanBook.Chapters.Reals.Max
import LeanBook.Chapters.Reals.Multiply
import Lean

universe u v

namespace LeanBook.Ordering

open DCut

/- # The Distributive Property -/

theorem sum_pos_pos {a b : DCut} (ha : 0 < a) (hb : 0 < b) : 0 < a + b := by
  constructor
  . intro h
    have ha0 := pos_has_zero.mp ha
    have hb0 := pos_has_zero.mp hb
    have : 0 ∈ (a+b).A := by
      exact ⟨ 0, ⟨ ha0, ⟨ 0, ⟨ hb0, by exact Rat.zero_add 0 ⟩ ⟩ ⟩ ⟩
    simp[←h,zero_rw,odown] at this
  . intro q hq
    have : q ∈ b.A := by
      simp[zero_rw,odown] at hq
      exact b.dc q 0 ⟨ by linarith, zero_in_pos hb ⟩
    exact ⟨ 0, ⟨ zero_in_pos ha, ⟨ q, ⟨ this, by linarith ⟩ ⟩ ⟩ ⟩

theorem sum_nneg_nneg {a b : DCut} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by
  rcases two_nn_ineqs ha hb with ⟨ ha, hb ⟩ | h | h
  . apply lt_imp_le
    apply sum_pos_pos ha hb
  . simp[h,sum_zero_left,hb]
  . simp[h,sum_zero_right,ha]

theorem op_from_two_vals {a : DCut} {x y : ℚ} (hx : x ∈ a.A) (hy : y ∈ a.A)
  : ∃ z ∈ a.A, x < z ∧ y < z := by
  by_cases h : x < y
  . have ⟨ z, ⟨ hz1, hz2 ⟩ ⟩ := a.op y hy
    exact ⟨ z, ⟨ hz1, ⟨ by linarith, hz2 ⟩ ⟩ ⟩
  . have ⟨ z, ⟨ hz1, hz2 ⟩ ⟩ := a.op x hx
    exact ⟨ z, ⟨ hz1, ⟨ hz2, by linarith ⟩ ⟩ ⟩

theorem prod_in_pos_mul {a b : DCut} {x y: ℚ} (ha : 0 < a) (hb : 0 < b)
                        (hx : x ∈ a.A) (hy : y ∈ b.A) (hx0 : 0 < x)
  : x*y ∈ (mul_pos a b ha hb).A := by
  obtain ⟨ x', ⟨ hx1', hx2' ⟩ ⟩ := a.op x hx
  obtain ⟨ y', ⟨ hy1', hy2' ⟩ ⟩ := op_from_two_vals hy (zero_in_pos hb)
  have hy' : 0 ≤ y' := by  linarith
  have hxy' : x * y < x' * y' := by
    have h1 : 0 < x' := by linarith
    have h2 : y ≤ y' := by linarith
    nlinarith
  exact ⟨ x', ⟨ hx1', ⟨ y', ⟨ hy1', ⟨ by linarith, ⟨ by linarith, hxy' ⟩ ⟩  ⟩ ⟩ ⟩ ⟩

theorem pos_distrib {a b c : DCut} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  : mul_pos a (sum b c) ha (sum_pos_pos hb hc) = sum (mul_pos a b ha hb) (mul_pos a c ha hc) := by

  ext q
  constructor

  . intro hq
    choose x hx yz hyz hx0 hyz0 hxyz using hq
    choose y hy z hz hyz using hyz
    rw[←hyz] at hxyz

    have hxy := prod_in_pos_mul ha hb hx hy hx0
    have hxz := prod_in_pos_mul ha hc hx hz hx0

    apply (sum (mul_pos a b ha hb) (mul_pos a c ha hc)).dc q (x*y + x*z)
    split_ands
    . linarith
    . simp[sum,presum]
      exact ⟨ x*y, ⟨ hxy, ⟨ x*z, ⟨ hxz, rfl⟩ ⟩ ⟩ ⟩

  . intro hq
    choose xy hxy xz hxz h using hq
    choose x₁ hx₁ y hy hx₁0 hy0 hx₁y using hxy
    choose x₂ hx₂ z hz hx₂0 hz0 hx₂z using hxz

    let x := max x₁ x₂
    have hx1 : x ∈ a.A := by
      by_cases g : x₁ ≤ x₂
      . have : x = x₂ := by exact max_eq_right g
        exact Set.mem_of_eq_of_mem this hx₂
      . have : x = x₁ := by exact max_eq_left (by linarith)
        exact Set.mem_of_eq_of_mem this hx₁
    have hx2 : 0 < x := by exact lt_sup_of_lt_left hx₁0

    obtain ⟨ x', ⟨ hx1', hx2' ⟩ ⟩ := a.op x hx1

    have : y + z ∈ (sum b c).A := by
      exact ⟨ y, ⟨ hy, ⟨ z, ⟨ hz, rfl ⟩ ⟩ ⟩ ⟩

    have hxyz : x*(y+z) ∈ (mul_pos a (sum b c) ha (sum_pos_pos hb hc)).A := by
      use! x', hx1', y+z, this
      split_ands
      repeat
      nlinarith

    apply (mul_pos a (sum b c) ha (sum_pos_pos hb hc)).dc q (x*(y+z))

    split_ands
    . have h' : q < x₁ * y + x₂ * z := by linarith
      have w1 : x₁ ≤ x := by exact le_max_left x₁ x₂
      have w2 : x₂ ≤ x := by exact le_max_right x₁ x₂
      nlinarith
    . exact hxyz

theorem nneg_distrib {a b c : DCut} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
  : mul_nneg a (b + c) ha (sum_nneg_nneg hb hc) =
    (mul_nneg a b ha hb) + (mul_nneg a c ha hc) := by
  rcases three_nn_ineqs ha hb hc with ⟨ ha', hb', hc' ⟩ | h | h | h
  . have h1 := nneg_eq_pos ha' (sum_pos_pos hb' hc')
    have h2 := nneg_eq_pos ha' hb'
    have h3 := nneg_eq_pos ha' hc'
    simp[hadd_inst] at h1
    simp[h1,h2,h3,hadd_inst]
    exact pos_distrib ha' hb' hc'
  repeat
  simp[h]

example {a b:DCut} : a = b ↔ -a = -b := by exact Iff.symm neg_inj

theorem neg_sum_eq {a b c: DCut} : a = b+c ↔ -a = -b + -c := by
 constructor
 repeat
 intro h
 apply neg_inj.mp
 simp[h,add_comm]

example {a b:DCut} : a*b = (-a)*(-b) := by
  simp only [mul_neg_dist_left, mul_neg_dist_right, neg_neg]

example {a b:DCut} : -a + -b = -(a+b) := by
  exact Eq.symm (neg_add a b)

theorem nn_distrib {a b c : DCut} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
  : a * (b + c) = a*b + a*c := by
  simp[hmul_inst,mul]
  simp[ha,hb,hc,neg_le.mp,sum_nneg_nneg]
  have : -c + -b ≤ 0 := by
    have := sum_nneg_nneg hc hb
    rw[negate_le,neg_add_rev,add_comm] at this
    exact this
  simp[this,sum_nneg_nneg,nneg_distrib,ha,hb,hc]

theorem bn_distrib {a b c : DCut} (ha : 0 ≤ a) (hb : b < 0) (hc : 0 ≤ c) :
  a * (b + c) = a * b + a * c := by
  by_cases h : 0 ≤ c+b
  . have h2 : a * ( (c+b) + (-b)) = a*(c+b) + a*(-b) := nn_distrib ha h (flip hb)
    simp at h2
    rw[h2]
    simp[add_comm]
  . apply neg_t.mpr at h
    apply lt_imp_le at h
    rw[←negate_le'] at h
    have h2 : a * ( -(c+b) + c ) = a*(-(c+b)) + a*c := nn_distrib ha h hc
    simp at h2
    apply neg_inj.mpr at h2
    rw[neg_neg] at h2
    rw[h2]
    simp
    rw[←neg_add,mul_neg_dist_left,neg_neg]

theorem distrib {a b c : DCut}
  : a*(b+c) = a*b+a*c := by
  rcases three_ineqs a b c with ⟨ ha, hb, hc ⟩ | ⟨ ha, hb, hc ⟩ |
                                ⟨ ha, hb, hc ⟩ | ⟨ ha, hb, hc ⟩ |
                                ⟨ ha, hb, hc ⟩ | ⟨ ha, hb, hc ⟩ |
                                ⟨ ha, hb, hc ⟩ | ⟨ ha, hb, hc ⟩

  . exact nn_distrib ha hb hc

  . have := nn_distrib (flip ha) hb hc
    rw[Iff.symm neg_inj,add_comm] at this
    simp_all[add_comm]

  . exact bn_distrib ha hb hc

  . have := bn_distrib ha hc hb
    simp[mul_neg_dist_right] at this
    rw[neg_sum_eq]
    rw[add_comm]
    rw[this]
    exact SubtractionMonoid.neg_add_rev (a * c) (a * b)

  . have := bn_distrib (flip ha) hb hc
    simp[mul_neg_dist_right] at this
    rw[neg_sum_eq]
    exact this

  . have := bn_distrib (flip ha) hc hb
    simp[mul_neg_dist_right] at this
    rw[neg_sum_eq]
    rw[add_comm]
    rw[this]
    exact sum_comm

  . have := nn_distrib ha (flip hb) (flip hc)
    simp only [←neg_add, mul_neg_dist_left, mul_neg_dist_right, neg_neg] at this
    rw[Iff.symm neg_inj]
    exact this

  . have := nn_distrib (flip ha) (flip hb) (flip hc)
    simp only [←neg_add, mul_neg_dist_left, mul_neg_dist_right, neg_neg] at this
    exact this

instance nuna_inst :  NonUnitalNonAssocSemiring DCut := ⟨
  @distrib,
  by
    intro a b c
    have := @distrib c a b
    rw [mul_comm] at this
    simp[this,mul_comm,add_comm],
  @mul_zero_left,
  @mul_zero_right
⟩

instance nusr_inst : NonUnitalSemiring DCut := ⟨
  λ x y z => Eq.symm (@mul_assoc x y z)
⟩

#print Semiring

instance semi_ring_inst : Semiring DCut := ⟨
  @mul_id_left,
  @mul_id_right,
  rfl,
  λ n => Nat.cast_add_one n,
  npow,
  @npow_zero,
  @npow_succ
⟩

theorem neg_of_rat {x : ℚ} : -ofRat x = ofRat (-x) := by
  simp[ofRat,neg_inst,neg,preneg,odown]
  ext q
  constructor
  . choose a ha b hb h
    simp_all
    linarith
  . intro hq
    simp_all
    use! q+x, (by linarith), x, (by linarith)
    linarith

theorem sub_rats {x y: ℚ} : ofRat (x-y) = ofRat x - ofRat y := by
  rw[←add_neg,neg_of_rat,Rat.sub_eq_add_neg,add_rats]

instance ring_inst : Ring DCut := ⟨
  λ a b => rfl,
  λ z a => (ofRat z) * a,
  by
    intro a
    have : ofRat 0 = 0 := rfl
    simp[this,mul_zero_left],
  by
    intro n a
    simp[add_rats,mul_comm,distrib]
    have : ofRat 1 = 1 := rfl
    simp[this],
  by
    intro n a
    simp[add_rats,mul_comm,distrib]
    simp[←neg_of_rat],
  @neg_add_cancel_left,
  λ n => rfl,
  by
    intro n
    simp[IntCast.intCast,Int.negSucc,add_rats,neg_inst]
    simp[←neg_of_rat]
    have : -ofRat 1 = -1 := rfl
    simp[this]
    rfl
⟩

instance com_ring_inst : CommRing DCut := ⟨
  @mul_comm
⟩

example {a b c : DCut} : a*(b+c) - c = a*c - c + a*b := by
  ring

example {a b : DCut} : (a-b)^2 = a^2 - 2*a*b + b^2 := by
  ring
