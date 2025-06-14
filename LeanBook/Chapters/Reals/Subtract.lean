import Mathlib
import LeanBook.Chapters.Appendix
import LeanBook.Chapters.Reals.Dedekind
import LeanBook.Chapters.Reals.Add

universe u v

namespace LeanBook.Ordering
open LeanBook.Ordering

open DCut

/- # Negation -/

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
    apply b_up_closed hq
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
    exact b_up_closed hy h2 hq
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



/- ## Subtraction -/

def sub (a b : DCut) : DCut := a + (-b)

instance hsub_inst : HSub DCut DCut DCut := ⟨ sub ⟩

instance sub_inst : Sub DCut := ⟨ sub ⟩

theorem add_neg (a b : DCut) : a + -b = a - b := by
  simp[hsub_inst,sub]

/- Let's check this definition works for the simple example `1-1=0`. The forward direction is easy. For the reverse direction, we need to choose x and y so that

  - `x < 1`
  - `y < -1`
  - `x + y = q`

Since q < 0, we know q-1 < -1. For y, we take the point halfway between q-1 and -1, which is `y = (q-2)/2`.

-/

example : ofRat 1 - ofRat 1 = ofRat 0 := by
  simp[hsub_inst,sub,neg_rat]
  ext q
  simp[hadd_inst,sum,ofRat,presum,odown]
  constructor
  . intro ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, h ⟩ ⟩ ⟩ ⟩
    linarith
  . intro hq
    exact ⟨ (q+2)/2, ⟨ by linarith, ⟨ (q-2)/2, ⟨ by linarith, by linarith ⟩ ⟩ ⟩ ⟩

/- More challenging is to show for any cut `c` that `c-c=0`. We are given `q<0`. Since `c.A` is not `ℚ`, we can choose an element `t ∉ c.A`. We then want to find `a ∈ -c.A` and `b ∈ c.A` so that `a+b=q`. Using the Archimedean property of the rational numbers, we can find `n` such that `t + (n+1)q ∈ c.A` and `t + nq ∉ c.A`.

These values do not work directly because of the edge case where `c` is a principal cut (representing a rational number). For example, the situation could look like the diagram below.
```
                -c.A                        b      c.A    -a
       -t - nq             q       0   t + (n+1)q       t + nq
  ←———————+———————)————————+———————+———————+————————)—————+————————————→
                 -2       -1             4-3=1      2   4-2=2
```

But because `c.A` is open, we can find `z` greater than `t + (n+1)q` and which is still in c.A.
```
        -c.A                                              c.A
                      q          0    t + (n+1)q                  t + nq
  ←———————)———————————+——————————+————————+————————+———————)————————+————————————→
                                                   z
```

And then take ε = z - (t + (n+1)q) to get the following situation, where `a` is completly inside `-c.A`.
```
          a    -c.A                        b          c.A
  ←———————+———————)———————+———————+————————+———————————)———————+————————————→
   -t - nq - ε            q       0    t + (n+1)q + ε       t + nq + ε
```

This proof outline takes some work to get done in Lean. First we need a result showing that given `t ∉ c.A` we can find an `n` so that `t + n s ∈ c.A`. -/

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

/- We then define the set of all `n` such that t + ns ∈ c.A. For subsequent steps to work, we need to instantiate this set as decidable. This can be done using Classical logic, in which propositions are considered decidable by default. -/

def Svals (c : DCut) (s t : ℚ) : Set ℕ := {n : ℕ | t + n * s ∈ c.A}

noncomputable
instance s_dec {c : DCut} {s t : ℚ}  : DecidablePred (· ∈ Svals c s t) := by
    intro n
    apply Classical.propDecidable

/- With `Svals` decidiable and nonempty, we can use `Nat.find` to show it has a minimal element. Note that `Nat.find` uses the Axiom of Choice.  -/

theorem min_element (S : Set ℕ) [DecidablePred (· ∈ S)] (h : ∃ x, x ∈ S)
  : ∃ m, m ∈ S ∧ (∀ k < m, k ∉ S) := by
  have hsne : S.Nonempty := h
  let m := Nat.find hsne
  have hm : m ∈ S := Nat.find_spec hsne
  have hm_min : ∀ k < m, k ∉ S := λ k => Nat.find_min hsne
  exact ⟨ m, hm, hm_min ⟩

/- We use the minimal element to find `n` so that  `t + (n+1)q ∈ c.A` and `t + nq ∉ c.A`. as desired. -/

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

/- Finally, we prove the desired theorem. -/

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

/- And by commutativity: -/

theorem neg_add_cancel_left {c : DCut} : -c + c = 0 := by
  rw[sum_comm,add_neg,neg_add_cancel_right]

/- ## Additive Group Structure -/

instance add_group_inst : AddGroup DCut :=
  AddGroup.ofLeftAxioms add_assoc @sum_zero_left @neg_add_cancel_left

instance add_comm_group_inst : AddCommGroup DCut := ⟨ @sum_comm ⟩

example (x y z : DCut) : x - y + z = z + x - y := by abel

instance add_monoid_wo_inst : AddMonoidWithOne DCut := ⟨
    by
      ext q
      exact ⟨ id, id ⟩,
    by
      intro n
      ext q
      constructor
      repeat
      . intro hq
        simp_all[add_rats,nat_cast_inst]
        exact hq
  ⟩
