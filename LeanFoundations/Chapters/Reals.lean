/- --------------------------------------------------------------------------
 -
 -
 -
 -
 -
 -
 -
 -                                       EE 546
 -
 -                              **REAL NUMBERS IN LEAN**
 -
 -                    DEPARTMENT OF ELECTRICAL AND COMPUTER ENGINEERING
 -                              UNIVERISITY OF WASHINGTON
 -                                 PROF.  ERIC KLAVINS
 -
 -                                     WINTER 2025
 -
 -
 -                               Reading: MIL 2.3-2.5, 3.6
 -
 -
 -
 -
 ------/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
--import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv





















/- # WHAT IS A REAL NUMBER?

One way to characterize the reals is that they are numbers with infinite decimal expansions. For example,

  1.0000000 ...        --> Also an integer
  3.5                  --> Also a fracton
  3.3333333 ...        --> Also a fracton
  1.4142135 ...        --> √2, an algebraic number, not rational
  3.1415927 ...        --> π, a trancendental number, not alegbreic or rational

We might be tempted to define the reals as all sequences of integers, and in fact at least one Real Analysis textbook does this.

But the usual method, and the one taken by Lean, is to define `Cauchy Sequences` over ℚ that converge to irrational values. For example, the sequence

  4/1
  4/1 - 4/3
  4/1 - 4/3 + 4/5
  4/1 - 4/3 + 4/5 - 4/7
  4/1 - 4/3 + 4/5 - 4/7 + 4/9

Converges to pi.

-/




/- # ISSUES

Two issues arise.

  1) What does it mean for a sequence over ℚ to converge? The normal notion of convergence over ℝ doesn't work here, because it requires knowledge about the existence of a real number being converged to. But we haven't defined ℝ yet.

    To address this, we'll define `Cauchy Convergence`, which states that as you go out in the sequence, the values become arbitrarily close to each other. This means it converges to something, but that something might not be rational. So we'll call it real.

  2) Multiple sequences can converge in this sense to the same value. That is, the values of two sequences become arbitrarily close to each other.

    To address this issue, we'll define a notion of equality on Cauchy Sequences and correspond to each `equivalence class` of sequences a real number.

-/












/- # SEQUENCES

Sequences over the rational numbers are just functions from ℕ to ℚ. -/

/- Example: (1/n) -/
def σ₁ (n : ℕ) : ℚ := (1:ℚ) / (n+1)

#eval [σ₁ 0, σ₁ 1, σ₁ 2, σ₁ 3]


/- Example: Another name for 1 ... -/
def one (n : Nat) : ℚ := match n with
  | Nat.zero => 9/10
  | Nat.succ k => one k + 9/(10^(n+1))

#eval [one 0, one 1, one 2, one 3]


/- Example: √2 -/
def sqrt2 (n : Nat) : ℚ := match n with
  | Nat.zero => 1
  | Nat.succ k => (sqrt2 k + 2 / (sqrt2 k))/2

#eval [sqrt2 0, sqrt2 1, sqrt2 2, sqrt2 3, sqrt2 4]
#eval (665857.0/470832)^2






/- # OPERATIONS ON SEQUENCES

You can perform many of the same operations on sequences as you can on numbers. This allows you to make new sequences out of old ones.  -/

def add (a b : ℕ → ℚ) := λ n => a n + b n
def mul (a b : ℕ → ℚ) := λ n => (a n)*(b n)
def scale (c : ℚ) (a : ℕ → ℚ) := λ n => c * (a n)
-- and more

-- Example
def σ₂ := scale 3 (add σ₁ (mul σ₁ σ₁))

#eval [σ₂ 0, σ₂ 1, σ₂ 2, σ₂ 3]

def two := (mul sqrt2 sqrt2)
#eval [two 0, two 1, two 2, two 3]
#eval (332929 : Float)/166464
















/- # THE USUAL NOTION OF CONVERGENCE

One notion of convergence is to specify what the sequence converges to: -/

def ConvergesTo (f : ℕ → ℚ) (x:ℚ) := ∀ ε > 0, ∃ n , ∀ m ≥ n, |f m - x| < ε

/- Here's an easy example of a constant sequence. -/
example : ConvergesTo (λ _ => 3) 3 := by
  intro ε hε
  use 1
  intro n h
  simp[hε]

/- Advanced: (1/n) → 0. This method is not covered in this class, but see MIL. -/
example : Filter.Tendsto (λ n => (1:ℚ)/n) Filter.atTop (nhds (0:ℚ)) := by
  intro X h
  simp
  exact mem_nhdsWithin_of_mem_nhds h

/- NOTE: This notion of convergence requires you know what the sequence is converging to and that it is rational.

  NOTE: The tendency in Mathlib is to prove things in the most generality possible. But this can make it hard to understand the simple examples that abound in engineering mathematics unless you know advanced topology.
-/










/- # CONVERGENCE OF THE SUM OF TWO SEQUENCES -/
#help tactic use
theorem converge_add                 -- Adapted from MIL 3.6
    {σ₁ σ₂ : ℕ → ℚ } {a b : ℚ}
    (h1 : ConvergesTo σ₁ a) (h2 : ConvergesTo σ₂ b)
    : ConvergesTo (add σ₁ σ₂) (a+b) := by

  intro ε εpos
  simp[add]
  have ε2pos : 0 < ε / 2 := by linarith
  have ⟨Ns, hs⟩ := h1 (ε/2) ε2pos
  have ⟨Nt, ht⟩ := h2 (ε/2) ε2pos

  use max Ns Nt
  intro m hm

  have ngeNs : m ≥ Ns := le_of_max_le_left hm
  have ngeNt : m ≥ Nt := le_of_max_le_right hm

  calc |σ₁ m + σ₂ m - (a + b)|
    _ = |σ₁ m - a + (σ₂ m - b)| := by congr; linarith
    _ ≤ |σ₁ m - a| + |σ₂ m - b| := (abs_add _ _)
    _ < ε / 2 + ε / 2           := (add_lt_add (hs m ngeNs) (ht m ngeNt))
    _ = ε                       := by norm_num














/- # CAUCHY SEQUENCES

A different notion of convergence is Cauchy Convergence, stating that values become arbitrary close to each other without saying what they become close to. In fact, whatever the value is, it may not be rational. -/

def IsCauchy (σ : ℕ → ℚ) :=
  ∀ ε > 0 , ∃ N : ℕ , ∀ n m : ℕ,
  n > N → m > N → abs (σ n - σ m) < ε

/- Here's the same example as above.  -/
theorem three_c : IsCauchy (λ _ => 3) := by
  intro ε hε
  use 1
  intro n m hn hm
  simp[hε]

/- Proving more complicated examples, even just 1/n, is tough without more machinery. -/

















/- # EXAMPLE: THE SUM OF CAUCHY SEQUENCES IS CAUCHY -/
#check abs_lt
#check half_pos

theorem cauchy_add {s1 s2 : ℕ → ℚ}
  : IsCauchy s1 →
    IsCauchy s2 →
    IsCauchy (add s1 s2) := by

  -- Introduce everything
  intro h1 h2 ε hε
  have ⟨ N1, h1' ⟩ := h1 (ε/2) (by exact half_pos hε)
  have ⟨ N2, h2' ⟩ := h2 (ε/2) (by exact half_pos hε)
  use N1 + N2
  intro m n gm gn

  -- Dispatch assumptions in the hypotheses
  have h1'' := h1' n m (by linarith) (by linarith)
  have h2'' := h2' n m (by linarith) (by linarith)

  -- Break the add up and the absolute values
  simp_all[add,abs_lt]

  -- The rest is arithmetic
  exact ⟨ by linarith, by linarith ⟩






















/- # EXAMPLE THE PRODUCT OF TWO CAUCHY SEQUENCES IS CAUCHY -/

theorem cauchy_mul (s1 s2 : ℕ → ℚ) :
  IsCauchy s1 →
  IsCauchy s2 →
  IsCauchy (mul s1 s2) := by
    sorry




















/- # EQUALITY OF SEQUENCES

Different sequences may converge to the same value. For example, here is a list of ways to approximate π:

  https://mathworld.wolfram.com/PiFormulas.html

Thus, every real number corresponds to a whole equivalence class of sequences. Here is the notion of equality we can use. -/

def eq (σ₁ σ₂ : ℕ → ℚ) :=
  ∀ ε > 0, ∃ N, ∀ m n,
  m > N → n > N → |σ₁ n - σ₂ m| < ε

/- Here's an example that ought to be true -/
example : eq (mul sqrt2 sqrt2) (λ _ => 2) := by

  intro ε hε
  let N := ε.den^2
  use N
  intro m n hm hn
  simp[mul]

  induction n with
  | zero =>
    simp at hn
  | succ k ih =>
    unfold sqrt2
    by_cases h1: k ≤ N
    . sorry
    . have h2 : k > N := by linarith
      have ih' := ih h2
      -- |a^2-2|<ε → |(a^2 + 2 + 4/(a^2))/4 -2| < ε
      sorry



















/- # ORDERING -/

def leq (σ τ : ℕ → ℚ) := eq σ τ ∨ ∃ N, ∀ n > N, σ n ≤ τ n





















/- # EXAMPLE : 1 ≤ √2 -/

/- The arithmetic mean is greater than or equal to the geometric mean -/
theorem am_gm (a b : ℚ) : ((a+b)/2)^2 ≥ a*b := by

  have : ((a+b)/2)^2 - a*b ≥ 0 := by
    calc ((a+b)/2)^2 - a*b
    _ = (a^2 + 2*a*b + b^2)/4 - a*b := by linarith
    _ = (a^2 - 2*a*b + b^2)/4 := by linarith
    _ = ((a-b)/2)^2 := by linarith
    _ ≥ 0 := sq_nonneg ((a - b) / 2)

  linarith

#help tactic simp!

example : leq (λ _ => 1) sqrt2 := by

  apply Or.inr
  use 0
  intro n hn

  induction n with
  | zero => rfl
  | succ k ih =>

    -- k = 0
    by_cases h0: k = 0
    . simp![h0]
      linarith

    -- k > 0
    . have : k > 0 := by exact Nat.zero_lt_of_ne_zero h0
      have ih' : 1 ≤ sqrt2 k := ih this
      unfold sqrt2

      have h4 : sqrt2 k * (2 / sqrt2 k) = 2 := by
        calc sqrt2 k * (2 / sqrt2 k)
        _ = (sqrt2 k * 2) / sqrt2 k := by rw[mul_div]
        _ = (2 * sqrt2 k) / sqrt2 k := by rw[mul_comm]
        _ = 2 * (sqrt2 k / sqrt2 k) := by rw[mul_div]
        _ = 2 * 1 := by rw[div_self]; linarith
        _ = 2 := Rat.mul_one 2

      have h5 := am_gm (sqrt2 k) (2/(sqrt2 k))
      simp[h4] at h5

      have h6 : 1 ≤ ((sqrt2 k + 2 / sqrt2 k) / 2) ^ 2 := by
        calc (1:ℚ)
        _ ≤ 2 := rfl
        _ ≤ ((sqrt2 k + 2 / sqrt2 k) / 2) ^ 2 := h5

      have h1 : 0 ≤ sqrt2 k := by linarith
      have h2 : 0 ≤ 2/(sqrt2 k) := Rat.div_nonneg rfl h1
      have h3 : 0 ≤ (sqrt2 k + 2 / sqrt2 k)/2 := Rat.div_nonneg (Rat.add_nonneg h1 h2) rfl
      exact (one_le_sq_iff₀ h3).mp h6
















/- # EXAMPLE : COMMUTATIVITY OF SEQUENCE ADDITION -/

theorem sadd_comm {σ τ : ℕ → ℚ}
  : IsCauchy σ → IsCauchy τ → eq (add σ τ) (add τ σ) := by
  intro h1 h2 ε hε
  have ⟨ N1, h1' ⟩ := h1 ε hε
  have ⟨ N2, h2' ⟩ := h2 ε hε
  use N1 + N2
  intro m n hm hn
  have h1'' := h1' m n (by linarith) (by linarith)
  have h2'' := h2' m n (by linarith) (by linarith)
  simp_all[add]
  sorry








/- # EQ IS REFLEXIVE, SYMMETRIC, AND TRANSITIVE -/

theorem eq_refl {σ : ℕ → ℚ}
  : IsCauchy σ → eq σ σ := by
  intro hc ε hε
  have ⟨ N, h ⟩ := hc ε hε
  use N
  intro m n hm hn
  have h' := h n m hn hm
  exact h'

theorem eq_sym {σ₁ σ₂ : ℕ → ℚ}
  : IsCauchy σ₁ → IsCauchy σ₂ → eq σ₁ σ₂ → eq σ₂ σ₁ := by
  intro h1 h2 h12 ε hε
  have ⟨ N1, h1' ⟩ := h1 ε hε
  have ⟨ N2, h2' ⟩ := h2 ε hε
  use N1 + N2
  intro m n hm hn
  have h1'' := h1' n m (by linarith) (by linarith)
  have h2'' := h2' n m (by linarith) (by linarith)
  sorry

theorem eq_trans {σ₁ σ₂ σ₃: ℕ → ℚ}
  : IsCauchy σ₁ → IsCauchy σ₂ → eq σ₁ σ₂ → eq σ₂ σ₃ → eq σ₁ σ₃ := by
  sorry











/- # THE CAUCHY COMPLETION OF THE RATIONALS = THE REALS -/

namespace Temp

inductive Real where
  | ofCauchy (σ : ℕ → ℚ) (h : IsCauchy σ) : Real

open Real

def three := ofCauchy (λ _ => 3) three_c













/- # OPERATIONS, RELATIONS, and PROPERTIES "LIFT" -/

/- Example operation -/
def radd (x y : Real) : Real := match x, y with
  | ofCauchy σ h1, ofCauchy τ h2 => ofCauchy (add σ τ) (cauchy_add h1 h2)

#check radd three three


/- Example relation -/
def req (x y : Real) : Prop := match x, y with
  | ofCauchy σ _, ofCauchy τ _ => eq σ τ

theorem req_refl (x : Real) : req x x := match x with
  | ofCauchy _ h => eq_refl h

example : req three three := by apply req_refl


/- Example Property -/
theorem radd_comm {x y : Real} : req (radd x y) (radd y x) := by
  match x, y with
  | ofCauchy σ h1, ofCauchy τ h2 =>
    simp[req,radd]
    exact sadd_comm h1 h2

end Temp



/- # ALL THE PROPERTIES OF THE REALS

ℝ is a field (so is ℚ)
  + and * are associative, commutative, distributive, inverses
  there are additive and multiplicative identities

ℝ is totally ordered by ≤ and respected by + and * (so is ℚ)

ℝ is complete with respect to ≤ (but ℚ isn't)
  Every bounded nonempty set has a least upper bound
  This is the only

All these properties are available, along with many more. -/

#check mul_assoc
#check add_mul
#check mul_le_mul_left
#check le_total
#check le_csSup











/- # AND MORE REAL STUFF -/

open Real

example : ∃ x : ℝ, x^2 = 2 := by
  use sqrt 2
  simp

example (x : Real) : (cos x)^2 + (sin x)^2 = 1 := by
  exact cos_sq_add_sin_sq x

example : deriv (fun x : ℝ ↦ x^5) 6 = 5 * 6^4 := by
  simp

example : deriv sin π = -1 := by
  simp











/- # REFERENCES

A nice description of the Cauchy Completion: https://mathweb.ucsd.edu/~tkemp/140A/Construction.of.R.pdf

A book that describes the Cauchy Completion:  Rudin, W.: Principles of Mathematical Analysis. Third Edition. International Series in Pure and Applied Mathematics. McGraw-Hill Book Co., New York – Aukland – Dusseldorf, 1976.ß

A real analysis book in which ℝ is constructed from decimal expansions of the form f : ℕ → ℤ with f(0) being the integer part and f(n) ∈ {0, ..., 9} for n ≥ 1. https://docs.ufpr.br/%7Ehigidio/Ensino/Seminario/Davidson-Donsig-2010-Real%20Analysis%20and%20Aplications.pdf  -/
