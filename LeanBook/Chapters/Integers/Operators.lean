import Mathlib
import LeanBook.Chapters.Integers.Definition

namespace LeanBook

/- # Lifting Operators

In this section we show how to _lift_ an operation, such as negation or addition, from `Pair` to `Int`, and more generally from any type to a quotient on that type. -/

/- ## Lifting Negation

Next, we define the meaning of negation, which is simply to switch the elements of a pair. -/

def pre_negate (x : Pair) : Pair := ⟨ x.q, x.p ⟩

/- We would like to **lift** the definition of negation to our new `Int` type. This means defining negation of an entire equivalence class, which would only work if our `pre_negate` function has the same result on all elements of an equivalence class, which fortunately it does! To capture this notion we define a _respects_ theorem.  -/

theorem pre_negate_respects (x y : Pair) :
  x ≈ y → mk (pre_negate x) = mk (pre_negate y) := by
  intro h
  simp_all[pre_int_setoid,eq]
  apply Quot.sound
  simp[pre_int_setoid,eq,pre_negate,h]

/- With this theorem, we may use Lean's `Quotient.lift` to define `negate` on `Int`. -/

def pre_negate' (x : Pair) : Int := mk (pre_negate x)

def negate (x : Int) : Int := Quotient.lift pre_negate' pre_negate_respects x

/- We may register our negation function wit the `Neg` class, allowing us to use the `-` notation for it, and to use any general theorems proved in Mathlib for types with negation.  -/

instance int_negate : Neg Int := ⟨ negate ⟩

/- To prove theorems about negation we need some fundamental tools for proving properties of quotients:

- `Quotient.exists_rep`, which says `∃ a, ⟦a⟧ = q`. This operator allows you to assert the existence of a representative of an equivalence class. Then, if you are trying to prove a result about the equivalence class, it amounts to proving it about the representative.

- `Quotient.sound`, which says `a ≈ b → ⟦a⟧ = ⟦b⟧`. Applying this operator allows you to replace a goal involving proving two equivalence classes are equal, with one showing that representatives of the respective equivalence classes are equivalent under the associated Setoid relation. In other words, we _unlift_ the equality back to the underlying space.

Using these two operations, we have may prove a simple theorem: -/

theorem negate_negate { x : Int } : -(-x) = x := by
  let ⟨ u, hu ⟩ := Quotient.exists_rep x
  rw[←hu]
  apply Quot.sound
  simp[pre_int_setoid,pre_negate,eq]
  linarith


/- ## Lifing Addition

Just as we lifted negation, we can also define and lift addition. For pairs, addition is just componentwise addition. -/

def pre_add (x y : Pair) : Pair := ⟨ x.p + y.p, x.q + y.q ⟩

/- To do the lift, we need another respects theorey. This time, the theorem assumes multiple equivalences. -/

theorem pre_add_respects (w x y z : Pair)
  : w ≈ y → x ≈ z → mk (pre_add w x) = mk (pre_add y z) := by
  intro h1 h2
  apply Quot.sound
  simp_all[pre_int_setoid,eq,pre_add]
  linarith

/- With this theorem we can define addition on integers. -/

def pre_add' (x y : Pair) : Int := mk (pre_add x y)

def add (x y : Int) : Int := Quotient.lift₂ pre_add' pre_add_respects x y

/- And while we are at it, we can register addition with Mathlib's Add class so we can use `+`. -/

instance int_add : Add Int := ⟨ add ⟩

/- Here is an example. It is remarkable to see that the entire edifice we have build can interact so easily with `rfl`. -/

example : (1:Int) + 17 = 18 := rfl
