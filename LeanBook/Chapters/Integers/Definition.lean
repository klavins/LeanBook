import Mathlib

/- # From Pairs to Integers

Here, mainly to illustrate the use of **quotients**, we take a different approach, which is standard in foundational mathematics, although perhaps not as idiomatically type theoretic. We define pairs of natural numbers `(p,q)` and use the convention that if `p>q` then `(p,q)` represents the positive number `p-q`. Otherwise, it represents the non-positive number `q-p`. This construction allows for multiple representatives of the same number. Therefore, we define the equivalence `(p,q) ≈ (r,s)` to mean `p+s=q+r`.

As usual when defining a type with the same name as something in the standard library or in Mathlib, we open a namespace to avoid naming conflicts. The `Int` type we define in this section has the fully qualified name `LeanBook.Int`, and is a totally different type than Lean's `Int` type. -/

namespace LeanBook

/- ## Pairs of Natural Numbers

We first define pairs of natural numbers, recording the components of the pair in a simple structure. Then we define the notion of equivalence that will form the basis of the definition of an integer. -/

@[ext]
structure Pair where
  p : Nat
  q : Nat

def eq (x y: Pair) : Prop := x.p + y.q = x.q + y.p

/- Here are a few test cases. -/

example : eq ⟨1,2⟩ ⟨2,3⟩ := rfl
example : eq ⟨3,2⟩ ⟨20,19⟩ := rfl
example : ¬eq ⟨3,2⟩ ⟨20,23⟩ := by intro h; simp_all[eq]

/- ## Equivalence Relations

An **equivalence relation** `≈` is a relation that is

- reflexive: x ≈ x for all x
- symmetric: x ≈ y implies y ≈ x for all x and y
- transitive: x ≈ y and y ≈ z implies x ≈ z for all x, y and z

The relation `eq` defined above is such an equivalence relation. But we have to prove it. This is pretty easy, since it is just some basic arithmetic. -/

theorem eq_refl (u : Pair) : eq u u := by
  simp[eq]
  linarith

theorem eq_symm {v w: Pair} : eq v w → eq w v := by
  intro h
  simp_all[eq]
  linarith

theorem eq_trans {u v w: Pair} : eq u v → eq v w → eq u w := by
  intro h1 h2
  simp_all[eq]
  linarith

/- With these properties in hand, we can register an instance of `Equivalence`, a Lean 4 standard library class that stores the properties of the equivalence rlation in one object, and enables us to easily use any theorems requiring our `eq` relation to have them. -/

instance eq_equiv : Equivalence eq := ⟨ eq_refl, eq_symm, eq_trans ⟩

/- We can also register `eq` with the `HasEquiv` class, which allows us to use the `≈' notation. -/

@[simp]
instance pre_int_has_equiv : HasEquiv Pair := ⟨ eq ⟩

/- Here is an example using the new notation. -/

def u : Pair := ⟨ 1,2 ⟩
def v : Pair := ⟨ 12,13 ⟩
#check u ≈ v

/- Finally, we register `Pair` and `eq` as a `Setoid`, which is a set and an equivalence relation on the set. It is needed for the definition of the quotient space later.  -/

instance pre_int_setoid : Setoid Pair :=
  ⟨ eq, eq_equiv ⟩

/- ## Quotients

The **equivalence class** of `x` is defined to be the set of all pairs `y` such that `x≈y`. The set of all equivalence classes is called the **quotient space**, which we can form using Lean's `Quotient`:  -/

def Int := Quotient pre_int_setoid

/- We can then construct elements of `Int` using `Quotient.mk`. -/

def mk (w : Pair) : Int := Quotient.mk pre_int_setoid w

#check mk ⟨ 1, 2 ⟩  -- 1
#check mk ⟨ 2, 1 ⟩  -- -1

/- A key aspect of the quotient space is that equality is extended to elements of the quotient space. Thus, we can write: -/

#check mk ⟨ 1, 2 ⟩ = mk ⟨ 2, 3 ⟩

/- instead of using `≈`. As a result, we can us all the properties of equality we have become used to with basic types, such as definitional equality and substution.

We may now register a few more classes. The first defines zero, the second defines one, and the third defines a coercion from natural numbers to (non-negative) integers. -/

instance int_zero : Zero Int := ⟨ mk ⟨ 0,0 ⟩ ⟩
instance int_one : One Int := ⟨ mk ⟨ 1,0 ⟩ ⟩
instance int_of_nat {n: ℕ} :OfNat Int n := ⟨ mk ⟨ n, 0 ⟩ ⟩

#check (0:Int)
#check (1:Int)
#check (123:Int)
