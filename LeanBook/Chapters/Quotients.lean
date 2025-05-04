import Mathlib

/- # Integers via Quotients

Now that we have defined the natural numbers `Nat`, the next obvious step is to define the ingeters `Int`(whole numbers that can be positive, negative or zero) . This can be done in several ways. For example, the Lean 4 standard library defines integers inductively say that (a) any natural numbers is an integer, and (b) the negative successor of an integer is an integer.

Here, mainly to illustrate the use of **quotients**, we take a different approach, which is also standard in foundational mathematics. We define pairs of natural numbers `(p,q)` and use the convention that if `p>q` then `(p,q)` represents the positive number `p-q`. Otherwise, it represents the non-positive number `q-p`. This construction allows for multiple representatives of the same number. Therefore, we define the equivalence `(p,q) ≈ (r,s)` to mean `p+s=q+r`. This approach is standard in foundational mathematics. For example, see Nicolas Bourbaki's _Algebra_. -/

namespace Temp

/- ## Pairs of Natural Numbers

We first define pairs of natural numbers, keeping the components of the pair in a simple structure. And then we define the notion of equivalence that will form the basis of the definition of an integer. -/

@[ext]
structure Pair where
  p : Nat
  q : Nat

def eq (x y: Pair) : Prop := x.p + y.q = x.q + y.p

example : eq ⟨1,2⟩ ⟨2,3⟩ := rfl
example : eq ⟨3,2⟩ ⟨20,19⟩ := rfl
example : ¬eq ⟨3,2⟩ ⟨20,23⟩ := by intro h; simp_all[eq]

/- ## Equivalence Relations

An **equivalence relation** is a relation that is reflexive, symmetric, and transitive. To define a  quotient space, we need to first show our `eq` relation has these properties. This is pretty easy. -/

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

/- With these properties in hand, we can register an instance of `Equivalence`, a Lean 4 standard library class that stores the properties in one object, and enables us to easily use any theorems requiring our `eq` relation to have them. -/

instance eq_equiv : Equivalence eq := ⟨ eq_refl, eq_symm, eq_trans ⟩

/- We can also register `eq` with the `HasEquiv` class, which allows us to use the `≈' notation. -/

@[simp]
instance pre_int_has_equiv : HasEquiv Pair := ⟨ eq ⟩

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

/- A key aspect of the quotient space is that equality is extended to elements of the quotient space. Thus, we can write -/

#check mk ⟨ 1, 2 ⟩ = mk ⟨ 2, 3 ⟩

/- instead of using `≈`. The result is that we can us all the properties of equality we are used to with basic types, such as definitional equality and substution.

With `Int` defined, we may now register a few more classes. The first defines zero, the second defines one, and the third defines a coercion from natural numbers to (non-negative) integers. -/

instance int_zero : Zero Int := ⟨ mk ⟨ 0,0 ⟩ ⟩
instance int_one : One Int := ⟨ mk ⟨ 1,0 ⟩ ⟩
instance int_of_nat {n: ℕ} :OfNat Int n := ⟨ mk ⟨ n, 0 ⟩ ⟩

#check (0:Int)
#check (1:Int)
#check (123:Int)

/- ## Lifting Functions: Negation

Next, we define the meaning of negation, which is simply to switch the elements of a pair. -/

def pre_negate (x : Pair) : Pair := ⟨ x.q, x.p ⟩

/- We would like to **lift** the definition of negation to our new `Int` type. This means defining negation of an entire equivalence class, which would only work if our `pre_negate` function has the same result on all elements of an equivalence class, which fortunately it does! To capture this notion we define a _respects_ theorem.  -/

theorem pre_negate_respects (x y : Pair) :
  x ≈ y → mk (pre_negate x) = mk (pre_negate y) := by
  intro h
  simp_all[pre_int_setoid,eq]
  apply Quot.sound
  simp[pre_int_setoid,eq,pre_negate,h]

/- With this theorem in place, we simply use Lean's `Quotient.lift` to define `negate` on `Int`. -/

def pre_negate' (x : Pair) : Int := mk (pre_negate x)

def negate (x : Int) : Int := Quotient.lift pre_negate' pre_negate_respects x

/- And we can register our negation function wit the `Neg` class, allowing us to use the `-` notation for it. -/

instance int_negate : Neg Int := ⟨ negate ⟩

/- Here is an example proof using negation, the notation for it. It also introduces to fundamental tools for proving properties of quotients:

- `Quotient.exists_rep`, which says `∃ a, ⟦a⟧ = q`. This operator allows you to assert the existence of a representative of an equivalence class. Then, if you are trying to prove a result about the equivalence class, it amounts to proving it about the representative.

- `Quotient.sound`, which says `a ≈ b → ⟦a⟧ = ⟦b⟧`. Applying this operator allows you to replace a goal involving proving two equivalence classes are equal, with one showing that representatives of the respective equivalence classes are equivalent under the associated Setoid relation. In other words, we _unlift_ the equality back to the underlying space. -/

theorem negate_negate { x : Int } : -(-x) = x := by
  let ⟨ u, hu ⟩ := Quotient.exists_rep x
  rw[←hu]
  apply Quot.sound
  simp[pre_int_setoid,pre_negate,eq]
  linarith

/- ## Lifing Operators: Addition

(1,2) + (2,3) = (3,5)
-1      -1    = -2

(1,3) + (6,2) = (7,5)
-2    + 4     = 2

-/

def pre_add (x y : Pair) : Pair := ⟨ x.p + y.p, x.q + y.q ⟩

theorem pre_add_respects (w x y z : Pair)
  : w ≈ y → x ≈ z → mk (pre_add w x) = mk (pre_add y z) := by
  intro h1 h2
  apply Quot.sound
  simp_all[pre_int_setoid,eq,pre_add]
  linarith

def pre_add' (x y : Pair) : Int := mk (pre_add x y)

def add (x y : Int) : Int := Quotient.lift₂ pre_add' pre_add_respects x y

instance int_add : Add Int := ⟨ add ⟩

/- ## Lifting Theorems : Additive Commutivity

There is no direct operator for lifting theorems, but doing so is straightforward. One typically defines a theorem on the base space and then uses it to prove the corresponding theorem on the quotient space. For example, here are several theorems defined on pairs. -/

theorem pre_add_com {x y: Pair} : eq (pre_add x y) (pre_add y x) := by
  simp[eq,pre_add]
  linarith

theorem pre_add_assoc {x y z: Pair}
  : eq (pre_add (pre_add x y) z) (pre_add x (pre_add y z))  := by
  simp[eq,pre_add]
  linarith

theorem pre_zero_add (x : Pair) : eq (pre_add ⟨0,0⟩ x) x := by
  simp[eq,pre_add]
  linarith

theorem pre_inv_add_cancel (x : Pair) : eq (pre_add (pre_negate x) x) ⟨0,0⟩ := by
  simp[eq,pre_negate,pre_add]
  linarith

/- To lift these theorems to Int, we apply essentially the same pattern to each. We assert the existence of `Pairs` that represent each of the intgers in the target theorem. We substitute those in for the integers. We use `Quot.sound` to restate the goal in terms of pairs. And finally we use the underlying theorem. Here are several examples: -/

theorem add_comm (x y: Int) : x+y = y+x := by
  have ⟨ u, hu ⟩ := Quotient.exists_rep x
  have ⟨ v, hv ⟩ := Quotient.exists_rep y
  rw[←hu,←hv]
  apply Quot.sound
  apply pre_add_com

theorem add_assoc (x y z: Int) : x+y+z = x+(y+z) := by
  have ⟨ u, hu ⟩ := Quotient.exists_rep x
  have ⟨ v, hv ⟩ := Quotient.exists_rep y
  have ⟨ w, hw ⟩ := Quotient.exists_rep z
  rw[←hu,←hv,←hw]
  apply Quot.sound
  apply pre_add_assoc

theorem zero_add (x : Int) : 0 + x = x := by
  have ⟨ u, hu ⟩ := Quotient.exists_rep x
  rw[←hu]
  apply Quot.sound
  apply pre_zero_add

theorem inv_add_cancel (x : Int) : -x + x = 0 := by
  have ⟨ u, hu ⟩ := Quotient.exists_rep x
  rw[←hu]
  apply Quot.sound
  apply pre_inv_add_cancel

/- ## Defining the Additive Group Structure on Int

The theorems above were chosen so that we could instantiate a everything we need to show that `Int` forms an additive, commutative group! -/

instance int_add_comm_magma : AddCommMagma Int :=
  ⟨ add_comm ⟩

instance int_add_semi : AddSemigroup Int :=
  ⟨ add_assoc ⟩

instance int_add_comm_semi : AddCommSemigroup Int := ⟨ add_comm ⟩

instance int_group : AddGroup Int :=
  AddGroup.ofLeftAxioms add_assoc zero_add inv_add_cancel

/- Now we get all the theorems and tactics about additive groups from Mathlib to apply to our `Int` type! For example, -/

example (x: Int) : x-x = 0 := by
  group

example (x y : Int) : x + y - y = x := by
  exact add_sub_cancel_right x y

example (x y z : Int) : x+y+z = x+z+y := by
  calc x+y+z
  _ = x+(y+z) := by rw[add_assoc]
  _ = x+(z+y) := by rw[add_comm y z]
  _ = x+z+y   := by rw[add_assoc]

/- ## References

The construction here is defined in a number of Algebra textbooks from the early twentieth centry. For example, see Nicolas Bourbaki, _Algebra_, (1943). The English translation of that book from 1974 has the relevant material on page 20.

-/
