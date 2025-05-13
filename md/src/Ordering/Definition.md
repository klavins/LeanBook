
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Ordering/Definition.lean'>Code</a> for this chapter</span>
 # Overview

An **order relation** on a set `A` is a predicate `A → A → Prop` that captures some notion of order. A familiar example is the the _less than_ relation on the natural numbers: 
```lean
#check 1 ≤ 2
```
 where `<` is shorthand for 
```lean
#check Nat.le       -- ℕ → ℕ → Prop
```
 `Nat.le` is an example of a **total order** on a set, meaning any two elements `x` and `y` are related (i.e. `x≤y` or `y≤x`). This need not be the case in general. For example, the subset relation `⊆` on sets is only a **partial order**, because one can find sets `A` and `B` for which neither `A ⊆ B` or `B ⊆ A`. 
```lean
namespace Temp

def A : Set ℕ := {1,2}
def B : Set ℕ := {3,4}

example : ¬A ⊆ B ∧ ¬B ⊆ A := by
  apply And.intro
  . intro h
    have h1a: 1 ∈ A := by simp[A]
    have h1b := h h1a
    simp[B] at h1b
  . intro h
    have h3b: 3 ∈ B := by simp[B]
    have h3a := h h3b
    simp[A] at h3a

end Temp
```
 You will encounter many other examples of orderings besides these two, some of which we will get to in later sections. For now, we aim like to define a hierarchy of types of orders that capture their similarities and differences, defining a general theory of orders. A side goal here is to show how Lean's heirachy machinery works from the point of view of defining a _new_ hierarchy instead of using someone else's hierarchy.

Most of this material comes from the book _Introduction to Lattices and Order_ by Davey and Priestly. 
 ## Partial Orders

A **partially ordered set** or **poset** is a set and a _less-than_ ordering relation on the set that requires pretty much the minimum one might expect from a binary relation for it to be called an ordering: the relation needs to be reflexive, anti-symmetric, and transitive (see [Relations](../Relations.html) for these definitions). Using a new Lean `class`, we define a class of types that have a less-than relation with these three properties. 
```lean
class Poset (α : Type u) where
  le : Relation α α
  refl : Refl le
  anti_sym : AntiSym le
  trans : Trans le

namespace Poset
```
 ### Example : The Natural Numbers

Lean's standard library has all of these properties defined for natural numbers. Therefore, we can assert that `ℕ` is a `poset` by instantiating the `Poset` class as follows. 
```lean
instance : Poset ℕ := ⟨ Nat.le, @Nat.le.refl, @Nat.le_antisymm, @Nat.le_trans⟩
```
 ### Example : Sets

Lean's standard library also has all of these properties defined for sets.  
```lean
instance {A: Type u} : Poset (Set A) := ⟨
  Set.Subset,
  Set.Subset.refl,
  λ _ _ h1 h2 => Set.Subset.antisymm h1 h2,
  λ _ _ _ h1 h2 => Set.Subset.trans h1 h2
⟩
```
 ## Poset Notation

Simply having the `Poset` class defined does not give us much, however. Thus, the main goal of this section is to develop theorems that, for example, apply to any `Poset`, define specific kinds of `Poset`, or that relate `Posets` to each other.

To state these theorems cleaning, we first register some notation with Lean. Instantiating the `LE` and `LT` classes in Lean's standard library allow us to use `≤`, `≥`, `<`, and `ge` on elements of our `Poset` type. Notice how these instances are declared. We have to supply a Type `A`, and require that it has been instantiated as a `Poset`. 
```lean
instance le_inst {A : Type u} [Poset A] : LE A := ⟨ Poset.le ⟩
instance lt_inst {A : Type u} [Poset A] : LT A := ⟨ λ x y => x ≤ y ∧ x ≠ y ⟩

example {A : Type u} [Poset A] (x:A) := x ≥ x
```
 ## Total Orders

A **total order** is a `Poset` with the added requirement that any two elements are comparable. 
```lean
def Comparable {P : Type u} [Poset P] (x y: P) := x ≤ y ∨ y ≤ x

class TotalOrder (T: Type u) extends Poset T where
  comp: ∀ x y : T, Comparable x y
```
 The natural numbers are a total order, which is shown via a theorem in Lean's standard library. : 
```lean
instance nat_total_order : TotalOrder ℕ :=
  ⟨ Nat.le_total ⟩
```
 Sets are not a total order, however. 
```lean
example : ∃ x y : Set ℕ, ¬Comparable x y := by
  apply Exists.intro {1}
  apply Exists.intro {2}
  simp[Comparable]
```
 ## (Meet) Semilattices

A `Semilattice` is a `Poset` for which there exists a greatest lower bound function, usually called `meet`, for every pair of points `x` and `y`. We define the notion of a greatest lower bound first. 
```lean
def IsGLBFunc {P : Type u} [Poset P] (f: P → P → P) :=
  ∀ x y, (f x y ≤ x ∧ f x y ≤ y) ∧ (∀ w, w ≤ x → w ≤ y → w ≤ f x y)
```
 Then we extend the hierarchy with a new class of orders. 
```lean
class Semilattice (L : Type u) extends Poset L where
  meet : L → L → L
  is_glb : IsGLBFunc meet
```
 For example, the natural numbers form a semilattice. So do sets. 
```lean
instance nat_semi_lattice : Semilattice ℕ :=
  ⟨
    Nat.min,
    by
      intro x y
      apply And.intro
      . exact ⟨ Nat.min_le_left x y, Nat.min_le_right x y⟩
      . intro _ h1 h2
        exact Nat.le_min_of_le_of_le h1 h2
  ⟩

instance set_semi_lattice {α : Type u}: Semilattice (Set α) :=
  ⟨
    Set.inter,
    by
      intro A B
      apply And.intro
      . apply And.intro
        . intro x hx
          exact Set.mem_of_mem_inter_left hx
        . intro x hx
          exact Set.mem_of_mem_inter_right hx
      . intro _ h1 h2 _ hc
        exact ⟨ h1 hc, h2 hc ⟩
  ⟩
```
 ## Lattices

If all pairs of elements also have a least upper bound, then the `Poset` is called a `Lattice`. The least upper bound function is called the **join**. 
```lean
def IsLUBFunc {P : Type u} [Poset P] (f: P → P → P) :=
  ∀ x y, (x ≤ f x y ∧ y ≤ f x y) ∧ (∀ w, x ≤ w → y ≤ w → f x y ≤ w)

class Lattice (L : Type u) extends Semilattice L where
  join : L → L → L
  is_lub : IsLUBFunc join
```
 Both ℕ and Sets are Lattices as well. The joing for ℕ is `Nat.max` and the join for sets is `Set.union`. 
```lean
instance nat_lattice : Lattice ℕ :=
  ⟨
    Nat.max,
    by
      intro x y
      apply And.intro
      . exact ⟨ Nat.le_max_left x y, Nat.le_max_right x y ⟩
      . intro _ h1 h2
        exact Nat.max_le_of_le_of_le h1 h2
  ⟩


instance set_lattice {α : Type u}: Lattice (Set α) :=
  ⟨
    Set.union,
    by
      intro A B
      simp
      apply And.intro
      . exact Set.union_subset_iff.mp sorry
      . intro C h1 h2 c hc
        apply Or.elim hc
        . exact λ h3 => h1 h3
        . exact λ h3 => h2 h3
  ⟩
```
 As an example of a semilattice that is not a lattice is the so-called [information ordering](./Information.html) on partial functions, decribed in a separate chapter. 
 ## Notation for Lattices

The meet and join of two elements `x` and `y` of a poset are denonted `x ⊓ y` and `x sup y`. The notation classes for these operations are called `Min` and `Max`, even though you do not have to use them for actual mins and maxes. 
```lean
instance semi_lattice_and {L : Type u} [Semilattice L] : Min L :=
  ⟨ Semilattice.meet ⟩

instance lattice_or {L : Type u} [Lattice L] : Max L :=
  ⟨ Lattice.join ⟩
```
 ## Meet and Join Example Thoerems

Here are two straightforward theorems about meets and joins that test out the definitions and notation. 
```lean
theorem meet_idempotent {L : Type u} [Semilattice L] (x : L) : x ⊓ x = x := by
  have ⟨ ⟨ h1, h2 ⟩, h3 ⟩ := Semilattice.is_glb x x
  have h4 := h3 x (by apply Poset.refl) (by apply Poset.refl)
  exact Poset.anti_sym (x ⊓ x) x h1 h4

theorem join_idempotent {L : Type u} [Lattice L] (x : L) : x ⊔ x = x := by
  have ⟨ ⟨ h1, h2 ⟩, h3 ⟩ := Lattice.is_lub x x
  have h4 := h3 x (by apply Poset.refl) (by apply Poset.refl)
  apply Poset.anti_sym (x ⊔ x) x h4 h1
```

<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
