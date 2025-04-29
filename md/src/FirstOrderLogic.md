 # First Order Logic

## Limitations of Propositional Logic

The main thing missing from propositional logic is objects. For example, suppose we wanted reason about statements like:

- Every person who lives in Seattle lives in Washington.
- There exists a person who does not live in Seattle.

These statements would be difficult in propositional logic, although given that there are only a finite number of people in the world we could say things like:

- lives_in_seattle_eric → lives_in_washington_eric
- lives_in_seattle_fred → lives_in_washington_fred
- ...

where we create new propositions for every person and every statement we would like to say about that person. However, what if we wanted to reason about an infinite domain like ℕ and say things like the following?

- every natural number is either odd or even

Since there are an infinite number of natural numbers, we need an infinite number of propositions

- odd_0, even_0, odd_1, even_1, ...

## First Order Logic

First order logic (FOL) enriches propositional logic with the following elements:

- **Objects**: such as numbers, names, people, places, etc.
- **Functions**: that transform objects into other objects -- See next set of notes
- **Predicates**: that relate objects to objects
- **Quantifiers**: ∀ and ∃ that allow us to say:
  - ∀: For all objects ___
  - ∃: There exists an object such that ___
- All the connectives we have encountered so far: ∨, ∧, →, ¬, ...
- **Types**: Traditional FOL does not have types, but we will use them anyway)

For example, in the following proposition built from these elements:
```
∀ x ∃ y , f x > y
```
is read "For all x, there exists a y such that f(x) is greater than y". In this example,
- The objects x and y are presumbly numbers
- The symbol f is a function that maps numbers to numbers
- The symbol > is predicate taking two arguments and return true or false

All of this can be done easily in Lean. 
```lean
variable (f : Nat → Nat)
#check ∀ x : Nat , ∃ y : Nat , f x > y
```
 ### Objects

**Objects** in FOL can come from any agreed upon universe. Since we will be using Lean to work with first order logic, you can just assume that objects are any basic terms: numbers, strings, lists, and so on. FOL does not allow us to quantify over functions and types, only basic objects. 
 #### Example: People

For example, suppose we wanted to reason about a finite number of people. In Lean we can enumerate them with a new type: 
```lean
inductive Person where | mary | steve | ed | jolin

open Person

#check ed
```
 #### Example : Natural Numbers, Strings, Booleans, etc

Lean has a number of built inn types we can use, such as numbers, strings, and Booleans.

```lean
#check 1234
#check "uwece"
#check true
```
 # PREDICATES

A **predicate** is a `Prop` valued function.

#### Example: A Predicate on People

A predicate on Person is a function from Person into Prop, such as one which might specify whether the person lives in Seattle: 
```lean
def InSeattle (x : Person) : Prop := match x with
  | mary  | ed    => True
  | steve | jolin => False

#check InSeattle

example : InSeattle steve ∨ ¬InSeattle steve :=
  Or.inr (λ h => h)
```
 #### Example: A Predicate on ℕ

Or we might define a predicate inductively on the natural numbers. 
```lean
def is_zero(n : Nat) : Prop := match n with
  | Nat.zero => True
  | Nat.succ _ => False

#check is_zero

example : ¬is_zero 91 :=  -- is_zero 91 → False
  λ h => h

theorem t : is_zero 0 := True.intro

theorem t1 : True := True.intro
```
 # PREDICATES WITH MULTIPLE ARGUMENTS

We may define predicates to take any number or arguments, including no arguments at all. 
```lean
-- No argument predicates are just normal propositions
variable (P : Prop)
#check P

-- A one-argument predicate
variable (InWashington : Person → Prop)
#check InWashington steve

-- A two-argument predicate
variable (Age : Person → Nat → Prop)
#check Age jolin 27

-- etc.
```
 # RELATIONS

A two-argument predicate is called a relation.

`EXAMPLE` We might define a predicate on pairs of people such as 
```lean
def on_right (p q : Person) : Prop := match p with
  | mary => q = steve
  | steve => q = ed
  | ed => q = jolin
  | jolin => q = mary
```
 `EXAMPLE` We can define other predicates in terms of existing predicates. 
```lean
def next_to (p q : Person) := on_right p q ∨ on_right q p

example : next_to mary steve :=
  Or.inl (Eq.refl steve)


-- rfl == Eq.refl _
```
 # GREATER THAN IS A RELATION 
 `EXAMPLE`: "greater than" is a relation. Relations are usually represented with infix notation, but they are still just predicates. For example, in Lean, the greater-than relation on natural numbers is: 
```lean
#check @GT.gt Nat
#eval GT.gt 2 3
```
 This doesn't look very nice, so Lean defines notation:

  infix:50 " > "  => GT.gt

and we can write: 
```lean
#eval 2 > 3
```
 Similarly, >=, <, <=, != are all relations available in Lean. 
 # UNIVERSAL QUANTIFICATION

In FOL, we use the symbol ∀ to denote universal quantification. You can think of univeral quantifiaction like a potentially infinte AND:

  ∀ x P(x)   ≡    P(x₁) ∧ P(x₂) ∧ P(x₃) ∧ ...

EXAMPLE: Here's how you say "All people who live in Seattle also live in Washington":

  ∀ x : Person , InSeattle(x) → InWashington(x)

EXAMPLE: In Lean, let's say we wanted to prove that every person either lives in Seattle or does not live in Seattle. A proof of this fact has the form of a function that takes an arbtrary person x and returns a proof that that person either lives in Seattle or does not. Thus, we can say: 
```lean
example : ∀ (x : Person) , (InSeattle x) ∨ ¬(InSeattle x) :=
  λ x => match x with
  | steve => Or.inr (λ h => h)
  | mary => sorry
  | ed => sorry
  | jolin => sorry
```
 ∀ is just syntactic sugar for polymorphism. The above FOL statement can be equally well written as: 
```lean
#check (x : Person) → (InSeattle x) ∨ ¬(InSeattle x)
```
 Which highlights why we can just use a lambda to dispatch a forall. 
 # FORALL INTRODUCTION AND ELIMINATION

The universal quantifer has the introduction rule:

                    Γ ⊢ P
  `∀-intro` ————————————————————————
                Γ ⊢ ∀ x : α, P

Where x is not in the free variables of Γ. The rule states that if we can prove P in context Γ assuming x not mentioned elsewhere in Γ, then we can prove ∀ x : α, P.

We also have the elimination rule:

               Γ ⊢ ∀ x , P x
  `∃-elim` ————————————————————————
                     P t

where t is any term. This rule states that if we know P x holds for every x, then it must hold for any particular t. 
 # PROVING STATEMENTS WITH ∀

The Curry-Howard Isomorphism works for universal quantification too. We could do as we did with proposotional logic and rewrite the FOL rules as type inference. However, here we just say what it means in Lean (which amounts to the same thing).

   `∀-intro` To prove ∀ x , P x we construction a function that takes any x and returns proof of P x. This is an extension of the λ-abstraction rule.

   `∀-elim` Given a proof h of ∀ x , P x (which we recall is a λ-abstractionn) and a particular y of type α, we can prove P y by simply applying h to y. This is an extension of the λ-application rule.

For example, here is a proof that uses both of these rules: 
```lean
variable (α : Type) (P Q : α → Prop)

example : (∀ x : α, P x ∧ Q x) → ∀ y : α, P y :=
  λ h q => (h q).left
```
 # EXISTS

The ∃ quantifer is like an OR over a lot of propositions:

  ∃ x , P(x)   ≃   P(x₁) ∨ P(x₂) ∨ ....

and it has similar introduction and elimination rules:

             Γ ⊢ φ[x:=t]                Γ ⊢ ∃ x , φ     Γ, φ ⊢ ψ
  ∃-intro: ———————————————     ∃-elim: ———————————————————————————
             Γ ⊢ ∃ x, φ                        Γ ⊢ ψ

Constructively, the first rule says that if we have a proof of φ with x some term t substituted in for x, then we have a proof of ∃ x, φ.

The second says that if we have a proof of ∃ x, φ and also a proof of ψ assuming φ, then we have a proof of ψ.


 # LEAN IMPLEMENTATION OF EXISTS

In FOL, ∃ is usally just an abbreviation for as ¬∀¬. However, from a constructive point of view:

  "knowing that it is not the case that every x satisfies ¬ p is not the same as having a particular x that satisfies p." (Lean manual)

So in Lean, ∃ is defined inductively and constructively: 
```lean
namespace temp

inductive Exists {α : Type} (p : α → Prop) : Prop where
  | intro (x : α) (h : p x) : Exists p

end temp
```
 All we need to introduce an existentially quantified statement with predicate P is an element and a proof that P holds for that element.

An example use of the introduction rule is the following. Note the assumption that `α has at least one element q` is necessary.  
```lean
example (q : α) : (∀ x , P x) → (∃ x , P x) :=
  λ hp => Exists.intro q (hp q)
```
 # EXISTS ELIMINATION

The ∃-elim rule is defined in Lean as follows: 
```lean
namespace temp

theorem Exists.elim {α : Type} {P : α → Prop} {b : Prop}
   (h₁ : Exists (λ x => P x)) (h₂ : ∀ (a : α), P a → b) : b :=
  match h₁ with
  | intro a h => h₂ a h

end temp
```
 In this rule

  b is an arbitrary proposition
  h₁ is a proof of ∃ x , p x
  h₂ is a proof that ∀ a , p a → b

which allow us to conclude b 
 # EXISTS ELIMINATION EXAMPLE

For example, in 
```lean
example (h₁ : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x :=
  Exists.elim h₁
  (λ c h => Exists.intro c (And.intro h.right h.left))
```
 # EXAMPLE PROOFS 
```lean
variable (p: Type → Prop)
variable (r : Prop)

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
  (λ h => Exists.elim h (λ c h => And.intro (Exists.intro c h.left) h.right))
  (λ h => Exists.elim h.left (λ c h1 => Exists.intro c (And.intro h1 h.right)))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  sorry
```
 # SOLUTIONS 
```lean
example : ∀ (x : Person) , (S x) ∨ ¬(S x) :=
  λ x => match x with
    | mary  | ed    => Or.inl trivial
    | steve | jolin => Or.inr (λ h => False.elim h)

example : (∀ x : α, P x ∧ Q x) → ∀ y : α, P y :=
  λ h : ∀ x : α, P x ∧ Q x =>     -- →-elim
  λ y : α =>                      -- ∀-intro
  (h y).left                      -- ∃-elim with h and y (and ∧-elim-left)

example (q : α) : (∀ x , P x) → (∃ x , P x) :=
  λ h => Exists.intro q (h q)

example (h₁ : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x :=
  have h₂ := λ w : α =>                                            -- proof of ∀
             λ hpq : P w ∧ Q w  =>                                 -- proof of →
             (Exists.intro w (And.intro hpq.right hpq.left))
  Exists.elim h₁ h₂
```

<div style='height=50px'>&nbsp;</div><hr>
Copyright © Eric Klavins, 2025-Present
