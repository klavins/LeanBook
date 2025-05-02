<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Connectives.lean'>Code</a> for this chapter</span>
 # Propositional Logic Connectives

One of the remarkable things about inductive types is that the capture all of propositional logic, first order logic, and more. Thus, instead of defining _and_, _or_ and the other logical connectives as built-in operators in the Lean language, they are just defined in the standard library in terms of more primited inductive types. 
```lean
namespace Temp
```
 ## _And_ is an Inductive Type

Recall the inference rule
```
                 Γ ⊢ φ   Γ ⊢ ψ
    ∧-Intro ———————————————————
                  Γ ⊢ φ ∧ ψ
```

It states that whenever we know propositions φ and ψ, then we know φ ∧ ψ. From the point of view of types, it says that if φ and ψ are of type Prop, then so is φ ∧ ψ. In Lean we can write this as an inductive type definition as follows. 
```lean
inductive And (φ ψ : Prop) : Prop where
  | intro : φ → ψ → And φ ψ
```
 You can think of `h : And p q` as
- h has type And p q
- h is evidence that the type And p q is not empty
- h is a proof of the proposition And p q.

## A PROOF OF A SIMPLE PROPOSITION

Consider the proposition
```
p → q → And p q
```

As a type, this proposition is a function from p to q to And p q. Thus, we know that an element of this type has the form
```
λ hp => λ hq => sorry
```

For the body of this lambda abstraction, we need to `introduce` an And type, which requires proofs of p and q respectively. Using the inductive definition of And we get
```
λ hp hq => And.intro hp hq
```

```lean
def g (p q : Prop) : p → q → And p q :=
  λ hp => λ hq => And.intro hp hq
```
 ## And Eliminiation

The elimination rules for And are
```
                Γ ⊢ φ ∧ ψ                          Γ ⊢ φ ∧ ψ
  ∧-Elim-Left ——————————————         ∧-Elim-Right —————————————
                  Γ ⊢ φ                              Γ ⊢ ψ
```
which we can write in Lean as 
```lean
def And.left {p q : Prop} (hpq : And p q) :=
  match hpq with
  | And.intro hp _ => hp

def And.right {p q : Prop} (hpq : And p q) :=
  match hpq with
  | And.intro _ hq => hq
```
 # Proofs with And-Elimination

With these inference rules, we can do even more proofs: 
```lean
example (p q : Prop) : (And p q) → p :=
  λ hpq => And.left hpq

example (p q : Prop) : (And p q) → (And q p) :=
  λ hpq => And.intro hpq.right hpq.left
```
 ### Match is Enough

Note that the elimination rules above are a _convenience_ we defined to make the proof look more like propositional logic. We could also just write: 
```lean
example (p q : Prop) : (And p q) → p :=
  λ hpq => match hpq with
    | And.intro hp _ => hp
```
 This pattern suggests that with inductive types, we can think of match as a generic elimination rule.

## Or is Inductive

To introduce new OR propositions, we use the two introduction rules
```
                 Γ ⊢ φ                              Γ ⊢ ψ
 ∨-Intro-Left ———————————          ∨-Intro-Right ————————————
               Γ ⊢ φ ∨ ψ                          Γ ⊢ φ ∨ ψ
```
In Lean, we have 
```lean
inductive Or (φ ψ : Prop) : Prop where
  | inl (h : φ) : Or φ ψ
  | inr (h : ψ) : Or φ ψ
```
 And we can use this inference rule in proofs as well. 
```lean
example (p q : Prop) : And p q → Or p q :=
  λ hpq => Or.inr hpq.right
```
 ## OR ELIMINATION

Recall the inference rule
```
           Γ,p ⊢ r    Γ,q ⊢ r    Γ ⊢ p ∨ q
  ∨-Elim ————————————————————————————————————
                       Γ ⊢ r
```

It allows us to prove r given proofs that `p → r`, `q → r` and `p ∨ q`. We can define this rule in Lean with: 
```lean
def Or.elim {p q r : Prop} (hpq : Or p q) (hpr : p → r) (hqr : q → r) :=
  match hpq with
  | Or.inl hp => hpr hp
  | Or.inr hq => hqr hq
```
 # Example of and Or-Elim Proof

Here is an example proof using introduction and elimination. 
```lean
example (p q : Prop): Or p q → Or q p :=
  λ hpq => Or.elim
    hpq                               -- p ∨ q
    (λ hp => Or.inr hp)               -- p → (q ∨ p)
    (λ hq => Or.inl hq)               -- q → (q ∨ p)
```
 Once again, the elimination rule is just a convenience and the proof could be written with match.

## False is Inductive

Finally, we have `False`, which has no introduction rule, kind of like `Empty`, except we add the requirement that `False` is also type of `Prop`.  
```lean
inductive False : Prop
```
 From False we get the `Not` connective, which is just "syntactic sugar". 
```lean
def Not (p : Prop) : Prop := p → False
```
 Here is an example proof: 
```lean
example (p q : Prop): (p → q) → (Not q → Not p) :=
  λ hpq hq => λ hp => hq (hpq hp)
```
 ## False Elimination

To define the elimination rule for false
```
           Γ ⊢ ⊥
  ⊥-Elim ——————————
           Γ ⊢ p
```
we take advantage of the fact that False was defined inductively. 
```lean
def False.elim { p : Prop } (h : False) : p :=
  nomatch h
```
 Here is an example proof that from False you can conclude anything: 
```lean
example (p q : Prop): And p (Not p) → q :=
  λ h => False.elim (h.right h.left)
```
 By the way, this is another way to prove the HW1 example: 
```lean
example : False → True :=
  λ h => False.elim h
```
 ## NOTATION

The main difference between what we have defined here and Lean is that Lean defines notation like ∨ and ∧. We won't redo that entire infrastructure here. But to give a sense of it, here is how Lean defines infix notation for Or and And and Not notation.
```hs
infixr:30 " ∨ "  => Temp.Or
infixr:35 " ∧ "   => Temp.And
notation:max "¬" p:40 => Temp.Not p
```

The numbers define the precedence of the operations. So `v` has lower precedence than `∧`, which has lower precedence than `-`.

Now we can write 
```lean
end Temp -- start using Lean's propositions

example (p q : Prop): (p ∧ (¬p)) → q :=
  λ h => False.elim (h.right h.left)
```
 ## Examples

You should try to do as many of these as possible. These are borrowed from the [Theorem Proving in Lean Book](https://lean-lang.org/theorem_proving_in_lean4/title_page.html). 
```lean
variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p := sorry
example : p ∧ q ↔ q ∧ p := sorry
example : p ∨ q ↔ q ∨ p := sorry
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry
example : (p → q) → (¬q → ¬p) := sorry
```
 # REFERENCES

- https://lean-lang.org/theorem_proving_in_lean4/inductive_types.html

- Homotypy Type Theory Book
  https://homotopytypetheory.org/book/
  Chapter 5 covers inductive types



<div style='height=50px'>&nbsp;</div><hr>
Copyright © Eric Klavins, 2025-Present
