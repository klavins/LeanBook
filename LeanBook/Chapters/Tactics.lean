 import Mathlib

/- # Tactics

Tactic mode is entered in a proof using the keyword `by`
-/

variable (p : Type → Prop)

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  sorry


/- ## The `intro` Tactic

Introducion applies to implications and forall statements, introducing either a new hypothesis or a new object. It takes the place of `λ h₁ h₂ ... => ...`

Note also that by using `.` and indentation, you can visually break up your proof to it is more readable. -/

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro hnep x
    sorry
  . intro hanp
    sorry

/- ## The `apply` and `exact` Tactics

The `apply` tactic applies a function, forall statement, or another theorem. It looks for arguments that match its type signature in the context and automatically uses them if possible. -/

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro h x hp
    exact h (Exists.intro x hp)
  . intro h hepx
    apply Exists.elim hepx
    intro x hpa
    exact (h x) hpa

example (p : Nat → Prop) (h : ∀ (x : Nat) , p x) : p 14 := by
  apply h

theorem my_thm (q : Prop) : q → q := id

example (q : Nat → Prop) : (∀ x, q x) → ∀ x, q x := by
  apply my_thm

/- `exact` is a variant of apply that requires you to fill in the arguments you are using. It essentially pops you out of tactic mode. It is used at the end of proofs to make things more clear and robust to changes in how other tactics in the proof are applied. -/

example (p : Nat → Prop) (h : ∀ (x : Nat) , p x) : p 14 := by
  exact h 14

/- ## The `assumption` Tactic

This tactic looks through the context to find an assumption that applies, and applies it. It is like apply but where you don't even say what to apply. -/

example (c : Type) (h : p c) : ∃ x, p x := by
  apply Exists.intro c
  assumption

/- ## Structures

Structures in Lean are a way to package data. They are a kind of inductive type, but presented differently. For example, -/

structure Point where
  x : Int
  y : Int

/- You can make new points in a variety of ways -/

def p₁ := Point.mk 1 2
def p₂ : Point := { x := 1, y := 2 }
def p₃ : Point := ⟨ 1,2 ⟩

/- ## Packaging and Exists

In Lean, And is a structure (not a simple inductive type, like I originally described). -/

#print And

example (p : Prop): p → (p ∧ p) :=
  λ hp => ⟨ hp, hp ⟩

/- This notation also works with inductive types though, as with Exists. -/

#print Exists

example (p : Type → Prop) (c : Type) : (∀ x, p x) → ∃ x, p x :=
  λ h => ⟨ c, h c ⟩

example : ∃ (p : Point) , p.x = 0 :=  by
  exact ⟨ ⟨ 0, 0 ⟩, rfl ⟩


/- ### Tactics Produce Low Level Proofs -/

theorem t (p : Type → Prop) (c : Type) : (∀ x, p x) → ∃ x, p x := by
  intro h
  exact ⟨ c, h c ⟩

#print t


/- ## Pattern Matching

You can match constructors with intro to more easily break up expressions. -/

example (p q : Prop) : p ∧ q → q := by
  intro ⟨ _, hq ⟩
  exact hq

example : (∃ x , ¬p x) → ¬ ∀ x, p x := by
  intro ⟨ x, hnp ⟩ hnap
  exact hnp (hnap x)

example (P Q : Type → Prop): (∃ x, P x ∧ Q x) → ∃ x, Q x ∧ P x := by
  intro ⟨ x, ⟨ hp, hq ⟩ ⟩
  exact ⟨ x, ⟨ hq, hp ⟩ ⟩

/- ## Getting Help with Apply?

You can ask Lean to try to find someting to apply with `apply?` -/

example : (∃ x , ¬p x) → ¬ ∀ x, p x := by
  intro ⟨ x, hnp ⟩ hnap
  apply?

/- It doesn't always work though. -/

/- ## FOL Examples Revisited

Now that we can use tactics, our First Order Logic Proofs can be made to look a little cleaner, although one might argue the use of angled brackets is harder to read. -/

variable (p: Type → Prop)
variable (r : Prop)

theorem asd : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro h x hp
    exact h (Exists.intro x hp)
  . intro hp ⟨ x, hnp ⟩
    exact hp x hnp

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  apply Iff.intro
  . intro ⟨ x, ⟨ hx, hr ⟩ ⟩
    exact ⟨ ⟨ x, hx ⟩ , hr ⟩
  . intro ⟨ ⟨ x, hx ⟩ , hr ⟩
    exact ⟨ x, ⟨ hx, hr ⟩ ⟩

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro h x hp
    exact h ⟨ x, hp ⟩
  . intro h ⟨ x, hp ⟩
    exact h x hp

/- ## The `have` and `let` Tactics

You can use `have` to record intermediate results -/

example (p q : Prop) : p ∧ q → p ∨ q := by
  intro ⟨ h1, h2 ⟩
  have hp : p := h1
  exact Or.inl hp

/- If you need an intermediate value, you should use `let`. -/

example : ∃ n , n > 0 := by
  let m := 1
  exact ⟨ m, Nat.one_pos ⟩

/- ## Cases

The cases tactic wraps around Or.elim to make proofs easier to read. -/

example (p q : Prop) : (p ∨ q) → q ∨ p  := by
  intro h
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.symm (Or.inr hq)

-- Cases doesn't always buy you much. You can just apply Or.elim.
example (p q : Prop) : (p ∨ q) → q ∨ p  := by
  intro h
  apply Or.elim h
  . intro hp
    exact Or.symm h
  . intro hq
    exact Or.symm h

/- ## Cases Works With any Inductive Ttype

Here's are some somewhat longwinded ways to prove some simple results -/

variable (P Q : Type → Prop)

example : (∃ x, P x ∧ Q x) → ∃ x, Q x ∧ P x := by
  intro h
  cases h with
  | intro x h => exact ⟨ x, And.symm h ⟩

example (p q : Prop) : (p ∧ q) → (p ∨ q) :=  by
  intro h
  cases h with
  | intro hp hq => exact Or.inl hp



/- ## The `by_cases` Tactic

The cases tactic is not to be confused with the `by_cases` tactic, which uses `classical reasoning`. -/

example (p : Prop): p ∨ ¬p := by
  by_cases h : p
  . exact Classical.em p -- assuming h : p
  . exact Classical.em p -- assuming h : ¬p


/- # The `induction` Tactic

Proof by induction works for all inductive types. It is similar to using cases, but it adds an `inductive hypothesis` where needed.

As an example, consider the natural numbers and suppose P : Nat → Prop is a property. To prove P with induction, you do :

- **BASE CASE**: P(0)
- **INDUCTIVE STEP**: ∀ n, P(n) → P(n+1) -/

def E (n : Nat) : Prop := match n with
  | Nat.zero => True
  | Nat.succ x => ¬E x

example : ∀ n : Nat, E n ∨ E n.succ := by
  intro n
  induction n with
  | zero => exact Or.inl trivial
  | succ k ih =>
    apply Or.elim ih
    . intro h1
      exact Or.inr (by exact fun a ↦ a h1)
    . intro h3
      exact Or.inl h3


/- ## Tactic Documentation

There are a lot of tactics:

  https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md

-/
