import Mathlib
import LeanBook.Chapters.Ordering.Definition
import LeanBook.Chapters.Ordering.Properties

namespace LeanBook

open Poset

universe u v

/- ## Maps Between Posets -/

def OrderPreserving {P Q : Type u} [Poset P] [Poset Q] (φ : P → Q) :=
  ∀ x y : P, x ≤ y → φ x ≤ φ y

def OrderEmbedding {P Q : Type u} [Poset P] [Poset Q] (φ : P → Q) :=
  ∀ x y : P, x ≤ y ↔ φ x ≤ φ y

def OneToOne {P Q : Type u} (φ : P → Q) :=
  ∀ x y , φ x = φ y → x = y

def Onto {P Q : Type u} (φ : P → Q) :=
  ∀ y , ∃ x , φ x = y

def OrderIsomorphism {P Q : Type u} [Poset P] [Poset Q] (φ : P → Q) :=
  Onto φ ∧ OrderEmbedding φ

theorem order_pres_comp {P Q R : Type u} [Poset P] [Poset Q] [Poset R] (φ : P → Q) (ψ : Q → R)
  : OrderPreserving φ → OrderPreserving ψ → OrderPreserving (ψ ∘ φ) := by
  intro h1 h2 x y hxy
  apply h2 (φ x) (φ y)
  apply h1 x y
  exact hxy

theorem order_embed_1to1 {P Q : Type u} [Poset P] [Poset Q] (φ : P → Q)
  : OrderEmbedding φ → OneToOne φ := by
  intro h x y hxy
  apply anti_sym
  . apply (h x y).mpr
    exact eq_to_le hxy
  . apply (h y x).mpr
    exact eq_to_le (Eq.symm hxy)

theorem order_iso_bijective {P Q : Type u} [Poset P] [Poset Q] (φ : P → Q)
  : OrderIsomorphism φ → (OneToOne φ ∧ Onto φ) := by
  intro ⟨ h1, h2 ⟩
  exact ⟨ order_embed_1to1 φ h2, h1 ⟩

/- ## Examples -/

example : OrderPreserving (λ _ : ℕ => 0) := by
  intro x y h
  dsimp
  rfl

def f (n:ℕ) : Set ℕ := { x | x ≤ n }

example : OrderEmbedding f := by
  intro x y
  constructor
  . intro h
    intro z hz
    exact trans z x y hz h
  . intro h
    simp[f] at h
    exact h x (Poset.refl x)

def g (x : ℕ) : ℕ := 2*x

example : OrderEmbedding g := by
  intro x y
  constructor
  . intro h
    simp[g]
    exact h
  . intro h
    simp[g] at h
    exact h
