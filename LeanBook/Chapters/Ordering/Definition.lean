--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.

import Mathlib

universe u v

namespace LeanBook
open LeanBook

/- # Relations -/

def Relation (A : Type u) (B : Type v) := A → B → Prop
def Refl {A : Type u} (r : Relation A A) := ∀ x, r x x
def Symm {A : Type u} (r : Relation A A) := ∀ x y, r x y → r y x
def AntiSym {A : Type u} (r : Relation A A) := ∀ x y, r x y → r y x → x = y
def Trans {A : Type u} (r : Relation A A) := ∀ x y z, r x y → r y z → r x z

/- ## Partial Orders  -/

class Poset (α : Type u) where
  le : Relation α α
  refl : Refl le
  anti_sym : AntiSym le
  trans : Trans le

namespace Poset

instance le_inst {A : Type u} [Poset A] : LE A := ⟨ Poset.le ⟩
instance lt_inst {A : Type u} [Poset A] : LT A := ⟨ λ x y => x ≤ y ∧ x ≠ y ⟩
instance coe {A : Type u} : CoeSort (Poset A) (Type u) := ⟨ λ _ => A ⟩

/- ## Other operators -/

def up {P : Type u} [Poset P] (x : P) : Set P := λ y => x ≤ y
def down {P : Type u} [Poset P] (x : P) : Set P := λ y => y ≤ x

def Minimal {P : Type u} [Poset P] (S : Set P) (x : P) := x ∈ S ∧ ∀ y, x ≤ y
def Maximal {P : Type u} [Poset P] (S : Set P) (x : P) := x ∈ S ∧ ∀ y, y ≤ x

def is_bot {P : Type u} [Poset P] (x : P) := ∀ y, x ≤ y
def is_top {P : Type u} [Poset P] (x : P) := ∀ y, y ≤ x

/- ## Important Subsets of Posets -/

def Chain {P : Type u} [Poset P] (S : Set P) := ∀ x ∈ S, ∀ y ∈ S, x ≤ y ∨ y ≤ x
def AntiChain {P : Type u} [Poset P] (S : Set P) := ∀ x ∈ S, ∀ y ∈ S, ¬x ≤ y ∧ ¬y ≤ x

def UpSet {P : Type u} [Poset P] (S : Set P) := ∀ x, (∃ y ∈ S, y ≤ x) → x ∈ S
def DownSet {P : Type u} [Poset P] (S : Set P) := ∀ x, (∃ y ∈ S, x ≤ y) → x ∈ S

theorem up_is_up {P : Type u} [Poset P] (x : P) : UpSet (up x) := by
  intro z ⟨ y, ⟨ h1, h2 ⟩ ⟩
  simp_all[Set.mem_def,up]
  apply Poset.trans x y z h1 h2

theorem down_is_down {P : Type u} [Poset P] (x : P) : DownSet (down x) := by
  intro z ⟨ y, ⟨ h1, h2 ⟩ ⟩
  simp_all[Set.mem_def,down]
  apply Poset.trans z y x h2 h1

/- ## (Meet) Semilattices -/

def IsGLBFunc {P : Type u} [Poset P] (f: P → P → P) :=
  ∀ x y, (f x y ≤ x ∧ f x y ≤ y) ∧ (∀ w, w ≤ x → w ≤ y → w ≤ f x y)

class Semilattice (L : Type u) extends Poset L where
  meet : L → L → L
  is_glb : IsGLBFunc meet

/- ## Lattices -/

def IsLUBFunc {P : Type u} [Poset P] (f: P → P → P) :=
  ∀ x y, (x ≤ f x y ∧ y ≤ f x y) ∧ (∀ w, x ≤ w → y ≤ w → f x y ≤ w)

class Lattice (L : Type u) extends Semilattice L where
  join : L → L → L
  is_lub : IsLUBFunc join

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

theorem eq_to_le {P : Type u} [Poset P] {x y : P} : x = y → x ≤ y := by
  intro h
  rw[h]
  exact Poset.refl y

theorem order_embed_1to1 {P Q : Type u} [Poset P] [Poset Q] (φ : P → Q)
  : OrderEmbedding φ → OneToOne φ := by
  intro h x y hxy
  apply Poset.anti_sym
  . apply (h x y).mpr
    exact eq_to_le hxy
  . apply (h y x).mpr
    exact eq_to_le (Eq.symm hxy)

theorem order_iso_bijective {P Q : Type u} [Poset P] [Poset Q] (φ : P → Q)
  : OrderIsomorphism φ → (OneToOne φ ∧ Onto φ) := by
  intro ⟨ h1, h2 ⟩
  exact ⟨ order_embed_1to1 φ h2, h1 ⟩

/- ## Trees -/

class Tree (T : Type u) extends Poset T where
  has_bot : ∃ x : T, is_bot x
  down_chain : ∀ x : T, Chain (down x)
