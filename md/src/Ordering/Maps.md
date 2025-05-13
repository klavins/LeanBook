
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Ordering/Maps.lean'>Code</a> for this chapter</span>
 ## Maps Between Posets 
```lean
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
```

<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
