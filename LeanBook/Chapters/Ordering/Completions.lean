import Mathlib
import LeanBook.Chapters.Ordering.Definition
import LeanBook.Chapters.Ordering.Properties
import LeanBook.Chapters.Ordering.Maps

universe u v

namespace LeanBook
open LeanBook

/- # The Dedekind-MacNeille Completion

A completion is an embedding of a poset into a complete lattice. In this chapter we describe one such completion, the Dedekind-MacNeille Completion, which is a generalization of the Dedekind cuts method of constructing the real numbers from the rational numbers. We define `DM P` for any poset. If `P=ℚ`, the result is isomorphic to the reals with `-∞` and `∞`.

We first define `DM P` to be the family of subsets of `S ⊆ P` such that `lower (upper P) = P`. We could use Lean's subset notation, but that complicates the process of instantiating classes. So instead we use a structure.  -/

@[ext]
structure DM (P : Type u) [Poset P] where
  val : Set P
  h : lower (upper val) = val

/- We can easily show that `DM P` is a poset under the usual `⊆` ordering.  -/

instance DM.poset {P : Type u} [Poset P] : Poset (DM P) :=
  ⟨
    λ ⟨ A, hA ⟩ ⟨ B, hB ⟩ => A ⊆ B,
    by
      intro ⟨ A, _ ⟩
      exact Set.Subset.refl A,
    by
      intro ⟨ A, hA ⟩ ⟨ B, hB ⟩ h1 h2
      simp_all
      exact Set.Subset.antisymm h1 h2,
    by
      intro ⟨ A, hA ⟩ ⟨ B, hB ⟩ ⟨ C, hC ⟩ h1 h2
      exact Set.Subset.trans h1 h2
  ⟩

/- The `DM` structure forms what Davey and Priestly call a topped intersection structure, which is a Complete Lattice with a particular definition for the meet and join that we define next. -/


/- ## The Meet

We define a meet for `DM P`, which is just set-intersection taken over a subset of `DM P`. We have to show such an intersection still satisfies the `upper-lower` condition. First we define the intersection. -/

def DM.inter {P : Type u} [Poset P] (S : Set (DM P)) := { x | ∀ T ∈ S, x ∈ T.val }

/- We will need to use the fact that the interection of a family ot sets is a subset of every member of the family. -/

theorem DM.inter_sub {P : Type u} [Poset P] {S : Set (DM P)}
  : ∀ T ∈ S, inter S ⊆ T.val := by
  intro T hT x hx
  exact hx T hT

/- Now we can show the intersection is the meet. -/

theorem DM.inter_in_dm {P : Type u} [Poset P] {S : Set (DM P)}
  : lower (upper (inter S)) = inter S := by
    apply Set.eq_of_subset_of_subset
    . intro x hx T hT
      rw[←T.h]
      exact sub_low (sub_up (inter_sub T hT)) hx
    . exact sub_lu (inter S)

def DM.meet {P : Type u} [Poset P] (S : Set (DM P)) : DM P :=
  ⟨ inter S, inter_in_dm ⟩

/- To show that `DM P` is a Complete Semilattice, we need to show that this definition of `meet` is indeed a greatest lower bound. -/

theorem DM.meet_lb {P : Type u} [Poset P] :
  ∀ S : Set (DM P), IsLB S (meet S) := by
  intro S T hT
  apply DM.inter_sub
  exact hT

theorem DM.meet_greatest {P : Type u} [Poset P]
  : ∀ S : Set (DM P), ∀ w, (IsLB S w) → w ≤ meet S := by
  intro S W h
  intro x hx T hT
  exact h T hT hx

/- Now we have everything we need to instantiate the Complete Semilattice class. -/

instance DM.csl {P : Type u} [Poset P] : CompleteSemilattice (DM P) :=
  ⟨ meet, meet_lb, meet_greatest ⟩


/- ## The Join

Next we define a join, which is the intersection of sets containing the union. First we define the union. -/

def DM.union {P : Type u} [Poset P] (S : Set (DM P)) := { x | ∃ T ∈ S, x ∈ T.val }

/- Next we have an intermediate theorem analogous to the intersection theorem proved for the meet. -/

theorem DM.inter_union_dm {P : Type u} [Poset P] {S : Set (DM P)}
  : ∀ C ∈ {C : DM P| union S ⊆ C.val}, inter {C | union S ⊆ C.val} ⊆ C.val := by
    intro C hC x hx
    exact hx C hC

/- Next we show the intersection of sets containing the union is in `DM P`. -/

theorem DM.union_in_dm {P : Type u} [Poset P] {S : Set (DM P)}
  : lower (upper (inter {C | union S ⊆ C.val})) = inter {C | union S ⊆ C.val} := by
  apply Set.eq_of_subset_of_subset
  . intro x hx T hT
    rw[←T.h]
    exact sub_low (sub_up (inter_union_dm T hT)) hx
  . apply sub_lu

/- The join is then defined as follows. -/

def DM.join {P : Type u} [Poset P] (S : Set (DM P)) : DM P :=
  ⟨ inter { C | union S ⊆ C.val }, union_in_dm ⟩

/- To show `DM P` is a Complete Lattice, we need to show the join is a least upper bound, which we do in two steps. -/

theorem DM.join_ub {P : Type u} [Poset P] :
  ∀ S : Set (DM P), IsUB S (join S) := by
  intro S T hT x hx W hW
  simp[union,Set.subset_def] at hW
  exact hW x T hT hx

theorem DM.join_least {P : Type u} [Poset P]
  : ∀ S : Set (DM P), ∀ W, (IsUB S W) → join S ≤ W := by
  intro S W h x hx
  apply hx W
  intro y ⟨ Q, ⟨ h1, h2 ⟩ ⟩
  exact h Q h1 h2

/- Now we have everything we need to show `DM P` is a Complete Lattice. -/

instance DM.lattice {P : Type u} [Poset P] : CompleteLattice (DM P) :=
  ⟨ join, join_ub, join_least ⟩


/- ## Completion Map -/

theorem DM.down_is_dm {P : Type u} [Poset P] {x : P}
  : lower (upper (down x)) = down x :=
  by
    apply Set.eq_of_subset_of_subset
    . intro y hy
      exact hy x fun a a ↦ a
    . intro a ha
      simp_all[upper,lower]

def DM.make {P : Type u} [Poset P] (x : P) : DM P := ⟨ down x, down_is_dm ⟩

theorem DM.make_embed {P : Type u} [Poset P]
  : OrderEmbedding (make : P → DM P) := by
  intro x y
  constructor
  . intro h z hz
    exact Poset.trans z x y hz h
  . intro h
    simp[make,down,le_inst,Poset.le] at h
    exact h x (Poset.refl x)

-- example {P : Type u} [Poset P] (A : DM P) (hne : A.val ≠ ∅)
--   : A.val ≠ Set.univ → ∃ p : P, A ≤ DM.make p := by
--   intro h
--   simp[DM.make,down,le_inst,Poset.le]
--   by_contra hn
--   simp[Set.not_subset] at hn

--   sorry

/- ## Example -/

namespace Temp

inductive MyPoset where
  | a : MyPoset
  | b : MyPoset

open MyPoset

def myle (x y : MyPoset) := x = y

instance : Poset MyPoset :=
  ⟨ myle, by simp[myle], by simp[myle], by simp[myle] ⟩

theorem my_poset_all {x : MyPoset} : x ∈ ({a, b}: Set MyPoset) := by
  match x with
  | a => exact Set.mem_insert a {b}
  | b => exact Set.mem_insert_of_mem a rfl

def top : DM MyPoset := ⟨
  { a, b },
  by
    apply Set.eq_of_subset_of_subset
    . intro x h
      exact my_poset_all
    . intro x hx
      simp[lower,upper]
      intro y h1 h2
      match x with
      | a => exact h1
      | b => exact h2
  ⟩

def bot : DM MyPoset := ⟨
  ∅,
  by
    apply Set.eq_of_subset_of_subset
    . intro x hx
      simp[lower,upper] at hx
      have h1 := hx a
      have h2 := hx b
      rw[h1] at h2
      apply noConfusion h2
    . exact Set.empty_subset (lower (upper ∅))
⟩

example : ∃ b : DM MyPoset, ∀ x, b ≤ x := by
  use bot
  intro S y hy
  exact False.elim hy

end Temp
