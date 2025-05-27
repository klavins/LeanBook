import Mathlib
import LeanBook.Chapters.Ordering.Completions

universe u v

namespace LeanBook.Ordering
open LeanBook.Ordering

/- # The Dedekind-MacNielle Reals

In this section we build an alternative representation of the real numbers called the Dedekind-MacNielle Reals. Unlike the construction based on the Cauchy Sequence, the Dedekind-MacNielle construction relies on an embedding of the rational numbers `ℚ` into the _Dedekind-MacNielle Completion_ of `DM ℚ`. Although this framework is unlikely to be more useful thatn the Cauchy-Construction, it does afford us an opportunity to see how an entire number system can be build from scratch, what issues arise along they way, and how to structure a library. So think of this chapter as a case study in building a foundational data structure and its associated theorems.

We begin by defining a new `Real` type to be `DM ℚ`. in order for the constructor to work, we need to register `ℚ` as a poset and a total order. -/

instance rat_poset : Poset ℚ :=
  ⟨ λ x y => x ≤ y,
    by simp,
    by intro x y h1 h2; linarith,
    by intro x y z h1 h2; linarith ⟩

instance rat_total_order : TotalOrder ℚ := ⟨ @Rat.le_total ⟩

/- Then `Real` is simply defined as: -/

abbrev Real := DM ℚ

/- ## Making Numbers

As discussed in the previous section on the Dedekind-MacNielle Completion, the map `λ x → down x` is an order-preserving embedding from `P` to `DM P`. In the present situation, this map takes a rational number and converts it to a `Real`. To make this notion clear, we define a macro called `ofRat` which wraps around `DM.make`, which you will recall uses `down` to define the order embedding from `P` to `DM P`. -/

abbrev ofRat (q : ℚ) : Real := DM.make q

/- Using `ofRat` we instantiate the two useful numbers `0` and `1`, which allow us to use the notation `0` and `1` to refer to the corresponding elements of `DM ℚ` when the context is clear. -/

instance real_zero : Zero Real := ⟨ ofRat 0 ⟩
instance real_one : One Real := ⟨ ofRat 1 ⟩

/- ## Top and Bottom

One different between the `DM ℚ` construction of the reals and others is that it automatically creates a top and bottom element, which can be thought of as `∞` and `-∞`. Thus, we simply use the `bot` and `top` provided by the fact that `DM ℚ` is a complete lattice. -/

#check (CompleteLattice.bot : Real)
#check (CompleteLattice.top : Real)

/- However, these definitions are compicated to use in proofs (such as those in the [section on addition](./RealAdd.md) showing how addition operates on `top` and `bot`), so we define versions of `top` and `bot` for `Real` and show they are equivalent to those defined for Complete Lattices. First, we have a definition for `bot`. -/

def bot : Real := ⟨ ∅, by
  simp[lower,upper]
  ext x
  constructor
  . intro h
    simp at h
    have := h (x-1)
    linarith
  . intro h
    exact False.elim h
  ⟩

theorem bot_simp : CompleteLattice.bot = bot := by
    simp[bot,CompleteLattice.sup,DM.join,DM.inter,DM.union]
    apply Set.eq_of_subset_of_subset
    . intro x hx
      simp_all
      have := hx (DM.make (x-1))
      simp[DM.make,down] at this
      linarith
    . simp

/- Similarly we have a definition for `top`. -/

def top : Real := ⟨ Set.univ, by
  simp[lower,upper]
  ext x
  constructor
  . intro _
    exact trivial
  . intro h y hy
    exact hy x
  ⟩

theorem top_simp : CompleteLattice.top = top := by
    simp[bot,CompleteSemilattice.inf,DM.meet,DM.inter,top]

/- Using these theorems we can show that `bot` and `top` behave as expected. -/

theorem bot_le (x : Real) : bot ≤ x := by
  rw[←bot_simp]
  apply CompleteLattice.is_bot

theorem top_ge (s : Real) : s ≤ top := by
  rw[←top_simp]
  apply CompleteLattice.is_top

theorem not_top_bounded {x : Real} : x ≠ top → ∃ q : ℚ, x ≤ ofRat q := by
  rw[←top_simp]
  apply DM.not_top_is_bounded

theorem not_bot_nonempty {x : Real} : x ≠ bot → ∃ v, v ∈ x.val := by
  rw[←bot_simp]
  apply DM.not_bot_to_exists
