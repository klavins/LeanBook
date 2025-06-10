import Mathlib
import LeanBook.Chapters.Appendix

import LeanBook.Chapters.Reals.Dedekind
import LeanBook.Chapters.Reals.Add
import LeanBook.Chapters.Reals.Subtract
import LeanBook.Chapters.Reals.Max
import LeanBook.Chapters.Reals.Multiply
import Lean

universe u v

namespace LeanBook.Ordering
open LeanBook.Ordering

open DCut


/- # Todo -/

#synth Inv DCut
#synth CommRing DCut
#synth Ring DCut
#synth CommSemiring DCut
#synth Semiring DCut
#synth DivInvMonoid DCut
#synth Field DCut
#synth DivisionRing DCut

#synth ZeroLEOneClass DCut
#synth IsOrderedAddMonoid DCut
#synth IsStrictOrderedRing DCut
#synth IsOrderedRing DCut
#synth IsOrderedCancelAddMonoid DCut

#synth Min DCut

#synth DistribLattice DCut
#synth Lattice DCut
#synth SemilatticeInf DCut
#synth SemilatticeSupDCut
#synth LinearOrder DCut

#synth IsDomain DCut

#synth Repr DCut

#synth NNRatCast DCut    -- Docs say: Do not use directly. Use the coercion instead.


/- # Done -/

#synth RatCast DCut
#synth Max DCut
#synth MonoidWithZero DCut
#synth CommMonoidWithZero DCut

/- # Inferred -/

#synth AddLeftCancelSemigroup DCut
#synth AddRightCancelSemigroup DCut
