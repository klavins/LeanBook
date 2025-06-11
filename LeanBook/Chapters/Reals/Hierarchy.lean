--import Mathlib
import Lean

import Mathlib.Algebra.Group.Defs




-- set_option trace.Meta.synthInstance true
-- set_option synthInstance.maxHeartbeats 400


/- To figure out what instances need to be made for reals, it might be easiest to follow

  mathlib4/Mathlib/Data/Real/Basic.lean

Of those classes, DCut instantiates:

`Dedekind`
  instance : Zero
  instance : One
  instance : Inhabited
  instance : LT
  instance : LE
  instance : PartialOrder
  instance : Preorder
  instance : IsTrichotomous
  instance : IsTotal
  instance : Nontrivial
  instance : NatCast
  instance : IntCast
  instance : RatCast

`Add`
  instance : HAdd
  instance : Add
  instance : AddCommSemigroup
  instance : AddSemigroup
  instance : AddZeroClass

`Subtract`
  instance : Neg
  instance : HSub
  instance : Sub
  instance : AddGroup
  instance : AddCommGroup
  instance : AddMonoidWithOne ==> Automatic: AddMonoid, AddCommMonoid

`Max`
  instance Max

`Multiply`
  instance HMul
  instance Mul
  instance MulZeroClass
  instance MulOneClass
  instance Semigroup
  instance SemigroupWithZero
  instance MulZeroOneClass
  instance CommMagma
  instance CommSemigroup
  instance Monoid
  instance CommMonoid
  instance MonoidWithZero



noncomputable instance : Inv ℝ :=

instance instNNRatCast : NNRatCast ℝ where nnratCast q := ⟨q⟩
instance instRatCast : RatCast ℝ where ratCast q := ⟨q⟩
instance commRing : CommRing ℝ where

**Extra instances to short-circuit type class resolution.**
instance instRing : Ring ℝ := by infer_instance
instance : CommSemiring ℝ := by infer_instance
instance semiring : Semiring ℝ := by infer_instance
instance : CommMonoidWithZero ℝ := by infer_instance
instance : MonoidWithZero ℝ := by infer_instance

instance : AddLeftCancelSemigroup ℝ := by infer_instance
instance : AddRightCancelSemigroup ℝ := by infer_instance

instance instZeroLEOneClass : ZeroLEOneClass ℝ where
instance instIsOrderedAddMonoid : IsOrderedAddMonoid ℝ where
instance instIsStrictOrderedRing : IsStrictOrderedRing ℝ :=
instance instIsOrderedRing : IsOrderedRing ℝ :=
instance instIsOrderedCancelAddMonoid : IsOrderedCancelAddMonoid ℝ :=
instance : Max ℝ :=
instance : Min ℝ :=
instance : DistribLattice ℝ :=

**Extra instances to short-circuit type class resolution**
instance lattice : Lattice ℝ :=
instance : SemilatticeInf ℝ :=
instance : SemilatticeSup ℝ :=

noncomputable instance linearOrder : LinearOrder ℝ :=
instance : IsDomain ℝ := IsStrictOrderedRing.isDomain
noncomputable instance instDivInvMonoid : DivInvMonoid ℝ where
noncomputable instance field : Field ℝ where

**Extra instances to short-circuit type class resolution**
noncomputable instance : DivisionRing ℝ := by infer_instance
noncomputable instance decidableLT (a b : ℝ) : Decidable (a < b) := by infer_instance
noncomputable instance decidableLE (a b : ℝ) : Decidable (a ≤ b) := by infer_instance
noncomputable instance decidableEq (a b : ℝ) : Decidable (a = b) := by infer_instance
unsafe instance : Repr ℝ where

-/




open Lean Elab Command Term Meta



def isClass (env : Environment) (clsName : Name) : Bool :=
  match env.find? clsName with
  | some _ => true
  | _ => false

def checkInstancesForType (typeName : Name) : MetaM Unit := do
  let env ← getEnv
  let type := Lean.mkConst typeName

  -- Get all classes in the environment
  let mut instancesFound : Array Name := #[]
  for (clsName, _) in env.constants.toList do
    if Lean.isClass env clsName then
      try
        let app := mkApp (← mkConstWithLevelParams clsName) type
        let inst ← synthInstance? app
        if inst.isSome then
          instancesFound := instancesFound.push clsName
      catch _ =>
        pure ()

  -- Log results
  if instancesFound.isEmpty then
    logInfo m!"No type class instances found for {typeName}."
  else
    logInfo m!"{typeName} implements the following type classes: {instancesFound}"
    for cls in instancesFound do
      logInfo m!"- {cls}"

-- Example usage
-- run_meta checkInstancesForType `Nat

def listClassesInFile (mod : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mut classes := #[]
  for (name, info) in env.constants.toList do
    if Lean.isClass env name then
        classes := classes.push name
  return classes

-- Example usage
#eval show MetaM _ from do
  logInfo m!"Finding classes"
  let classes ← listClassesInFile `Mathlib.Algebra.Group.Defs
  logInfo m!"Size is : {classes.size}"
  for cls in classes do
    logInfo m!"Class: {cls}"
  return ()
