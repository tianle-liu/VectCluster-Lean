/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SingleCellCone

/-!
# Single Cell Cone Index

The literal new-cell coefficient at an explicitly equal target index.
This keeps integer degree transports visible in the cellular comparison.
-/
noncomputable section
namespace Verification.SingleCellConeIndex
open CategoryTheory CategoryTheory.Limits CochainComplex
open Verification.StrictSingleModel Verification.SingleCellCone
variable {A : Type*} [Category A] [Abelian A] [HasBinaryBiproducts A]
variable (P : A) (d : ℤ) (K : CochainComplex A ℤ)
variable (u : (single d P)⟦(-1 : ℤ)⟧ ⟶ K)
variable (j : ℤ) (h : d+1=j)

def headAt : ((single d P)⟦(-1 : ℤ)⟧).X j ≅ P :=
  (single d P).shiftFunctorObjXIso (-1) j d (by omega) ≪≫
    HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) d P

variable [K.IsStrictlyGE (d+1)]
theorem new_differential_at : (newIso P d K u).inv ≫ (mappingCone u).d d j ≫
    (oldIso P d K u j (by omega)).hom = (headAt P d j h).inv ≫ u.f j := by
  subst j
  exact new_differential P d K u

#print axioms headAt
#print axioms new_differential_at
end Verification.SingleCellConeIndex
