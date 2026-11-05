/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathLattice
import Verification.PrimitiveLattice
import Verification.CliqueSaturation

/-!
# Primitive Bipartite Extension

Integral elimination of the manuscript's bipartite unit matching.
The retraction of the independent column family is constructed from AS;
it is not supplied as an additional splitting assumption.
-/

noncomputable section
namespace Verification.PrimitiveBipartiteExtension

open Verification.FreezingLattice Verification.PathLattice
variable {P Q F : Type*} [AddCommGroup P] [AddCommGroup Q] [AddCommGroup F]
variable [Module.Finite ℤ (Q × F)]
variable (D : Q →ₗ[ℤ] P) (E : P →ₗ[ℤ] Q) (C : P →ₗ[ℤ] F) (G : Q →ₗ[ℤ] F)
variable (J : P →ₗ[ℤ] Q) (hJ : J.comp D=LinearMap.id)
variable (hi : Function.Injective (E.prod C)) (hs : Saturated (LinearMap.range (E.prod C)))

/-- AS produces the actual coordinate projection onto the independent columns. -/
def selectedRetraction : (Q × F) →ₗ[ℤ] P :=
  (LinearMap.fst ℤ P ((Q × F) ⧸ LinearMap.range (E.prod C))).comp
    (PrimitiveLattice.primitive_columns_split_compatible (E.prod C) hi hs).choose.toLinearMap

theorem selectedRetraction_left : (selectedRetraction E C hi hs).comp (E.prod C)=LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact congrArg Prod.fst
    ((PrimitiveLattice.primitive_columns_split_compatible (E.prod C) hi hs).choose_spec x)

/-- The full column retraction, including the frozen contributions of Q. -/
def fullRetraction : (P × (Q × F)) →ₗ[ℤ] (P × Q) :=
  extensionRetraction J (selectedRetraction E C hi hs) G

include hJ in
theorem fullRetraction_left : (fullRetraction E C G J hi hs).comp (bipartiteExtension D E C G)=LinearMap.id :=
  bipartiteExtension_split D E C G J (selectedRetraction E C hi hs) hJ
    (selectedRetraction_left E C hi hs)

include hJ hi hs in
theorem full_injective : Function.Injective (bipartiteExtension D E C G) := by
  apply Function.LeftInverse.injective (g:=fullRetraction E C G J hi hs)
  intro x
  exact LinearMap.congr_fun (fullRetraction_left D E C G J hJ hi hs) x

variable [NoZeroSMulDivisors ℤ (P × (Q × F))]
include hJ hi hs in
theorem full_saturated : Saturated (LinearMap.range (bipartiteExtension D E C G)) := by
  apply CliqueSaturation.split_range_saturated (bipartiteExtension D E C G) (fullRetraction E C G J hi hs)
  intro x
  exact LinearMap.congr_fun (fullRetraction_left D E C G J hJ hi hs) x

#print axioms selectedRetraction
#print axioms selectedRetraction_left
#print axioms fullRetraction
#print axioms fullRetraction_left
#print axioms full_injective
#print axioms full_saturated

end Verification.PrimitiveBipartiteExtension
