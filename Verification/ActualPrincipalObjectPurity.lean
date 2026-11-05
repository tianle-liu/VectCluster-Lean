/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrincipalObjectPurity
import Verification.ActualPrincipalPurity

/-!
# Actual Principal Object Purity

For the actual transverse slice, the ambient leg of the coherent
principal-purity arrow is precisely the fixed comparison of the original
principal pair. It does not depend on a separate choice for the slice.
-/
noncomputable section
namespace Verification.ActualPrincipalObjectPurity
open CategoryTheory CategoryTheory.Limits Opposite CochainComplex
open Verification.ActualOpenChart Verification.ActualOpenGeometry Verification.ActualTransverseSlice
open Verification.ActualTransverseLocalization
universe u w
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
variable (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0) (v : ι)
variable (hf : Function.Injective (columnMap ι κ τ B))
variable (hs : FreezingLattice.Saturated (LinearMap.range (columnMap ι κ τ B)))
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ CochainComplex C ℤ)
variable (T : (Under (CommRingCat.of R))ᵒᵖ ⥤ DerivedCategory C)
variable (P : PrincipalObjectPurity.Standard R F T)

def ambientIso : T.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (ClosedSource R ι κ τ j B v))) ≅
    DerivedCategory.Q.obj (mappingCone (ActualTransverseCone.ambientOpen R ι κ τ j B v F)) :=
  P.comparison (Intermediate R ι κ τ j B v) (originalParameter R ι κ τ j B v)
    (ActualTransverseSmooth.intermediate_smooth_AS R ι κ τ j B v hB hf hs)
    (ActualTransversePairSmooth.pair_smooth_AS R ι κ τ j B hB hf hs v).2.2
    (ActualTransverseRegular.parameter_regular R ι κ τ j B hB hf v)

theorem comparison_right : (ActualPrincipalPurity.comparison_AS R ι κ τ j B hB v F T hf hs
    (PrincipalObjectPurity.arrowPurity R F T P)).hom.right =
      (ambientIso R ι κ τ j B hB v hf hs F T P).hom := by
  simp only [ActualPrincipalPurity.comparison_AS,ActualPrincipalPurity.closedArrowIso,
    PrincipalObjectPurity.arrowPurity,ambientIso,Iso.trans_hom]
  simp

#print axioms ambientIso
#print axioms comparison_right
end Verification.ActualPrincipalObjectPurity
