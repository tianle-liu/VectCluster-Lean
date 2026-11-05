/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualClosedThomIso
import Verification.ActualTorusFace

/-!
# Actual Adjacent Torus Boundary

The adjacent geometric boundary in the original torus coordinates.
Both affine factors are removed by proved zero-section maps and standard
A1 invariance. The resulting map is the transverse-line boundary followed
by the actual Laurent face map, derived from the actual purity square.
-/
namespace Verification.ActualAdjacentTorusBoundary
open CategoryTheory CategoryTheory.Limits Opposite CochainComplex
open Verification.ActualOpenChart Verification.ActualTransverseSlice
open Verification.ActualTransverseLocalization Verification.ExchangeTransverseSlice
open Verification.ActualTransversePurity Verification.ActualTransverseCone
universe u w
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
variable (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0) (v : ι)
variable {D : Type*} [Category D] [Abelian D] [HasBinaryBiproducts D] [HasDerivedCategory.{w} D]
variable (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ CochainComplex D ℤ)
variable (T : (Under (CommRingCat.of R))ᵒᵖ ⥤ DerivedCategory D)

noncomputable def shiftedTheory : (Under (CommRingCat.of R))ᵒᵖ ⥤ DerivedCategory D :=
  F ⋙ shiftFunctor (CochainComplex D ℤ) (1 : ℤ) ⋙ DerivedCategory.Q

variable [IsIso (PolynomialSectionIso.projectionMap R (Fiber (characters R ι κ τ B)) ι T)]
variable [IsIso (PolynomialSectionIso.projectionMap R (ActualTorusFace.OldTorus R ι κ τ B v)
  (LocalTransverseOpen.Old v) (shiftedTheory R F))]
variable (P : PurityComparison R ι κ τ j B hB v F T)

noncomputable def torusBoundary :
    T.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (Fiber (characters R ι κ τ B)))) ⟶
      (shiftedTheory R F).obj
        (op (CommRingCat.mkUnder (CommRingCat.of R) (ActualTorusFace.OldTorus R ι κ τ B v))) :=
  (ActualClosedThomIso.closedIso R ι κ τ j B hB v T).hom ≫
    adjacentBoundary R ι κ τ j B hB v F T P ≫
      (ActualTorusFace.oldIso R ι κ τ j B hB v (shiftedTheory R F)).inv

theorem actual_torus_boundary : torusBoundary R ι κ τ j B hB v F T P =
    sliceBoundary R ι κ τ j B hB v F T P ≫
      (shiftedTheory R F).map (ActualTorusFace.torusFace R ι κ τ B v).toUnder.op := by
  unfold torusBoundary
  rw [ActualClosedThomIso.closedIso_hom, ← Category.assoc, adjacent_naturality, Category.assoc]
  congr 1
  exact ActualTorusFace.actual_open_map R ι κ τ j B hB v (shiftedTheory R F)

#print axioms shiftedTheory
#print axioms torusBoundary
#print axioms actual_torus_boundary
end Verification.ActualAdjacentTorusBoundary
