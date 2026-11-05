/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualLineContraction
import Verification.ActualTorusReducedRestriction
import Verification.SplitHomContraction

/-!
# Actual Contraction Boundary

The original adjacent torus boundary, on coefficient sections, is the
u=1 contraction followed by the actual restriction of character fibers.
The Thom identification is constructed from standard purity and A¹-invariance;
the formula itself is proved from actual ring maps and cone boundaries.
-/
namespace Verification.ActualContractionBoundary
open CategoryTheory CategoryTheory.Limits Opposite CochainComplex
open Verification.ActualOpenChart Verification.ExchangeTransverseSlice
open Verification.ActualTransversePurity Verification.ActualAdjacentTorusBoundary
open Verification.ActualTorusReducedRestriction
universe u w
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
variable (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0) (v : ι)
variable {D : Type*} [Category D] [Abelian D] [HasBinaryBiproducts D] [HasDerivedCategory.{w} D]
variable (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ CochainComplex D ℤ)
variable (T : (Under (CommRingCat.of R))ᵒᵖ ⥤ DerivedCategory D)
variable (P : PurityComparison R ι κ τ j B hB v F T)
variable [IsIso (DerivedCategory.Q.map (ActualTransverseBasepoint.lineProjection R ι κ τ B F))]
variable [IsIso (PolynomialSectionIso.projectionMap R (Fiber (characters R ι κ τ B)) ι T)]
variable [IsIso (PolynomialSectionIso.projectionMap R (ActualTorusFace.OldTorus R ι κ τ B v)
  (LocalTransverseOpen.Old v) (shiftedTheory R F))]

theorem boundary_as_contraction : torusBoundary R ι κ τ j B hB v F T P =
    (ActualLineContraction.thomContractionIso R ι κ τ B F j hB v T P).hom ≫
      DerivedCategory.Q.map ((reducedRestriction R ι κ τ B v F)⟦(1 : ℤ)⟧') ≫
        DerivedCategory.Q.map ((kernel.ι (LaurentBasepoint.projection R
          (OldBase R ι κ τ B v) F))⟦(1 : ℤ)⟧') := by
  rw [actual_torus_boundary,ActualLineContraction.actual_slice_contraction,Category.assoc]
  exact congrArg (fun f => (ActualLineContraction.thomContractionIso R ι κ τ B F j hB v T P).hom ≫ f)
    (shifted_restriction_inclusion R ι κ τ B v F)

variable (M : DerivedCategory D)

/-- This is the actual Hom projection onto the u=1 reduced summand. -/
noncomputable def oldContraction
    (a : (shiftedTheory R F).obj (op (CommRingCat.mkUnder (CommRingCat.of R)
      (ActualTorusFace.OldTorus R ι κ τ B v))) ⟶ M) :=
  SplitHomContraction.contraction
    (LaurentBasepoint.projection R (OldBase R ι κ τ B v) F) (1 : ℤ) M a

theorem boundary_on_sections
    (a : (shiftedTheory R F).obj (op (CommRingCat.mkUnder (CommRingCat.of R)
      (ActualTorusFace.OldTorus R ι κ τ B v))) ⟶ M) :
    torusBoundary R ι κ τ j B hB v F T P ≫ a =
      (ActualLineContraction.thomContractionIso R ι κ τ B F j hB v T P).hom ≫
        DerivedCategory.Q.map ((reducedRestriction R ι κ τ B v F)⟦(1 : ℤ)⟧') ≫
          oldContraction R ι κ τ B v F M a := by
  rw [boundary_as_contraction]
  simp only [oldContraction,SplitHomContraction.contraction,Category.assoc]

#print axioms boundary_as_contraction
#print axioms oldContraction
#print axioms boundary_on_sections
end Verification.ActualContractionBoundary
