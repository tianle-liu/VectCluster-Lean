/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualAdjacentBoundaryTheorem
import Verification.ActualContractionBoundary

/-!
# Actual Framed Contraction

The complete adjacent-block calculation for the original exchange slice:
actual AS discharges purity's geometric hypotheses; actual u=1 splitting
defines contraction; the character-fiber map defines restriction; and the
ordered original normal frame supplies precisely its permutation factor.
-/
namespace Verification.ActualFramedContraction
open CategoryTheory CategoryTheory.Limits Opposite CochainComplex
open Verification.ActualOpenChart Verification.ActualOpenGeometry
open Verification.ExchangeTransverseSlice Verification.ActualAdjacentTorusBoundary
open Verification.ActualTorusReducedRestriction
universe u w
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ] [LinearOrder ι]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
variable (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0) (v : ι)
variable (hf : Function.Injective (columnMap ι κ τ B))
variable (hs : FreezingLattice.Saturated (LinearMap.range (columnMap ι κ τ B)))
variable {D : Type*} [Category D] [Abelian D] [HasBinaryBiproducts D] [HasDerivedCategory.{w} D]
variable (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ CochainComplex D ℤ)
variable (T : (Under (CommRingCat.of R))ᵒᵖ ⥤ DerivedCategory D)
variable (purity : PrincipalPurityInterface.StandardPurity R F T)
variable [IsIso (DerivedCategory.Q.map (ActualTransverseBasepoint.lineProjection R ι κ τ B F))]
variable [IsIso (PolynomialSectionIso.projectionMap R (Fiber (characters R ι κ τ B)) ι T)]
variable [IsIso (PolynomialSectionIso.projectionMap R (ActualTorusFace.OldTorus R ι κ τ B v)
  (LocalTransverseOpen.Old v) (shiftedTheory R F))]
variable (orientation : ℤˣ →* End
  (T.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (Fiber (characters R ι κ τ B))))))
variable (M : DerivedCategory D)

theorem framed_boundary_on_sections
    (a : (shiftedTheory R F).obj (op (CommRingCat.mkUnder (CommRingCat.of R)
      (ActualTorusFace.OldTorus R ι κ τ B v))) ⟶ M) :
    ActualAdjacentBoundaryTheorem.framedBoundary R ι κ τ j B hB v hf hs F T purity orientation ≫ a =
      (orientation (-1) ^ ((Finset.univ.erase v).filter (fun i => i < v)).card) ≫
        (ActualLineContraction.thomContractionIso R ι κ τ B F j hB v T
          (ActualPrincipalPurity.comparison_AS R ι κ τ j B hB v F T hf hs purity)).hom ≫
        DerivedCategory.Q.map ((reducedRestriction R ι κ τ B v F)⟦(1 : ℤ)⟧') ≫
          ActualContractionBoundary.oldContraction R ι κ τ B v F M a := by
  rw [ActualAdjacentBoundaryTheorem.framedBoundary,NormalFrameInsertion.orientation_factor,
    ActualAdjacentBoundaryTheorem.boundary,Category.assoc,ActualContractionBoundary.boundary_on_sections]

#print axioms framed_boundary_on_sections
end Verification.ActualFramedContraction
