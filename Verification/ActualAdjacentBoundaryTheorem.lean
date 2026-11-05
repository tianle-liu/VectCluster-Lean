/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualPrincipalPurity
import Verification.ActualAdjacentTorusBoundary
import Verification.NormalFrameInsertion

/-!
# Actual Adjacent Boundary Theorem

The manuscript's actual adjacent block under the uniform cited purity
theorem. The AS hypotheses discharge the geometric conditions internally;
the two affine comparisons and the Laurent face map are actual constructed
maps. The remaining standard line-residue identification is kept separate.
-/
namespace Verification.ActualAdjacentBoundaryTheorem
open CategoryTheory CategoryTheory.Limits Opposite CochainComplex
open Verification.ActualOpenChart Verification.ActualOpenGeometry
open Verification.ActualTransverseLocalization Verification.ExchangeTransverseSlice
open Verification.ActualTransversePurity Verification.ActualAdjacentTorusBoundary
universe u w
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
variable (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0) (v : ι)
variable (hf : Function.Injective (columnMap ι κ τ B))
variable (hs : FreezingLattice.Saturated (LinearMap.range (columnMap ι κ τ B)))
variable {D : Type*} [Category D] [Abelian D] [HasBinaryBiproducts D] [HasDerivedCategory.{w} D]
variable (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ CochainComplex D ℤ)
variable (T : (Under (CommRingCat.of R))ᵒᵖ ⥤ DerivedCategory D)
variable (purity : PrincipalPurityInterface.StandardPurity R F T)
variable [IsIso (PolynomialSectionIso.projectionMap R (Fiber (characters R ι κ τ B)) ι T)]
variable [IsIso (PolynomialSectionIso.projectionMap R (ActualTorusFace.OldTorus R ι κ τ B v)
  (LocalTransverseOpen.Old v) (shiftedTheory R F))]

noncomputable def boundary := torusBoundary R ι κ τ j B hB v F T
  (ActualPrincipalPurity.comparison_AS R ι κ τ j B hB v F T hf hs purity)

theorem boundary_formula : boundary R ι κ τ j B hB v hf hs F T purity =
    sliceBoundary R ι κ τ j B hB v F T
      (ActualPrincipalPurity.comparison_AS R ι κ τ j B hB v F T hf hs purity) ≫
        (shiftedTheory R F).map (ActualTorusFace.torusFace R ι κ τ B v).toUnder.op :=
  actual_torus_boundary R ι κ τ j B hB v F T _

variable [LinearOrder ι]
variable (orientation : ℤˣ →* End
  (T.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (Fiber (characters R ι κ τ B))))))

noncomputable def framedBoundary :=
  orientation (Equiv.Perm.sign (NormalFrameInsertion.permutation
    (Finset.univ.erase v) v (Finset.not_mem_erase v Finset.univ))) ≫
      boundary R ι κ τ j B hB v hf hs F T purity

theorem framed_boundary_formula : framedBoundary R ι κ τ j B hB v hf hs F T purity orientation =
    (orientation (-1) ^ ((Finset.univ.erase v).filter (fun i => i < v)).card) ≫
      sliceBoundary R ι κ τ j B hB v F T
        (ActualPrincipalPurity.comparison_AS R ι κ τ j B hB v F T hf hs purity) ≫
          (shiftedTheory R F).map (ActualTorusFace.torusFace R ι κ τ B v).toUnder.op := by
  rw [framedBoundary, NormalFrameInsertion.orientation_factor, boundary_formula]

#print axioms boundary
#print axioms boundary_formula
#print axioms framedBoundary
#print axioms framed_boundary_formula
end Verification.ActualAdjacentBoundaryTheorem
