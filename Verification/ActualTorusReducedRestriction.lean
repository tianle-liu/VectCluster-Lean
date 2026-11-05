/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LaurentBasepoint
import Verification.ActualTorusFace
import Verification.ActualAdjacentTorusBoundary
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Actual Torus Reduced Restriction

The actual Laurent face preserves the coefficient projection. It therefore
induces a map on the actual reduced kernels, and its shifted inclusion square
is the contraction-then-restriction identity used by the cellular boundary.
-/
noncomputable section
namespace Verification.ActualTorusReducedRestriction
open CategoryTheory CategoryTheory.Limits Opposite CochainComplex
open Verification.ActualOpenChart Verification.ExchangeTransverseSlice
universe u
variable (R ι κ τ : Type u) [CommRing R] [Fintype κ]
variable (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) (v : ι)

abbrev OldBase := LocalTransverseOpen.OldFiber (characters R ι κ τ B) v

def fiberRestriction : OldBase R ι κ τ B v →ₐ[R] Fiber (characters R ι κ τ B) :=
  (LocalTransverseTorusFace.fiberRestriction (characters R ι κ τ B) v).restrictScalars R

theorem coefficient_square : (ActualTorusFace.torusFace R ι κ τ B v).comp
    (LaurentBasepoint.coefficient R (OldBase R ι κ τ B v)) =
      (LaurentBasepoint.coefficient R (Fiber (characters R ι κ τ B))).comp
        (fiberRestriction R ι κ τ B v) := by
  ext a
  change LocalTransverseTorusFace.torusFace (characters R ι κ τ B) v
    (algebraMap (OldBase R ι κ τ B v) (ActualTorusFace.OldTorus R ι κ τ B v) a) =
      algebraMap (Fiber (characters R ι κ τ B))
        (ActualTransverseLocalization.OpenTarget R ι κ τ B)
        (LocalTransverseTorusFace.fiberRestriction (characters R ι κ τ B) v a)
  rw [IsScalarTower.algebraMap_apply (OldBase R ι κ τ B v)
    (Polynomial (OldBase R ι κ τ B v)) (ActualTorusFace.OldTorus R ι κ τ B v),
    LocalTransverseTorusFace.torusFace_polynomial]
  exact Polynomial.aevalTower_C _ _ _

variable {D : Type*} [Category D] [Abelian D]
variable (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ D)

omit [Abelian D] in
theorem projection_square :
    LaurentBasepoint.projection R (Fiber (characters R ι κ τ B)) F ≫
      F.map (fiberRestriction R ι κ τ B v).toUnder.op =
    F.map (ActualTorusFace.torusFace R ι κ τ B v).toUnder.op ≫
      LaurentBasepoint.projection R (OldBase R ι κ τ B v) F := by
  unfold LaurentBasepoint.projection
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (fun f => F.map (AlgHom.toUnder f).op) (coefficient_square R ι κ τ B v).symm

def reducedRestriction :
    kernel (LaurentBasepoint.projection R (Fiber (characters R ι κ τ B)) F) ⟶
      kernel (LaurentBasepoint.projection R (OldBase R ι κ τ B v) F) :=
  kernel.map _ _ (F.map (ActualTorusFace.torusFace R ι κ τ B v).toUnder.op)
    (F.map (fiberRestriction R ι κ τ B v).toUnder.op) (projection_square R ι κ τ B v F)

theorem restriction_inclusion : reducedRestriction R ι κ τ B v F ≫
    kernel.ι (LaurentBasepoint.projection R (OldBase R ι κ τ B v) F) =
      kernel.ι (LaurentBasepoint.projection R (Fiber (characters R ι κ τ B)) F) ≫
        F.map (ActualTorusFace.torusFace R ι κ τ B v).toUnder.op := kernel.lift_ι _ _ _

section Derived
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : (Under (CommRingCat.of R))ᵒᵖ ⥤ CochainComplex C ℤ)

omit [HasBinaryBiproducts C] in
theorem shifted_restriction_inclusion :
    DerivedCategory.Q.map ((kernel.ι (LaurentBasepoint.projection R
      (Fiber (characters R ι κ τ B)) G))⟦(1 : ℤ)⟧') ≫
      (ActualAdjacentTorusBoundary.shiftedTheory R G).map
        (ActualTorusFace.torusFace R ι κ τ B v).toUnder.op =
    DerivedCategory.Q.map ((reducedRestriction R ι κ τ B v G)⟦(1 : ℤ)⟧') ≫
      DerivedCategory.Q.map ((kernel.ι (LaurentBasepoint.projection R
        (OldBase R ι κ τ B v) G))⟦(1 : ℤ)⟧') := by
  simpa only [CategoryTheory.Functor.map_comp] using
    (congrArg (fun f => DerivedCategory.Q.map (f⟦(1 : ℤ)⟧'))
      (restriction_inclusion R ι κ τ B v G)).symm

end Derived
#print axioms OldBase
#print axioms fiberRestriction
#print axioms coefficient_square
#print axioms projection_square
#print axioms reducedRestriction
#print axioms restriction_inclusion
#print axioms shifted_restriction_inclusion
end Verification.ActualTorusReducedRestriction
