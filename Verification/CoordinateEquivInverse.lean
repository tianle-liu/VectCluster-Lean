/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinatePairMap

/-!
# Coordinate Equiv Inverse

The coordinate-pair isomorphism is literally the pair map induced by
the inverse ring equivalence. This records equality of the actual cone
morphisms, not just the existence of isomorphic objects.
-/
noncomputable section
namespace Verification.CoordinateEquivInverse
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {A B ι : Type} [CommRing A] [CommRing B]
variable (x : ι → A) (y : ι → B) (e : A ≃+* B) (he : ∀ i,e (x i) = y i)

include he in
theorem inverse_coordinate (i : ι) : e.symm (y i) = x i := by
  rw [← he i,e.symm_apply_apply]

universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ)

theorem relativeMap_eq :
    CoordinatePairMap.relativeMap y x e.symm.toRingHom (inverse_coordinate x y e he) G =
      (CoordinatePairEquiv.relativeIso x y e he G).hom := by
  rfl

#print axioms inverse_coordinate
#print axioms relativeMap_eq
end Verification.CoordinateEquivInverse
