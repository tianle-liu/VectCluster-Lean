/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinatePairMap
import Verification.ConeDerivedInverse

/-!
# Coordinate Pair Equiv Map

A coordinate-pair isomorphism and its inverse are the actual functorial
pair maps attached to the two inverse ring homomorphisms.
-/
noncomputable section
set_option maxHeartbeats 400000
namespace Verification.CoordinatePairEquivMap
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.CoordinatePurityInput
variable {A B ι : Type} [CommRing A] [CommRing B]
variable (x : ι → A) (y : ι → B) (e : A ≃+* B) (he : ∀ i,e (x i)=y i)

include he in
theorem inverse_coordinate (i : ι) : e.symm (y i)=x i := by
  rw [← he i,e.symm_apply_apply]

theorem puncture_hom : (CoordinatePairEquiv.punctureIso x y e he).hom =
    CoordinatePairMap.punctureMap y x e.symm.toRingHom (inverse_coordinate x y e he) := by
  apply (cancel_mono (puncture B ι y).ι).mp
  rw [← CoordinatePairEquiv.puncture_square,← CoordinatePairMap.puncture_square]
  rfl

theorem puncture_inv : (CoordinatePairEquiv.punctureIso x y e he).inv =
    CoordinatePairMap.punctureMap x y e.toRingHom he := by
  apply (cancel_mono (puncture A ι x).ι).mp
  rw [← CoordinatePairMap.puncture_square]
  apply (cancel_epi (CoordinatePairEquiv.punctureIso x y e he).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc,← CoordinatePairEquiv.puncture_square,Category.assoc]
  change (puncture A ι x).ι = (puncture A ι x).ι ≫
    (CoordinatePairEquiv.schemeIso e).hom ≫ (CoordinatePairEquiv.schemeIso e).inv
  simp only [Iso.hom_inv_id,Category.comp_id]

universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ)

theorem relative_hom : (CoordinatePairEquiv.relativeIso x y e he G).hom =
    CoordinatePairMap.relativeMap y x e.symm.toRingHom (inverse_coordinate x y e he) G := by
  simp only [CoordinatePairEquiv.relativeIso,ConeDerivedComparison.coneIso,asIso_hom,
    CoordinatePairMap.relativeMap,puncture_hom]
  rfl

theorem relative_inv : (CoordinatePairEquiv.relativeIso x y e he G).inv =
    CoordinatePairMap.relativeMap x y e.toRingHom he G := by
  have h := ConeDerivedInverse.inverse
    (pairArrow A ι x G) (pairArrow B ι y G)
    (G.mapIso (CoordinatePairEquiv.punctureIso x y e he))
    (G.mapIso (CoordinatePairEquiv.schemeIso e))
    (CoordinatePairEquiv.pair_square x y e he G)
  change (CoordinatePairEquiv.relativeIso x y e he G).inv = _ at h
  rw [h]
  simp only [Functor.mapIso_inv,puncture_inv,CoordinatePairMap.relativeMap]
  rfl

#print axioms inverse_coordinate
#print axioms puncture_hom
#print axioms puncture_inv
#print axioms relative_hom
#print axioms relative_inv
end Verification.CoordinatePairEquivMap
