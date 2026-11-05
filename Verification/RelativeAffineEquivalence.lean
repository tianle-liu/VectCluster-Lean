/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RelativeProductNaturality

/-!
# Relative Affine Equivalence

The genuine relative affine Spec construction is functorial and sends
an algebra equivalence to an isomorphism over Spec R.
-/
noncomputable section
namespace Verification.RelativeAffineEquivalence
open CategoryTheory AlgebraicGeometry
open Verification.RelativeProductNaturality Verification.RelativeProductAffine
variable (R A B D : Type) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
variable [Algebra R A] [Algebra R B] [Algebra R D]

theorem affineMap_comp (f : A →ₐ[R] B) (g : B →ₐ[R] D) :
    affineMap R B D g ≫ affineMap R A B f = affineMap R A D (g.comp f) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom g.toRingHom) ≫ Spec.map (CommRingCat.ofHom f.toRingHom) = _
  rw [← Spec.map_comp]
  rfl

theorem affineMap_id : affineMap R A A (AlgHom.id R A) = 𝟙 (affineOver R A) := by
  apply Over.OverMorphism.ext
  change Spec.map (𝟙 (CommRingCat.of A)) = _
  rw [Spec.map_id]
  rfl

def affineIso (e : A ≃ₐ[R] B) : affineOver R B ≅ affineOver R A where
  hom := affineMap R A B e.toAlgHom
  inv := affineMap R B A e.symm.toAlgHom
  hom_inv_id := by rw [affineMap_comp]; simpa using affineMap_id R B
  inv_hom_id := by rw [affineMap_comp]; simpa using affineMap_id R A

#print axioms affineMap_comp
#print axioms affineMap_id
#print axioms affineIso
end Verification.RelativeAffineEquivalence
