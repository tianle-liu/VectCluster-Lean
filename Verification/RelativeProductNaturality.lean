/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RelativeProductPair
import Verification.CoordinatePairMap

/-!
# Relative Product Naturality

Naturality of the literal affine-coordinate identification for products
over Spec R. Both the normal variables and the coefficient morphism are
checked through the two actual pullback projections.
-/
noncomputable section
namespace Verification.RelativeProductNaturality
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.RelativeProductFunctor Verification.RelativeProductAffine
variable (R A B ι : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

variable (f : A →ₐ[R] B)

def affineMap : affineOver R B ⟶ affineOver R A :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    dsimp only [affineOver,Over.mk_hom]
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact f.commutes r)

def polynomialMap : Spec (CommRingCat.of (MvPolynomial ι B)) ⟶ Spec (CommRingCat.of (MvPolynomial ι A)) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.map f.toRingHom))

def coefficientProjection : Spec (CommRingCat.of (MvPolynomial ι A)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom MvPolynomial.C)

theorem ambientIso_inv_snd : (ambientIso R A ι).inv ≫
    (prod.snd : normal R ι ⨯ affineOver R A ⟶ affineOver R A).left = coefficientProjection A ι := by
  simp only [ambientIso,Iso.trans_inv,Category.assoc,Over.prodLeftIsoPullback_inv_snd]
  dsimp only [normal,affineOver,Over.mk_hom]
  rw [pullbackSpecIso_inv_snd]
  change Spec.map (CommRingCat.ofHom (tensorEquiv R A ι).toRingEquiv.toRingHom) ≫
    Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact tensor_constant R A ι a

theorem polynomialMap_normal : polynomialMap R A B ι f ≫ normalProjection R A ι = normalProjection R B ι := by
  unfold polynomialMap normalProjection
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  change (MvPolynomial.map f.toRingHom).comp (MvPolynomial.map (algebraMap R A)) =
    MvPolynomial.map (algebraMap R B)
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, MvPolynomial.map_C,AlgHom.coe_toRingHom]
    exact congrArg MvPolynomial.C (f.commutes r)
  · intro i
    simp only [RingHom.comp_apply, MvPolynomial.map_X]

theorem polynomialMap_coefficient : polynomialMap R A B ι f ≫ coefficientProjection A ι =
    coefficientProjection B ι ≫ Spec.map (CommRingCat.ofHom f.toRingHom) := by
  unfold polynomialMap coefficientProjection
  rw [← Spec.map_comp,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact MvPolynomial.map_C f.toRingHom a

theorem productMap_fst : (prod.map (𝟙 (normal R ι)) (affineMap R A B f)).left ≫
    (prod.fst : normal R ι ⨯ affineOver R A ⟶ normal R ι).left =
      (prod.fst : normal R ι ⨯ affineOver R B ⟶ normal R ι).left := by
  rw [← Over.comp_left, Limits.prod.map_fst, Category.comp_id]

theorem productMap_snd : (prod.map (𝟙 (normal R ι)) (affineMap R A B f)).left ≫
    (prod.snd : normal R ι ⨯ affineOver R A ⟶ affineOver R A).left =
      (prod.snd : normal R ι ⨯ affineOver R B ⟶ affineOver R B).left ≫
        Spec.map (CommRingCat.ofHom f.toRingHom) := by
  rw [← Over.comp_left, Limits.prod.map_snd]
  rfl

theorem inverse_naturality : (ambientIso R B ι).inv ≫
    (prod.map (𝟙 (normal R ι)) (affineMap R A B f)).left =
      polynomialMap R A B ι f ≫ (ambientIso R A ι).inv := by
  apply (cancel_mono (Over.prodLeftIsoPullback (normal R ι) (affineOver R A)).hom).1
  apply pullback.hom_ext
  · simp only [Category.assoc,Over.prodLeftIsoPullback_hom_fst]
    rw [productMap_fst,ambientIso_inv_fst,ambientIso_inv_fst,polynomialMap_normal]
  · simp only [Category.assoc,Over.prodLeftIsoPullback_hom_snd]
    rw [productMap_snd,ambientIso_inv_snd,← Category.assoc,ambientIso_inv_snd,polynomialMap_coefficient]

theorem ambient_naturality : (prod.map (𝟙 (normal R ι)) (affineMap R A B f)).left ≫
    (ambientIso R A ι).hom = (ambientIso R B ι).hom ≫ polynomialMap R A B ι f := by
  apply (cancel_epi (ambientIso R B ι).inv).1
  rw [← Category.assoc,inverse_naturality,Category.assoc,Iso.inv_hom_id,Category.comp_id,
    Iso.inv_hom_id_assoc]

#print axioms affineMap
#print axioms polynomialMap
#print axioms coefficientProjection
#print axioms ambientIso_inv_snd
#print axioms polynomialMap_normal
#print axioms polynomialMap_coefficient
#print axioms productMap_fst
#print axioms productMap_snd
#print axioms inverse_naturality
#print axioms ambient_naturality
end Verification.RelativeProductNaturality
