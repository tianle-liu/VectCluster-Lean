/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RelativeProductFunctor
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-!
# Relative Product Affine

The normal affine-space product in schemes over Spec R has its literal
polynomial coordinate ring over the coefficient algebra. The coordinate
formula is proved on the actual tensor product, including the normal X_i.
-/
noncomputable section
namespace Verification.RelativeProductAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
variable (R A ι : Type) [CommRing R] [CommRing A] [Algebra R A]
attribute [local instance] MvPolynomial.algebraMvPolynomial

def affineOver : Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))

def tensorEquiv : (MvPolynomial ι R ⊗[R] A) ≃ₐ[R] MvPolynomial ι A :=
  (Algebra.TensorProduct.comm R (MvPolynomial ι R) A).trans
    ((MvPolynomial.algebraTensorAlgEquiv R A).restrictScalars R)

theorem tensor_X (i : ι) : tensorEquiv R A ι (MvPolynomial.X i ⊗ₜ[R] 1) = MvPolynomial.X i := by
  simp [tensorEquiv,MvPolynomial.algebraTensorAlgEquiv_tmul]

theorem tensor_constant (a : A) : tensorEquiv R A ι (1 ⊗ₜ[R] a) = MvPolynomial.C a := by
  simp [tensorEquiv,MvPolynomial.algebraTensorAlgEquiv_tmul,Algebra.smul_def]

def ambientIso : ((RelativeProductFunctor.normal R ι) ⨯ (affineOver R A)).left ≅
    Spec (CommRingCat.of (MvPolynomial ι A)) :=
  Over.prodLeftIsoPullback _ _ ≪≫ pullbackSpecIso R (MvPolynomial ι R) A ≪≫
    Scheme.Spec.mapIso (tensorEquiv R A ι).toRingEquiv.toCommRingCatIso.symm.op

theorem left_coordinate_map : (tensorEquiv R A ι).toAlgHom.comp Algebra.TensorProduct.includeLeft =
    MvPolynomial.mapAlgHom (Algebra.ofId R A) := by
  apply MvPolynomial.algHom_ext
  intro i
  simpa only [AlgHom.comp_apply,Algebra.TensorProduct.includeLeft_apply,MvPolynomial.mapAlgHom_apply,
    MvPolynomial.map_X,MvPolynomial.eval₂_X] using tensor_X R A ι i

def normalProjection : Spec (CommRingCat.of (MvPolynomial ι A)) ⟶ Spec (CommRingCat.of (MvPolynomial ι R)) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.map (algebraMap R A)))

theorem ambientIso_inv_fst : (ambientIso R A ι).inv ≫
    (prod.fst : RelativeProductFunctor.normal R ι ⨯ affineOver R A ⟶ RelativeProductFunctor.normal R ι).left =
      normalProjection R A ι := by
  simp only [ambientIso,Iso.trans_inv,Category.assoc,Over.prodLeftIsoPullback_inv_fst]
  dsimp only [RelativeProductFunctor.normal,affineOver,Over.mk_hom]
  rw [pullbackSpecIso_inv_fst]
  change Spec.map (CommRingCat.ofHom (tensorEquiv R A ι).toRingEquiv.toRingHom) ≫
    Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) = _
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (((tensorEquiv R A ι).toAlgHom.comp
    Algebra.TensorProduct.includeLeft).toRingHom)) = _
  rw [left_coordinate_map]
  rfl

#print axioms affineOver
#print axioms tensorEquiv
#print axioms tensor_X
#print axioms tensor_constant
#print axioms ambientIso
#print axioms left_coordinate_map
#print axioms normalProjection
#print axioms ambientIso_inv_fst
end Verification.RelativeProductAffine
