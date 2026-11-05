/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LaurentScalarModel
import Verification.TorusSmooth
import Verification.LocalizedEmptyPair
import Verification.StrictLocalizedCells
import Verification.ContractedModelTransport

/-!
# Torus Contracted Model

The genuine split torus scheme has a strict model concentrated in degree
zero. This transports the ordinary torus cell along the actual empty-normal
pair comparison and the literal empty-polynomial algebra equivalence.
-/
noncomputable section
namespace Verification.TorusContractedModel
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.ContractedStrictProductInput
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D]
variable [HasZeroObject D] [HasShift D ℤ]
variable [∀ n : ℤ,(CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R : Type) [CommRing R]
variable (T : StrictLocalizedCells.TorusCells J L G R)
variable (empty : ∀ X : Scheme,IsEmpty X → IsZero (L.obj (DerivedCategory.Q.obj (G.obj X))))
variable (κ : Type) [Fintype κ]

def normalRingEquiv : TorusThomInput.NormalRing R Empty Empty κ ≃ₐ[R] OriginalTorus.Torus R κ :=
  ((MvPolynomial.isEmptyAlgEquiv (TorusThomInput.BaseRing R Empty κ) Empty).restrictScalars R).trans
    ((MvPolynomial.isEmptyAlgEquiv (OriginalTorus.Torus R κ) Empty).restrictScalars R)

def ambientIso : L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of (OriginalTorus.Torus R κ))))) ≅
    L.obj (TorusThomInput.thom R Empty Empty κ G) :=
  L.mapIso (DerivedCategory.Q.mapIso (G.mapIso (Scheme.Spec.mapIso
    (normalRingEquiv R κ).toRingEquiv.toCommRingCatIso.op))) ≪≫
      LocalizedEmptyPair.iso L G empty (TorusThomInput.NormalRing R Empty Empty κ) Empty MvPolynomial.X

def cell : StrictSingleModel.Cell J 0
    (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of (OriginalTorus.Torus R κ)))))) :=
  StrictSingleModel.ofIso (StrictSingleModel.redegree (T.cell Empty Empty κ) (by simp))
    (ambientIso L G R empty κ)

def model : ContractedModel J
    (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of (OriginalTorus.Torus R κ))))))
    (T.cell Empty Empty κ).term where
  model := StrictSingleModel.model (cell J L G R T empty κ)
  upper := by dsimp [StrictSingleModel.model,StrictSingleModel.single];infer_instance
  contraction := HomotopyEquiv.refl _

def functionEquiv : LaurentScalarModel.Coefficients R (κ→ℤ) ≃ₐ[R] OriginalTorus.Torus R κ :=
  LaurentScalarModel.coefficientEquiv R (Finsupp.linearEquivFunOnFinite ℤ ℤ κ).symm

def functionSmooth : Algebra.Smooth R (LaurentScalarModel.Coefficients R (κ→ℤ)) := by
  letI := TorusSmooth.torus_smooth R κ
  exact Algebra.Smooth.of_equiv (functionEquiv R κ).symm

def functionModel : ContractedModel J
    (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of (LaurentScalarModel.Coefficients R (κ→ℤ)))))))
    (T.cell Empty Empty κ).term :=
  ContractedModelTransport.ring J L G (functionEquiv R κ).toRingEquiv (model J L G R T empty κ)

#print axioms functionEquiv
#print axioms functionSmooth
#print axioms functionModel
#print axioms normalRingEquiv
#print axioms ambientIso
#print axioms cell
#print axioms model
end Verification.TorusContractedModel
