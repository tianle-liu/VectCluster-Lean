/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathStrictFrameTwist
import Verification.StrictPositiveColumnMatrix

/-!
# Path Strict Frame Matrix

Four-periodic frame changes conjugate actual finite biproduct scalar matrices, with the constant integer summands kept explicitly.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.PathStrictFrameMatrix
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.PathGradedCoefficientAction
open Verification.GradedMilnorWittDegreeSpaces
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R : Type) [CommRing R]
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (W : GradedMilnorWittSheaf.Standard site N)
variable (P : GradedMilnorWittHomogeneity.Standard site N W)
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (H : GradedMilnorWittStrictScalars.Standard J L G R site M N W P V)



open Classical Verification.StrictTorusSymbolInput Verification.BinaryWordCoordinates
attribute [local instance] Abelian.hasFiniteBiproducts
variable (Z₀ : A)

def item (I : Finset ℕ) (r n : ℕ) (i : Index n) : summand Z₀ M r n i ≅ summand Z₀ M r n i :=
  if hi : degree r n i=0 then Iso.refl _ else
    eqToIso (if_neg hi) ≪≫ PathStrictFrameTwist.twist J L G R site M N W P V H I (degree r n i) ≪≫
      (eqToIso (if_neg hi)).symm

def diagonal (I : Finset ℕ) (r n : ℕ) : (⨁ summand Z₀ M r n) ≅ (⨁ summand Z₀ M r n) :=
  biproduct.mapIso (item J L G R site M N W P V H Z₀ I r n)

omit [J.Additive] [L.Additive] in
theorem matrix (I : Finset ℕ) (j : ℕ) (hj : j∉I) (r n s m : ℕ)
    (hr : ∀ k : Index n,degree r n k≠0)
    (c : Index n → Index m → PathCoefficientRing.Coeff)
    (hc : ∀ k i,PathCoefficientGrading.Homogeneous (degree s m i-degree r n k) (c k i)) :
    (diagonal J L G R site M N W P V H Z₀ (insert j I) r n).hom ≫
      biproduct.matrix (StrictPositiveColumnMatrix.entries Z₀ M r n s m hr
        (fun k i _=>H.scalar _ _ (PathStrictFrameTwist.realized R site N W P
          (PathCoefficientRing.g^(j/2)*c k i) (PathStrictFrameTwist.signed_degree j (hc k i))))) ≫
      (diagonal J L G R site M N W P V H Z₀ I s m).hom=
    biproduct.matrix (StrictPositiveColumnMatrix.entries Z₀ M r n s m hr
      (fun k i _=>H.scalar _ _ (PathStrictFrameTwist.realized R site N W P (c k i) (hc k i)))) := by
  apply biproduct.hom_ext'
  intro k
  apply biproduct.hom_ext
  intro i
  simp only [diagonal,biproduct.mapIso_hom,Category.assoc,biproduct.map_π,
    biproduct.ι_map_assoc,biproduct.ι_matrix_assoc,biproduct.lift_π_assoc,biproduct.lift_π]
  by_cases hi : degree s m i=0
  · simp only [StrictPositiveColumnMatrix.entries,dif_pos hi,Category.comp_id,comp_zero,zero_comp]
  · simp only [StrictPositiveColumnMatrix.entries,dif_neg hi,item,dif_neg (hr k),dif_neg hi,
      Iso.trans_hom,Iso.symm_hom,eqToIso.hom,eqToIso.inv,Category.assoc,eqToHom_trans,eqToHom_refl,
      Category.id_comp,Category.comp_id,eqToHom_trans_assoc]
    simpa only [Category.assoc] using congrArg
      (fun f : M (degree r n k) ⟶ M (degree s m i) =>
        eqToHom (if_neg (hr k)) ≫ f ≫ eqToHom (if_neg hi).symm)
      (PathStrictFrameTwist.conjugate J L G R site M N W P V H I j hj
        (degree r n k) (degree s m i) (c k i) (hc k i))

#print axioms item
#print axioms diagonal
#print axioms matrix
end Verification.PathStrictFrameMatrix
