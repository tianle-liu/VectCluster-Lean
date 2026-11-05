/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathWordObjectTransport
import Verification.GradedScalarDegreeTransport

/-!
# Path Word Scalar Transport

Homogeneous actual scalar entries survive the exact path word reindexing with every degree and constant-object cast removed.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.PathWordScalarTransport
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

variable (Z : A)
section Y
variable (a r s : ℕ)
variable (b : Σ I : {I : PathCochains.Config (2*a) // I.val.card=r},
  BinaryWordCoordinates.Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates I.val.property)))
variable (i : Σ I : {I : PathCochains.Config (2*a) // I.val.card=s},
  BinaryWordCoordinates.Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates I.val.property)))
local notation "WB" => PathWeightFiltration.weight (PathStrictTermIndices.yWords a r b).val
local notation "WI" => PathWeightFiltration.weight (PathStrictTermIndices.yWords a s i).val
local notation "DB" => StrictTorusSymbolInput.degree (Fintype.card (Fin r)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates b.1.val.property)) b.2
local notation "DI" => StrictTorusSymbolInput.degree (Fintype.card (Fin s)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates i.1.val.property)) i.2

omit [J.Additive] [L.Additive] in
theorem y_scalar (hb : WB≠0) (hi : WI≠0) (hdb : DB≠0) (hdi : DI≠0)
    (c : space site N W (CommRingCat.of R) (DI-DB))
    (c' : space site N W (CommRingCat.of R) ((WI:ℤ)-(WB:ℤ))) (hc : c.val=c'.val) :
    eqToHom (if_neg hb).symm ≫ (PathWordObjectTransport.yObject Z M a r b).hom ≫
      (eqToHom (if_neg hdb) ≫ H.scalar DB DI c ≫ eqToHom (if_neg hdi).symm) ≫
      (PathWordObjectTransport.yObject Z M a s i).inv ≫ eqToHom (if_neg hi)=
    H.scalar (WB:ℤ) (WI:ℤ) c' := by
  calc
    _ = (eqToHom (if_neg hb).symm ≫ (PathWordObjectTransport.yObject Z M a r b).hom ≫ eqToHom (if_neg hdb)) ≫
        H.scalar DB DI c ≫
        (eqToHom (if_neg hdi).symm ≫ (PathWordObjectTransport.yObject Z M a s i).inv ≫ eqToHom (if_neg hi)) := by
          simp only [Category.assoc]
    _ = _ := by
      rw [PathWordObjectTransport.y_positive Z M a r b hb hdb,
        PathWordObjectTransport.y_positive_inv Z M a s i hi hdi]
      exact GradedScalarDegreeTransport.scalar J L G R site M N W P V H _ _ _ _
        (PathWordObjectTransport.y_degree a r b) (PathWordObjectTransport.y_degree a s i).symm c c' hc

#print axioms y_scalar
end Y
section Z
variable (n r s : ℕ)
variable (b : Σ I : {I : PathCochains.Config (n) // I.val.card=r},
  BinaryWordCoordinates.Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates I.val.property)))
variable (i : Σ I : {I : PathCochains.Config (n) // I.val.card=s},
  BinaryWordCoordinates.Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates I.val.property)))
local notation "WB" => PathWeightFiltration.weight (PathStrictTermIndices.zWords n r b).val
local notation "WI" => PathWeightFiltration.weight (PathStrictTermIndices.zWords n s i).val
local notation "DB" => StrictTorusSymbolInput.degree (Fintype.card (Fin r)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates b.1.val.property)) b.2
local notation "DI" => StrictTorusSymbolInput.degree (Fintype.card (Fin s)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates i.1.val.property)) i.2

omit [J.Additive] [L.Additive] in
theorem z_scalar (hb : WB≠0) (hi : WI≠0) (hdb : DB≠0) (hdi : DI≠0)
    (c : space site N W (CommRingCat.of R) (DI-DB))
    (c' : space site N W (CommRingCat.of R) ((WI:ℤ)-(WB:ℤ))) (hc : c.val=c'.val) :
    eqToHom (if_neg hb).symm ≫ (PathWordObjectTransport.zObject Z M n r b).hom ≫
      (eqToHom (if_neg hdb) ≫ H.scalar DB DI c ≫ eqToHom (if_neg hdi).symm) ≫
      (PathWordObjectTransport.zObject Z M n s i).inv ≫ eqToHom (if_neg hi)=
    H.scalar (WB:ℤ) (WI:ℤ) c' := by
  calc
    _ = (eqToHom (if_neg hb).symm ≫ (PathWordObjectTransport.zObject Z M n r b).hom ≫ eqToHom (if_neg hdb)) ≫
        H.scalar DB DI c ≫
        (eqToHom (if_neg hdi).symm ≫ (PathWordObjectTransport.zObject Z M n s i).inv ≫ eqToHom (if_neg hi)) := by
          simp only [Category.assoc]
    _ = _ := by
      rw [PathWordObjectTransport.z_positive Z M n r b hb hdb,
        PathWordObjectTransport.z_positive_inv Z M n s i hi hdi]
      exact GradedScalarDegreeTransport.scalar J L G R site M N W P V H _ _ _ _
        (PathWordObjectTransport.z_degree n r b) (PathWordObjectTransport.z_degree n s i).symm c c' hc

#print axioms z_scalar
end Z

end Verification.PathWordScalarTransport
