/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathActualWordInsert
import Verification.PathConfigurationNonincident
import Verification.PathConfigurationIncidence

/-!
# Path Actual Word Rows

All positive normal-word entries of the actual original path differential equal the literal full-rho scalar matrix, including nonincident zero blocks.
-/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.PathActualWordRows
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
attribute [local instance] Abelian.hasFiniteBiproducts
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.ExchangeOpenCover Verification.IndependentBasicOpen
open Verification.IndependentOpenCoordinates Verification.GlobalExchangeSmooth
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasBinaryBiproducts A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {Z : Type*} [Category Z] [Preadditive Z] [HasFiniteBiproducts Z]
variable [HasZeroObject Z] [HasShift Z ℤ] [∀ q : ℤ, (CategoryTheory.shiftFunctor Z q).Additive] [Pretriangulated Z]
variable (J : DerivedCategory A ⥤ Z) [J.Additive] [J.CommShift ℤ] [J.IsTriangulated]
variable (L : DerivedCategory C ⥤ Z) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)

open Verification.PathCompression Verification.PathOriginalStratumTransport
open Verification.PathOriginalIndependence Verification.PathSignedFaceUnits
open Verification.GradedSectionTotal Verification.SheafGradedLaurentResidue
open Verification.PathMilnorWittCoefficients
variable (R : Type) [CommRing R] [Nontrivial R]
variable (P : LocalizedCoordinatePurity.Standard L R G)
variable (H : LocalizedAffineThomInvariance.Standard L R G)
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (hV : LocalizedThomSections.Naturality J L G R site M N V)
variable (Cg : StandardThomContractionNormalization.Grading R site N)
variable (hCg : SheafContractionNaturality.Standard R site N Cg)
variable (O : ThomPermutationInput.Standard J L G R site M N V)
variable (W : GradedMilnorWittSheaf.Standard site N)
variable (QO : GradedMilnorWittThomOrientation.Normalization J L G R site M N V O W)
variable (MW : GradedMilnorWittLaurent.Standard R site N W Cg)

variable (T : StrictLocalizedCells.TorusCells J L G R)
variable (CR : StrictProjectiveModel.ChainRepresentability (A:=A))
variable (empty : ∀ X : Scheme,IsEmpty X → IsZero (L.obj (DerivedCategory.Q.obj (G.obj X))))
variable (Q : LocalizedIndexedPurity.Standard L R G P)
variable (K : LocalizedNormalizedFlag.Standard L R G E P)
variable (Norm : ∀ (ι : Type) [Fintype ι] [LinearOrder ι] [DecidableEq ι] (v : ι) (r : ℕ)
  (hr : Fintype.card (CoordinateFlag.Old ι v)=r),
  StandardThomContractionNormalization.Standard J L G R site M N V hV H
    (CoordinateFlag.Old ι v) r hr (K.principal ι v) Cg)

variable (Z₀ : A) (Symbols : StrictTorusSymbolInput.Standard J L G R T Z₀ M site N W V)

variable (PH : GradedMilnorWittHomogeneity.Standard site N W)
variable (SC : GradedMilnorWittStrictScalars.Standard J L G R site M N W PH V)

section Y
variable (d p : ℕ)
local notation "B" => PathOriginalYPresentation.matrix (2*d)
local notation "pos" => positive_order B y_mutable
local notation "neg" => negative_order B y_mutable
local notation "supp" => support B y_mutable
local notation "hf" => fun I hI => (PathOriginalAS.y d I hI).1
local notation "hs" => fun I hI => (PathOriginalAS.y d I hI).2
local notation "Model" => OriginalPositiveCellular.model J L G R T (Empty) (2*d) B pos neg supp hf hs E P CR empty
variable (b : Σ I : {I : PathCochains.Config (2*d) // I.val.card=p+1},
  BinaryWordCoordinates.Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates I.val.property)))
variable (i : Σ I : {I : PathCochains.Config (2*d) // I.val.card=p},
  BinaryWordCoordinates.Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates I.val.property)))
local notation "SrcIndex" => PathStrictTermIndices.yWords d p i
local notation "TgtIndex" => PathStrictTermIndices.yWords d (p+1) b
local notation "ActualEntry" => biproduct.ι (fun x : {x : PathNormalizedBasis.NormalIndex PathEndpointWords.BothNormal (2*d) // -(PathStratumGrading.degree x)= -((p+1:ℕ):ℤ)} => PathOriginalDegreeTerms.wordObject Z₀ M x.val) (TgtIndex) ≫
  (PathActualWordDifferential.yDegree J L G R T Z₀ M site N W V Symbols E P CR empty PH SC d (p+1)).inv ≫
  (Model).complex.d (-((p+1:ℕ):ℤ)) (-(p:ℤ)) ≫
  (PathActualWordDifferential.yDegree J L G R T Z₀ M site N W V Symbols E P CR empty PH SC d p).hom ≫
  biproduct.π (fun x : {x : PathNormalizedBasis.NormalIndex PathEndpointWords.BothNormal (2*d) // -(PathStratumGrading.degree x)= -((p:ℕ):ℤ)} => PathOriginalDegreeTerms.wordObject Z₀ M x.val) (SrcIndex)

theorem y_nonincident (h : ¬i.1.val.val⊆b.1.val.val) : ActualEntry=0 := by
  rw [PathActualWordDifferential.y_entry,
    PathConfigurationNonincident.y_zero J L G R T Z₀ M site N W V Symbols E P CR empty PH SC d p b.1 i.1 h]
  simp only [comp_zero,zero_comp]

def yCoefficient : GradedMilnorWittDegreeSpaces.space site N W (CommRingCat.of R)
    ((PathWeightFiltration.weight (SrcIndex).val:ℤ)-(PathWeightFiltration.weight (TgtIndex).val:ℤ)) :=
  ⟨PathMilnorWittCoefficients.realize (W.symbols (CommRingCat.of R)).toCoefficients
    (PathEndpointCoordinates.yMatrix PathCoefficientRing.g PathCoefficientRing.rho d (TgtIndex).val (SrcIndex).val),
    PathMilnorWittGradedRealization.homogeneous PH (CommRingCat.of R)
      (PathMatrixCoefficientGrading.y_entry_degree d (TgtIndex).val (SrcIndex).val)⟩

include Q Norm hCg QO MW in
theorem y_positive (hi : PathWeightFiltration.weight (SrcIndex).val≠0)
    (hk : PathWeightFiltration.weight (TgtIndex).val≠0) :
    eqToHom (show M (PathWeightFiltration.weight (TgtIndex).val:ℤ)=PathOriginalDegreeTerms.wordObject Z₀ M (TgtIndex).val from (if_neg hk).symm) ≫ (ActualEntry) ≫ eqToHom (show PathOriginalDegreeTerms.wordObject Z₀ M (SrcIndex).val=M (PathWeightFiltration.weight (SrcIndex).val:ℤ) from if_neg hi)=
    SC.scalar (PathWeightFiltration.weight (TgtIndex).val:ℤ)
      (PathWeightFiltration.weight (SrcIndex).val:ℤ) (yCoefficient R site N W PH d p b i) := by
  rcases b with ⟨⟨⟨B₁,hB₁⟩,hb⟩,kb⟩
  rcases i with ⟨⟨⟨I,hI⟩,hiCard⟩,ki⟩
  subst p
  by_cases hsub : I⊆B₁
  · obtain ⟨j,hj,hn,ha,he⟩ := PathConfigurationIncidence.insertion ⟨I,hI⟩ ⟨B₁,hB₁⟩ hb hsub
    change B₁=insert j I at he
    subst B₁
    exact PathActualWordInsert.y_positive J L G E R P H site M N V hV Cg hCg O W QO MW T CR empty Q K Norm Z₀ Symbols PH SC hI j hj ha ki kb hi hk
  · have hz := y_nonincident J L G E R P site M N V W T CR empty Z₀ Symbols PH SC d I.card
      ⟨⟨⟨B₁,hB₁⟩,hb⟩,kb⟩ ⟨⟨⟨I,hI⟩,rfl⟩,ki⟩ hsub
    rw [hz]
    have hc : yCoefficient R site N W PH d I.card
        ⟨⟨⟨B₁,hB₁⟩,hb⟩,kb⟩ ⟨⟨⟨I,hI⟩,rfl⟩,ki⟩=0 := by
      apply Subtype.ext
      change PathMilnorWittCoefficients.realize _ (PathEndpointCoordinates.yMatrix _ _ _ _ _)=0
      rw [PathLiteralIncidentEntries.y_nonincident _ _ _ _ _ hsub,map_zero]
    rw [hc,map_zero]
    simp only [comp_zero,zero_comp]

include Q Norm hCg QO MW in
theorem y_zero_target (hi : PathWeightFiltration.weight (SrcIndex).val=0) : ActualEntry=0 := by
  rcases b with ⟨⟨⟨B₁,hB₁⟩,hb⟩,kb⟩
  rcases i with ⟨⟨⟨I,hI⟩,hiCard⟩,ki⟩
  subst p
  by_cases hsub : I⊆B₁
  · obtain ⟨j,hj,hn,ha,he⟩ := PathConfigurationIncidence.insertion ⟨I,hI⟩ ⟨B₁,hB₁⟩ hb hsub
    change B₁=insert j I at he
    subst B₁
    rw [PathActualWordInsert.y_insert J L G E R P H site M N V hV Cg hCg O W QO MW T CR empty Q K Norm Z₀ Symbols PH SC hI j hj ha]
    have hdi : StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)) ki=0 := by
      have hh := (PathWordObjectTransport.y_degree d I.card ⟨⟨⟨I,hI⟩,rfl⟩,ki⟩).symm
      exact hh.trans (by exact_mod_cast hi)
    simp only [StrictPositiveColumnMatrix.entries,dif_pos hdi,comp_zero,zero_comp]
  · exact y_nonincident J L G E R P site M N V W T CR empty Z₀ Symbols PH SC d I.card
      ⟨⟨⟨B₁,hB₁⟩,hb⟩,kb⟩ ⟨⟨⟨I,hI⟩,rfl⟩,ki⟩ hsub

#print axioms y_zero_target

#print axioms y_nonincident
#print axioms yCoefficient
#print axioms y_positive
end Y
section Z
variable (n p : ℕ)
local notation "B" => PathOriginalZPresentation.matrix (n)
local notation "pos" => positive_order B z_mutable
local notation "neg" => negative_order B z_mutable
local notation "supp" => support B z_mutable
local notation "hf" => fun I hI => (PathOriginalAS.z n I hI).1
local notation "hs" => fun I hI => (PathOriginalAS.z n I hI).2
local notation "Model" => OriginalPositiveCellular.model J L G R T (Fin 1) (n) B pos neg supp hf hs E P CR empty
variable (b : Σ I : {I : PathCochains.Config (n) // I.val.card=p+1},
  BinaryWordCoordinates.Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates I.val.property)))
variable (i : Σ I : {I : PathCochains.Config (n) // I.val.card=p},
  BinaryWordCoordinates.Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates I.val.property)))
local notation "SrcIndex" => PathStrictTermIndices.zWords n p i
local notation "TgtIndex" => PathStrictTermIndices.zWords n (p+1) b
local notation "ActualEntry" => biproduct.ι (fun x : {x : PathNormalizedBasis.NormalIndex PathEndpointWords.RightNormal (n) // -(PathStratumGrading.degree x)= -((p+1:ℕ):ℤ)} => PathOriginalDegreeTerms.wordObject Z₀ M x.val) (TgtIndex) ≫
  (PathActualWordDifferential.zDegree J L G R T Z₀ M site N W V Symbols E P CR empty PH SC n (p+1)).inv ≫
  (Model).complex.d (-((p+1:ℕ):ℤ)) (-(p:ℤ)) ≫
  (PathActualWordDifferential.zDegree J L G R T Z₀ M site N W V Symbols E P CR empty PH SC n p).hom ≫
  biproduct.π (fun x : {x : PathNormalizedBasis.NormalIndex PathEndpointWords.RightNormal (n) // -(PathStratumGrading.degree x)= -((p:ℕ):ℤ)} => PathOriginalDegreeTerms.wordObject Z₀ M x.val) (SrcIndex)

theorem z_nonincident (h : ¬i.1.val.val⊆b.1.val.val) : ActualEntry=0 := by
  rw [PathActualWordDifferential.z_entry,
    PathConfigurationNonincident.z_zero J L G R T Z₀ M site N W V Symbols E P CR empty PH SC n p b.1 i.1 h]
  simp only [comp_zero,zero_comp]

def zCoefficient : GradedMilnorWittDegreeSpaces.space site N W (CommRingCat.of R)
    ((PathWeightFiltration.weight (SrcIndex).val:ℤ)-(PathWeightFiltration.weight (TgtIndex).val:ℤ)) :=
  ⟨PathMilnorWittCoefficients.realize (W.symbols (CommRingCat.of R)).toCoefficients
    (PathEndpointCoordinates.zMatrix PathCoefficientRing.g PathCoefficientRing.rho n (TgtIndex).val (SrcIndex).val),
    PathMilnorWittGradedRealization.homogeneous PH (CommRingCat.of R)
      (PathMatrixCoefficientGrading.z_entry_degree n (TgtIndex).val (SrcIndex).val)⟩

include Q Norm hCg QO MW in
theorem z_positive (hi : PathWeightFiltration.weight (SrcIndex).val≠0)
    (hk : PathWeightFiltration.weight (TgtIndex).val≠0) :
    eqToHom (show M (PathWeightFiltration.weight (TgtIndex).val:ℤ)=PathOriginalDegreeTerms.wordObject Z₀ M (TgtIndex).val from (if_neg hk).symm) ≫ (ActualEntry) ≫ eqToHom (show PathOriginalDegreeTerms.wordObject Z₀ M (SrcIndex).val=M (PathWeightFiltration.weight (SrcIndex).val:ℤ) from if_neg hi)=
    SC.scalar (PathWeightFiltration.weight (TgtIndex).val:ℤ)
      (PathWeightFiltration.weight (SrcIndex).val:ℤ) (zCoefficient R site N W PH n p b i) := by
  rcases b with ⟨⟨⟨B₁,hB₁⟩,hb⟩,kb⟩
  rcases i with ⟨⟨⟨I,hI⟩,hiCard⟩,ki⟩
  subst p
  by_cases hsub : I⊆B₁
  · obtain ⟨j,hj,hn,ha,he⟩ := PathConfigurationIncidence.insertion ⟨I,hI⟩ ⟨B₁,hB₁⟩ hb hsub
    change B₁=insert j I at he
    subst B₁
    exact PathActualWordInsert.z_positive J L G E R P H site M N V hV Cg hCg O W QO MW T CR empty Q K Norm Z₀ Symbols PH SC hI j hj ha ki kb hi hk
  · have hz := z_nonincident J L G E R P site M N V W T CR empty Z₀ Symbols PH SC n I.card
      ⟨⟨⟨B₁,hB₁⟩,hb⟩,kb⟩ ⟨⟨⟨I,hI⟩,rfl⟩,ki⟩ hsub
    rw [hz]
    have hc : zCoefficient R site N W PH n I.card
        ⟨⟨⟨B₁,hB₁⟩,hb⟩,kb⟩ ⟨⟨⟨I,hI⟩,rfl⟩,ki⟩=0 := by
      apply Subtype.ext
      change PathMilnorWittCoefficients.realize _ (PathEndpointCoordinates.zMatrix _ _ _ _ _)=0
      rw [PathLiteralIncidentEntries.z_nonincident _ _ _ _ _ hsub,map_zero]
    rw [hc,map_zero]
    simp only [comp_zero,zero_comp]

include Q Norm hCg QO MW in
theorem z_zero_target (hi : PathWeightFiltration.weight (SrcIndex).val=0) : ActualEntry=0 := by
  rcases b with ⟨⟨⟨B₁,hB₁⟩,hb⟩,kb⟩
  rcases i with ⟨⟨⟨I,hI⟩,hiCard⟩,ki⟩
  subst p
  by_cases hsub : I⊆B₁
  · obtain ⟨j,hj,hn,ha,he⟩ := PathConfigurationIncidence.insertion ⟨I,hI⟩ ⟨B₁,hB₁⟩ hb hsub
    change B₁=insert j I at he
    subst B₁
    rw [PathActualWordInsert.z_insert J L G E R P H site M N V hV Cg hCg O W QO MW T CR empty Q K Norm Z₀ Symbols PH SC hI j hj ha]
    have hdi : StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)) ki=0 := by
      have hh := (PathWordObjectTransport.z_degree n I.card ⟨⟨⟨I,hI⟩,rfl⟩,ki⟩).symm
      exact hh.trans (by exact_mod_cast hi)
    simp only [StrictPositiveColumnMatrix.entries,dif_pos hdi,comp_zero,zero_comp]
  · exact z_nonincident J L G E R P site M N V W T CR empty Z₀ Symbols PH SC n I.card
      ⟨⟨⟨B₁,hB₁⟩,hb⟩,kb⟩ ⟨⟨⟨I,hI⟩,rfl⟩,ki⟩ hsub

#print axioms z_zero_target

#print axioms z_nonincident
#print axioms zCoefficient
#print axioms z_positive
end Z

end Verification.PathActualWordRows
