/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalAdjacentArrow
import Verification.StrictPositiveColumnMatrix
import Verification.OriginalStrictProjectionForm

/-!
# Path Original Adjacent Biproduct

In the actual strict-cell word splittings, the original path boundary is the literal homogeneous full-rho matrix, with its integer column zero.
-/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.PathOriginalAdjacentBiproduct
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
variable {d : ℕ} {I : Finset ℕ} (hI : Admissible (2*d) I)
variable (j : ℕ) (hj : j∈Finset.Icc 1 (2*d)) (ha : Addable I j)
local notation "B" => PathOriginalYPresentation.matrix (2*d)
local notation "pos" => positive_order B y_mutable
local notation "neg" => negative_order B y_mutable
local notation "supp" => support B y_mutable
local notation "hJ" => nextAdmissible hI j hj ha
local notation "b" => PathOriginalFlagIndex.target B y_mutable hI j hj ha
local notation "v" => PathOriginalFaceIndex.selectedNormal (I:=I) j hj
local notation "Source" => GlobalNormalFrame.ZeroLayer R Empty (2*d)
  ((mutableSet (2*d) (insert j I)).erase (v).val) B
local notation "New" => PathOriginalCoefficientTransport.Fiber (I:=insert j I) R Empty B
local notation "SI" => BinaryWordCoordinates.Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI))
local notation "TI" => BinaryWordCoordinates.Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hJ))
local notation "hf" => fun I hI => (PathOriginalAS.y d I hI).1
local notation "hs" => fun I hI => (PathOriginalAS.y d I hI).2

local notation "Edge" => ActualGlobalBoundary.edgeIndex Empty (2*d) B I.card b v

local notation "idx" => PathOriginalStrictCells.yIndex hI
local notation "SourceSplit" => OriginalStrictProjectionDetection.splitSource J L G R T Empty (2*d) B
  pos neg supp hf hs I.card idx {x : ℕ // x∈I} (PathEvenEndpointTorus.FreeCoordinates hI)
  (PathOriginalStrictCells.yBase R hI) site M N V Z₀ W Symbols

local notation "FromSplit" => OriginalStrictProjectionDetection.splitSource J L G R T Empty (2*d) B
  pos neg supp hf hs (I.card+1) b {x : ℕ // x∈insert j I} (PathEvenEndpointTorus.FreeCoordinates hJ)
  (PathOriginalStrictCells.yBase R hJ) site M N V Z₀ W Symbols
local notation "positivity" => fun k : TI => ne_of_gt (StrictTorusSymbolInput.degree_positive
  (Fintype.card (Fin (I.card+1))) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hJ)) (by simp only [Fintype.card_fin]; omega) k)
local notation "Scalars" => fun (k : TI) (i : SI) (_ : StrictTorusSymbolInput.degree
  (Fintype.card (Fin I.card)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)) i≠0) => SC.scalar
    (StrictTorusSymbolInput.degree (Fintype.card (Fin (I.card+1))) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hJ)) k)
    (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)) i)
    (PathOriginalScalarColumns.yEntry R site N W PH hI j hj ha i k)
local notation "Entries" => StrictPositiveColumnMatrix.entries Z₀ M
  (Fintype.card (Fin (I.card+1))) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hJ))
  (Fintype.card (Fin I.card)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)) (positivity) (Scalars)

omit [HasBinaryBiproducts A] [HasFiniteBiproducts Z] [HasZeroObject Z]
  [∀ q : ℤ, (shiftFunctor Z q).Additive] [Pretriangulated Z] [J.CommShift ℤ] [J.IsTriangulated]
  [L.Additive] [L.CommShift ℤ] [L.IsTriangulated] [Nontrivial R] [HasShift Z ℤ] in
theorem y_candidate_matrix :
    PathOriginalAdjacentArrow.yCandidate J L G R site M N V W T Z₀ Symbols PH SC hI j hj ha=
    (FromSplit).hom ≫ biproduct.matrix (Entries) ≫ (SourceSplit).inv := by
  have hc : (fun (i : SI) (_ : StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)) i≠0) =>
      PathOriginalScalarColumns.yColumn J L G R site M N V W PH SC hI j hj ha T Z₀ Symbols i)=
      StrictPositiveColumnMatrix.column Z₀ M
        (Fintype.card (Fin (I.card+1))) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hJ))
        (Fintype.card (Fin I.card)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)) (FromSplit) (positivity) (Scalars) := by
    funext i hi
    unfold PathOriginalScalarColumns.yColumn StrictPositiveColumnMatrix.column
    apply Finset.sum_congr rfl
    intro k _
    unfold PathOriginalTargetProjection.yProjection
    rw [OriginalStrictProjectionForm.projection]
    simp only [Category.assoc]
  change StrictPositiveColumnAssembly.arrow Z₀ M (Fintype.card (Fin I.card))
    (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)) (SourceSplit) _=_
  rw [hc]
  exact StrictPositiveColumnMatrix.matrix Z₀ M
    (Fintype.card (Fin (I.card+1))) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hJ))
    (Fintype.card (Fin I.card)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)) (FromSplit) (SourceSplit) (positivity) (Scalars)

include Q Norm hCg QO MW in
theorem y_conjugate :
    (FromSplit).inv ≫ OriginalStrictLocalBlocks.block J L G R T Empty (2*d) B pos neg supp hf hs E P CR empty I.card b idx ≫ (SourceSplit).hom=
    biproduct.matrix (Entries) := by
  rw [PathOriginalAdjacentArrow.y_block J L G E R P H site M N V hV Cg hCg O W QO MW
    T CR empty Q K Norm Z₀ Symbols PH SC hI j hj ha,y_candidate_matrix]
  simp only [Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.comp_id]

#print axioms y_candidate_matrix
#print axioms y_conjugate
end Y

section Z
variable {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
variable (j : ℕ) (hj : j∈Finset.Icc 1 n) (ha : Addable I j)
local notation "B" => PathOriginalZPresentation.matrix n
local notation "pos" => positive_order B z_mutable
local notation "neg" => negative_order B z_mutable
local notation "supp" => support B z_mutable
local notation "hJ" => nextAdmissible hI j hj ha
local notation "b" => PathOriginalFlagIndex.target B z_mutable hI j hj ha
local notation "v" => PathOriginalFaceIndex.selectedNormal (I:=I) j hj
local notation "Source" => GlobalNormalFrame.ZeroLayer R (Fin 1) n
  ((mutableSet n (insert j I)).erase (v).val) B
local notation "New" => PathOriginalCoefficientTransport.Fiber (I:=insert j I) R (Fin 1) B
local notation "SI" => BinaryWordCoordinates.Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI))
local notation "TI" => BinaryWordCoordinates.Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hJ))
local notation "hf" => fun I hI => (PathOriginalAS.z n I hI).1
local notation "hs" => fun I hI => (PathOriginalAS.z n I hI).2

local notation "Edge" => ActualGlobalBoundary.edgeIndex (Fin 1) n B I.card b v

local notation "idx" => PathOriginalStrictCells.zIndex hI
local notation "SourceSplit" => OriginalStrictProjectionDetection.splitSource J L G R T (Fin 1) n B
  pos neg supp hf hs I.card idx {x : ℕ // x∈I} (PathVariableEndpointMaps.FreeCoordinates hI)
  (PathOriginalStrictCells.zBase R hI) site M N V Z₀ W Symbols

local notation "FromSplit" => OriginalStrictProjectionDetection.splitSource J L G R T (Fin 1) n B
  pos neg supp hf hs (I.card+1) b {x : ℕ // x∈insert j I} (PathVariableEndpointMaps.FreeCoordinates hJ)
  (PathOriginalStrictCells.zBase R hJ) site M N V Z₀ W Symbols
local notation "positivity" => fun k : TI => ne_of_gt (StrictTorusSymbolInput.degree_positive
  (Fintype.card (Fin (I.card+1))) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hJ)) (by simp only [Fintype.card_fin]; omega) k)
local notation "Scalars" => fun (k : TI) (i : SI) (_ : StrictTorusSymbolInput.degree
  (Fintype.card (Fin I.card)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)) i≠0) => SC.scalar
    (StrictTorusSymbolInput.degree (Fintype.card (Fin (I.card+1))) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hJ)) k)
    (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)) i)
    (PathOriginalScalarColumns.zEntry R site N W PH hI j hj ha i k)
local notation "Entries" => StrictPositiveColumnMatrix.entries Z₀ M
  (Fintype.card (Fin (I.card+1))) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hJ))
  (Fintype.card (Fin I.card)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)) (positivity) (Scalars)

omit [HasBinaryBiproducts A] [HasFiniteBiproducts Z] [HasZeroObject Z]
  [∀ q : ℤ, (shiftFunctor Z q).Additive] [Pretriangulated Z] [J.CommShift ℤ] [J.IsTriangulated]
  [L.Additive] [L.CommShift ℤ] [L.IsTriangulated] [Nontrivial R] [HasShift Z ℤ] in
theorem z_candidate_matrix :
    PathOriginalAdjacentArrow.zCandidate J L G R site M N V W T Z₀ Symbols PH SC hI j hj ha=
    (FromSplit).hom ≫ biproduct.matrix (Entries) ≫ (SourceSplit).inv := by
  have hc : (fun (i : SI) (_ : StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)) i≠0) =>
      PathOriginalScalarColumns.zColumn J L G R site M N V W PH SC hI j hj ha T Z₀ Symbols i)=
      StrictPositiveColumnMatrix.column Z₀ M
        (Fintype.card (Fin (I.card+1))) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hJ))
        (Fintype.card (Fin I.card)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)) (FromSplit) (positivity) (Scalars) := by
    funext i hi
    unfold PathOriginalScalarColumns.zColumn StrictPositiveColumnMatrix.column
    apply Finset.sum_congr rfl
    intro k _
    unfold PathOriginalTargetProjection.zProjection
    rw [OriginalStrictProjectionForm.projection]
    simp only [Category.assoc]
  change StrictPositiveColumnAssembly.arrow Z₀ M (Fintype.card (Fin I.card))
    (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)) (SourceSplit) _=_
  rw [hc]
  exact StrictPositiveColumnMatrix.matrix Z₀ M
    (Fintype.card (Fin (I.card+1))) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hJ))
    (Fintype.card (Fin I.card)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)) (FromSplit) (SourceSplit) (positivity) (Scalars)

include Q Norm hCg QO MW in
theorem z_conjugate :
    (FromSplit).inv ≫ OriginalStrictLocalBlocks.block J L G R T (Fin 1) n B pos neg supp hf hs E P CR empty I.card b idx ≫ (SourceSplit).hom=
    biproduct.matrix (Entries) := by
  rw [PathOriginalAdjacentArrow.z_block J L G E R P H site M N V hV Cg hCg O W QO MW
    T CR empty Q K Norm Z₀ Symbols PH SC hI j hj ha,z_candidate_matrix]
  simp only [Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.comp_id]

#print axioms z_candidate_matrix
#print axioms z_conjugate
end Z

end Verification.PathOriginalAdjacentBiproduct
