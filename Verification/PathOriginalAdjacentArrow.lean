/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalStrictBlockColumns
import Verification.PathOriginalScalarColumns
import Verification.OriginalFiberProjectionDetection
import Verification.OriginalStrictBlockIndexTransport
import Verification.StrictPositiveColumnAssembly

/-!
# Path Original Adjacent Arrow

The literal original path boundary block equals its homogeneous MW scalar-column realization as a strict-sheaf arrow, hence for every strict coefficient object.
-/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.PathOriginalAdjacentArrow
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
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

def yCandidate : (StrictLocalizedCells.localCell J L G R T Empty (2*d) B pos neg supp hf hs (I.card+1) b).term ⟶ (StrictLocalizedCells.localCell J L G R T Empty (2*d) B pos neg supp hf hs I.card idx).term :=
  StrictPositiveColumnAssembly.arrow Z₀ M (Fintype.card (Fin I.card)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI))
    (SourceSplit) (fun i _ => PathOriginalScalarColumns.yColumn J L G R site M N V W PH SC hI j hj ha T Z₀ Symbols i)

omit [HasBinaryBiproducts A] [HasFiniteBiproducts Z] [HasZeroObject Z]
  [∀ q : ℤ, (shiftFunctor Z q).Additive] [Pretriangulated Z] [J.CommShift ℤ] [J.IsTriangulated]
  [L.Additive] [L.CommShift ℤ] [L.IsTriangulated] [Nontrivial R] [HasShift Z ℤ] in
theorem y_projection (i : SI) (hi : StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)) i≠0) :
    yCandidate J L G R site M N V W T Z₀ Symbols PH SC hI j hj ha ≫ OriginalCoordinateProjectionSymbols.projection J L G R T Empty (2*d) B pos neg supp hf hs I.card idx {x : ℕ // x∈I} (PathEvenEndpointTorus.FreeCoordinates hI) (PathOriginalStrictCells.yBase R hI) site M N V Z₀ W Symbols i hi = PathOriginalScalarColumns.yColumn J L G R site M N V W PH SC hI j hj ha T Z₀ Symbols i := by
  simpa only [yCandidate,OriginalStrictProjectionDetection.splitSource,
    OriginalCoordinateProjectionSymbols.projection,StrictTorusSymbolRedegree.split,
    StrictTorusSymbolRedegree.projection,StrictTorusSymbolInput.positiveProjection,
    StrictTorusSymbolInput.projection,Iso.trans_hom,Category.assoc] using
    StrictPositiveColumnAssembly.positive Z₀ M (Fintype.card (Fin I.card)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI))
      (SourceSplit) (fun i _ => PathOriginalScalarColumns.yColumn J L G R site M N V W PH SC hI j hj ha T Z₀ Symbols i) i hi

include Q Norm hCg QO MW in
theorem y_block :
    OriginalStrictLocalBlocks.block J L G R T Empty (2*d) B pos neg supp hf hs E P CR empty I.card b idx=
    yCandidate J L G R site M N V W T Z₀ Symbols PH SC hI j hj ha := by
  apply OriginalFiberProjectionDetection.detect J L G R T Empty (2*d) B pos neg supp hf hs
    (I.card+1) I.card b idx {x : ℕ // x∈insert j I} (PathEvenEndpointTorus.FreeCoordinates hJ) {x : ℕ // x∈I} (PathEvenEndpointTorus.FreeCoordinates hI)
    (PathOriginalStrictCells.yBase R hJ) (PathOriginalStrictCells.yBase R hI)
    site M N V Z₀ W Symbols H hV v (by omega)
  intro i hi
  change OriginalFiberTotalEvaluation.total J L G R T Empty (2*d) B pos neg supp hf hs (I.card+1) b site M N V W
    (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)) i) (OriginalStrictLocalBlocks.block J L G R T Empty (2*d) B pos neg supp hf hs E P CR empty I.card b idx ≫ OriginalCoordinateProjectionSymbols.projection J L G R T Empty (2*d) B pos neg supp hf hs I.card idx {x : ℕ // x∈I} (PathEvenEndpointTorus.FreeCoordinates hI) (PathOriginalStrictCells.yBase R hI) site M N V Z₀ W Symbols i hi)=
    OriginalFiberTotalEvaluation.total J L G R T Empty (2*d) B pos neg supp hf hs (I.card+1) b site M N V W
    (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)) i) (yCandidate J L G R site M N V W T Z₀ Symbols PH SC hI j hj ha ≫ OriginalCoordinateProjectionSymbols.projection J L G R T Empty (2*d) B pos neg supp hf hs I.card idx {x : ℕ // x∈I} (PathEvenEndpointTorus.FreeCoordinates hI) (PathOriginalStrictCells.yBase R hI) site M N V Z₀ W Symbols i hi)
  rw [y_projection]
  rw [←OriginalStrictBlockIndexTransport.codomain J L G R T Empty (2*d) B pos neg supp hf hs E P CR empty I.card b Edge idx (PathOriginalEdgeProjection.y_edge_eq hI j hj ha).symm]
  simp only [Category.assoc]
  change OriginalFiberTotalEvaluation.total J L G R T Empty (2*d) B pos neg supp hf hs (I.card+1) b site M N V W
    (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)) i) (OriginalStrictLocalBlocks.block J L G R T Empty (2*d) B pos neg supp hf hs E P CR empty I.card b Edge ≫
      PathOriginalEdgeProjection.yProjection J L G R site M N V W hI j hj ha T Z₀ Symbols i hi)=
    OriginalFiberTotalEvaluation.total J L G R T Empty (2*d) B pos neg supp hf hs (I.card+1) b site M N V W
      (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)) i) (PathOriginalScalarColumns.yColumn J L G R site M N V W PH SC hI j hj ha T Z₀ Symbols i)
  rw [PathOriginalScalarColumns.y_value J L G R H site M N V hV W Cg MW PH SC hI j hj ha T Z₀ Symbols]
  apply (PathYWordBasis.basis R hJ site N W Cg).symm.injective
  funext k
  rw [AddEquiv.symm_apply_apply]
  exact (PathOriginalStrictBlockColumns.y_column J L G E R P H site M N V hV Cg hCg O W QO MW
    T CR empty Q K Norm Z₀ Symbols hI j hj ha i hi k).trans (by
      simp only [PathActualColumnDegrees.yEntry,map_mul,map_pow,PathMilnorWittCoefficients.realize_g])

#print axioms yCandidate
#print axioms y_projection
#print axioms y_block
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

def zCandidate : (StrictLocalizedCells.localCell J L G R T (Fin 1) n B pos neg supp hf hs (I.card+1) b).term ⟶ (StrictLocalizedCells.localCell J L G R T (Fin 1) n B pos neg supp hf hs I.card idx).term :=
  StrictPositiveColumnAssembly.arrow Z₀ M (Fintype.card (Fin I.card)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI))
    (SourceSplit) (fun i _ => PathOriginalScalarColumns.zColumn J L G R site M N V W PH SC hI j hj ha T Z₀ Symbols i)

omit [HasBinaryBiproducts A] [HasFiniteBiproducts Z] [HasZeroObject Z]
  [∀ q : ℤ, (shiftFunctor Z q).Additive] [Pretriangulated Z] [J.CommShift ℤ] [J.IsTriangulated]
  [L.Additive] [L.CommShift ℤ] [L.IsTriangulated] [Nontrivial R] [HasShift Z ℤ] in
theorem z_projection (i : SI) (hi : StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)) i≠0) :
    zCandidate J L G R site M N V W T Z₀ Symbols PH SC hI j hj ha ≫ OriginalCoordinateProjectionSymbols.projection J L G R T (Fin 1) n B pos neg supp hf hs I.card idx {x : ℕ // x∈I} (PathVariableEndpointMaps.FreeCoordinates hI) (PathOriginalStrictCells.zBase R hI) site M N V Z₀ W Symbols i hi = PathOriginalScalarColumns.zColumn J L G R site M N V W PH SC hI j hj ha T Z₀ Symbols i := by
  simpa only [zCandidate,OriginalStrictProjectionDetection.splitSource,
    OriginalCoordinateProjectionSymbols.projection,StrictTorusSymbolRedegree.split,
    StrictTorusSymbolRedegree.projection,StrictTorusSymbolInput.positiveProjection,
    StrictTorusSymbolInput.projection,Iso.trans_hom,Category.assoc] using
    StrictPositiveColumnAssembly.positive Z₀ M (Fintype.card (Fin I.card)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI))
      (SourceSplit) (fun i _ => PathOriginalScalarColumns.zColumn J L G R site M N V W PH SC hI j hj ha T Z₀ Symbols i) i hi

include Q Norm hCg QO MW in
theorem z_block :
    OriginalStrictLocalBlocks.block J L G R T (Fin 1) n B pos neg supp hf hs E P CR empty I.card b idx=
    zCandidate J L G R site M N V W T Z₀ Symbols PH SC hI j hj ha := by
  apply OriginalFiberProjectionDetection.detect J L G R T (Fin 1) n B pos neg supp hf hs
    (I.card+1) I.card b idx {x : ℕ // x∈insert j I} (PathVariableEndpointMaps.FreeCoordinates hJ) {x : ℕ // x∈I} (PathVariableEndpointMaps.FreeCoordinates hI)
    (PathOriginalStrictCells.zBase R hJ) (PathOriginalStrictCells.zBase R hI)
    site M N V Z₀ W Symbols H hV v (by omega)
  intro i hi
  change OriginalFiberTotalEvaluation.total J L G R T (Fin 1) n B pos neg supp hf hs (I.card+1) b site M N V W
    (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)) i) (OriginalStrictLocalBlocks.block J L G R T (Fin 1) n B pos neg supp hf hs E P CR empty I.card b idx ≫ OriginalCoordinateProjectionSymbols.projection J L G R T (Fin 1) n B pos neg supp hf hs I.card idx {x : ℕ // x∈I} (PathVariableEndpointMaps.FreeCoordinates hI) (PathOriginalStrictCells.zBase R hI) site M N V Z₀ W Symbols i hi)=
    OriginalFiberTotalEvaluation.total J L G R T (Fin 1) n B pos neg supp hf hs (I.card+1) b site M N V W
    (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)) i) (zCandidate J L G R site M N V W T Z₀ Symbols PH SC hI j hj ha ≫ OriginalCoordinateProjectionSymbols.projection J L G R T (Fin 1) n B pos neg supp hf hs I.card idx {x : ℕ // x∈I} (PathVariableEndpointMaps.FreeCoordinates hI) (PathOriginalStrictCells.zBase R hI) site M N V Z₀ W Symbols i hi)
  rw [z_projection]
  rw [←OriginalStrictBlockIndexTransport.codomain J L G R T (Fin 1) n B pos neg supp hf hs E P CR empty I.card b Edge idx (PathOriginalEdgeProjection.z_edge_eq hI j hj ha).symm]
  simp only [Category.assoc]
  change OriginalFiberTotalEvaluation.total J L G R T (Fin 1) n B pos neg supp hf hs (I.card+1) b site M N V W
    (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)) i) (OriginalStrictLocalBlocks.block J L G R T (Fin 1) n B pos neg supp hf hs E P CR empty I.card b Edge ≫
      PathOriginalEdgeProjection.zProjection J L G R site M N V W hI j hj ha T Z₀ Symbols i hi)=
    OriginalFiberTotalEvaluation.total J L G R T (Fin 1) n B pos neg supp hf hs (I.card+1) b site M N V W
      (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)) i) (PathOriginalScalarColumns.zColumn J L G R site M N V W PH SC hI j hj ha T Z₀ Symbols i)
  rw [PathOriginalScalarColumns.z_value J L G R H site M N V hV W Cg MW PH SC hI j hj ha T Z₀ Symbols]
  apply (PathZWordBasis.basis R hJ site N W Cg).symm.injective
  funext k
  rw [AddEquiv.symm_apply_apply]
  exact (PathOriginalStrictBlockColumns.z_column J L G E R P H site M N V hV Cg hCg O W QO MW
    T CR empty Q K Norm Z₀ Symbols hI j hj ha i hi k).trans (by
      simp only [PathActualColumnDegrees.zEntry,map_mul,map_pow,PathMilnorWittCoefficients.realize_g])

#print axioms zCandidate
#print axioms z_projection
#print axioms z_block
end Z

end Verification.PathOriginalAdjacentArrow
