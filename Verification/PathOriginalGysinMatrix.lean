/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalResidueMatrix
import Verification.PathOriginalFlagIndex
import Verification.TorusWordQuadraticAction
import Verification.PathOriginalAS

/-!
# Path Original Gysin Matrix

The genuine ordered Gysin residue on each original path flag has the
full-rho matrix, including its actual normal-order factor.
-/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 4096
namespace Verification.PathOriginalGysinMatrix
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.ExchangeOpenCover Verification.IndependentBasicOpen
open Verification.IndependentOpenCoordinates Verification.GlobalExchangeSmooth
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {Z : Type*} [Category Z] [Preadditive Z] [HasFiniteBiproducts Z]
variable [HasZeroObject Z] [HasShift Z ℤ] [∀ q : ℤ, (CategoryTheory.shiftFunctor Z q).Additive] [Pretriangulated Z]
variable (J : DerivedCategory A ⥤ Z) [J.Additive] [J.CommShift ℤ]
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

include hCg QO in
omit [HasFiniteBiproducts Z] [HasZeroObject Z] [Pretriangulated Z] [L.IsTriangulated] [J.Additive] in
theorem y_total (q : ℤ) (a : Section site N Source (q-I.card)) :
    includeDegree (W.grading (CommRingCat.of New)) (q-(I.card+1 : ℕ))
      (OriginalOrderedGradedRow.residueValue J L G R Empty (2*d) B pos neg supp hf hs E P
        site M N V H hV O Cg I.card b v q a)=
    (W.symbols (CommRingCat.of New)).g^(PathRhoConfiguration.rank I j)*
      PathOriginalResidueTransport.yResidue R site N W Cg hI j hj ha
        (includeDegree (W.grading (CommRingCat.of Source)) (q-I.card) a) := by
  refine (OriginalTotalAdjacentResidue.total_residue J L G E R Empty (2*d) B P pos neg supp hf hs H
    I.card b v site M N V hV Cg hCg O W QO q a).trans ?_
  change (W.symbols (CommRingCat.of New)).g^
    (((Finset.univ.erase (v)).filter (fun i : Selected (2*d) (mutableSet (2*d) (insert j I)) => i<v))).card *
      PathOriginalResidueTransport.yResidue R site N W Cg hI j hj ha
        (includeDegree (W.grading (CommRingCat.of Source)) (q-I.card) a)=_
  rw [PathOriginalFaceIndex.preceding_count j hj hI]
  rfl

include hCg QO MW in
omit [HasFiniteBiproducts Z] [HasZeroObject Z] [Pretriangulated Z] [L.IsTriangulated] [J.Additive] in
theorem y_matrix (q : ℤ) (a : Section site N Source (q-I.card)) (k : TI) :
    (PathYWordBasis.basis R hJ site N W Cg).symm
      (includeDegree (W.grading (CommRingCat.of New)) (q-(I.card+1 : ℕ))
        (OriginalOrderedGradedRow.residueValue J L G R Empty (2*d) B pos neg supp hf hs E P
          site M N V H hV O Cg I.card b v q a)) k=
    (W.symbols (CommRingCat.of R)).g^(PathRhoConfiguration.rank I j)*
      ∑ i : SI, ((W.symbols (CommRingCat.of R)).g^(j/2)*
        realize (W.symbols (CommRingCat.of R)).toCoefficients
          (PathActualResidueCoordinates.yColumn hI j i (PathActualWordIndices.yWordEquiv hJ k).val))*
        ((PathOriginalResidueMatrix.ySourceBasis J L G R H site M N V hV W Cg hI j hj ha).symm
          (includeDegree (W.grading (CommRingCat.of Source)) (q-I.card) a)) i := by
  rw [y_total J L G E R P H site M N V hV Cg hCg O W QO hI j hj ha]
  have ht := congrFun (TorusWordQuadraticAction.coordinates_power R New
    (PathEvenEndpointTorus.FreeCoordinates hJ) (PathYWordBasis.torusEquiv R hJ) site N W Cg MW
    (PathRhoConfiguration.rank I j)
    (PathOriginalResidueTransport.yResidue R site N W Cg hI j hj ha
      (includeDegree (W.grading (CommRingCat.of Source)) (q-I.card) a))) k
  change (PathYWordBasis.basis R hJ site N W Cg).symm _ k=_ at ht
  rw [ht]
  exact congrArg (fun x => (W.symbols (CommRingCat.of R)).g^(PathRhoConfiguration.rank I j)*x)
    (PathOriginalResidueMatrix.y_matrix J L G R H site M N V hV W Cg hCg hI j hj ha MW _ k)

#print axioms y_total
#print axioms y_matrix
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

include hCg QO in
omit [HasFiniteBiproducts Z] [HasZeroObject Z] [Pretriangulated Z] [L.IsTriangulated] [J.Additive] in
theorem z_total (q : ℤ) (a : Section site N Source (q-I.card)) :
    includeDegree (W.grading (CommRingCat.of New)) (q-(I.card+1 : ℕ))
      (OriginalOrderedGradedRow.residueValue J L G R (Fin 1) n B pos neg supp hf hs E P
        site M N V H hV O Cg I.card b v q a)=
    (W.symbols (CommRingCat.of New)).g^(PathRhoConfiguration.rank I j)*
      PathOriginalResidueTransport.zResidue R site N W Cg hI j hj ha
        (includeDegree (W.grading (CommRingCat.of Source)) (q-I.card) a) := by
  refine (OriginalTotalAdjacentResidue.total_residue J L G E R (Fin 1) n B P pos neg supp hf hs H
    I.card b v site M N V hV Cg hCg O W QO q a).trans ?_
  change (W.symbols (CommRingCat.of New)).g^
    (((Finset.univ.erase (v)).filter (fun i : Selected n (mutableSet n (insert j I)) => i<v))).card *
      PathOriginalResidueTransport.zResidue R site N W Cg hI j hj ha
        (includeDegree (W.grading (CommRingCat.of Source)) (q-I.card) a)=_
  rw [PathOriginalFaceIndex.preceding_count j hj hI]
  rfl

include hCg QO MW in
omit [HasFiniteBiproducts Z] [HasZeroObject Z] [Pretriangulated Z] [L.IsTriangulated] [J.Additive] in
theorem z_matrix (q : ℤ) (a : Section site N Source (q-I.card)) (k : TI) :
    (PathZWordBasis.basis R hJ site N W Cg).symm
      (includeDegree (W.grading (CommRingCat.of New)) (q-(I.card+1 : ℕ))
        (OriginalOrderedGradedRow.residueValue J L G R (Fin 1) n B pos neg supp hf hs E P
          site M N V H hV O Cg I.card b v q a)) k=
    (W.symbols (CommRingCat.of R)).g^(PathRhoConfiguration.rank I j)*
      ∑ i : SI, ((W.symbols (CommRingCat.of R)).g^(j/2)*
        realize (W.symbols (CommRingCat.of R)).toCoefficients
          (PathActualResidueCoordinates.zColumn hI j i (PathActualWordIndices.zWordEquiv hJ k).val))*
        ((PathOriginalResidueMatrix.zSourceBasis J L G R H site M N V hV W Cg hI j hj ha).symm
          (includeDegree (W.grading (CommRingCat.of Source)) (q-I.card) a)) i := by
  rw [z_total J L G E R P H site M N V hV Cg hCg O W QO hI j hj ha]
  have ht := congrFun (TorusWordQuadraticAction.coordinates_power R New
    (PathVariableEndpointMaps.FreeCoordinates hJ) (PathZWordBasis.torusEquiv R hJ) site N W Cg MW
    (PathRhoConfiguration.rank I j)
    (PathOriginalResidueTransport.zResidue R site N W Cg hI j hj ha
      (includeDegree (W.grading (CommRingCat.of Source)) (q-I.card) a))) k
  change (PathZWordBasis.basis R hJ site N W Cg).symm _ k=_ at ht
  rw [ht]
  exact congrArg (fun x => (W.symbols (CommRingCat.of R)).g^(PathRhoConfiguration.rank I j)*x)
    (PathOriginalResidueMatrix.z_matrix J L G R H site M N V hV W Cg hCg hI j hj ha MW _ k)

#print axioms z_total
#print axioms z_matrix
end Z

end Verification.PathOriginalGysinMatrix
