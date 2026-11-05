/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalStrictBlockMatrix
import Verification.PathOriginalEdgeProjection

/-!
# Path Original Strict Block Columns

Every positive universal projection detects the literal path matrix column in the genuine strict-model boundary.
-/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.PathOriginalStrictBlockColumns
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

include Q Norm hCg QO MW in
theorem y_column (i : SI) (hi : StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)) i≠0)
 (k : TI) :
    (PathYWordBasis.basis R hJ site N W Cg).symm
      (includeDegree (W.grading (CommRingCat.of New)) ((StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)) i)-(I.card+1 : ℕ))
        (ActualSheafContractionRestriction.pullback site (N ((StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)) i)-(I.card+1 : ℕ)))
          (OriginalCanonicalFiberProjection.projection R Empty (2*d) (b).val B pos neg supp (b).property.2).toRingHom
          (OriginalOrderedStrictSections.localEquiv J L G R Empty (2*d) B pos neg supp hf hs site M N V (I.card+1) (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)) i) b
            (StrictCellTests.testAddEquiv J (StrictLocalizedCells.localCell J L G R T Empty (2*d) B pos neg supp hf hs (I.card+1) b) (M (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)) i))
              (OriginalStrictLocalBlocks.block J L G R T Empty (2*d) B pos neg supp hf hs E P CR empty I.card b Edge ≫ (PathOriginalEdgeProjection.yProjection J L G R site M N V W hI j hj ha T Z₀ Symbols i hi)))))) k=
    (W.symbols (CommRingCat.of R)).g^(PathRhoConfiguration.rank I j)*
      ((W.symbols (CommRingCat.of R)).g^(j/2)*
        realize (W.symbols (CommRingCat.of R)).toCoefficients
          (PathActualResidueCoordinates.yColumn hI j i (PathActualWordIndices.yWordEquiv hJ k).val)) := by
  have h := PathOriginalStrictBlockMatrix.y_matrix J L G E R P H site M N V hV Cg hCg O W QO MW
    T CR empty Q K Norm hI j hj ha (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)) i) (PathOriginalEdgeProjection.yProjection J L G R site M N V W hI j hj ha T Z₀ Symbols i hi) k
  have hc := PathOriginalEdgeProjection.y_coordinates J L G R H site M N V hV W Cg MW hI j hj ha T Z₀ Symbols i hi
  refine h.trans ?_
  apply congrArg (fun x => (W.symbols (CommRingCat.of R)).g^(PathRhoConfiguration.rank I j)*x)
  calc
    _ = ∑ l : SI, ((W.symbols (CommRingCat.of R)).g^(j/2)*
        realize (W.symbols (CommRingCat.of R)).toCoefficients
          (PathActualResidueCoordinates.yColumn hI j l (PathActualWordIndices.yWordEquiv hJ k).val))*
        ((Pi.single i 1 : SI → W.Total (CommRingCat.of R)) l) := by
      apply Finset.sum_congr rfl
      intro l _
      exact congrArg (fun x => ((W.symbols (CommRingCat.of R)).g^(j/2)*
        realize (W.symbols (CommRingCat.of R)).toCoefficients
          (PathActualResidueCoordinates.yColumn hI j l (PathActualWordIndices.yWordEquiv hJ k).val))*x)
        (congrFun hc l)
    _ = _ := by simp [Pi.single_apply]

#print axioms y_column
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

include Q Norm hCg QO MW in
theorem z_column (i : SI) (hi : StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)) i≠0)
 (k : TI) :
    (PathZWordBasis.basis R hJ site N W Cg).symm
      (includeDegree (W.grading (CommRingCat.of New)) ((StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)) i)-(I.card+1 : ℕ))
        (ActualSheafContractionRestriction.pullback site (N ((StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)) i)-(I.card+1 : ℕ)))
          (OriginalCanonicalFiberProjection.projection R (Fin 1) n (b).val B pos neg supp (b).property.2).toRingHom
          (OriginalOrderedStrictSections.localEquiv J L G R (Fin 1) n B pos neg supp hf hs site M N V (I.card+1) (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)) i) b
            (StrictCellTests.testAddEquiv J (StrictLocalizedCells.localCell J L G R T (Fin 1) n B pos neg supp hf hs (I.card+1) b) (M (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)) i))
              (OriginalStrictLocalBlocks.block J L G R T (Fin 1) n B pos neg supp hf hs E P CR empty I.card b Edge ≫ (PathOriginalEdgeProjection.zProjection J L G R site M N V W hI j hj ha T Z₀ Symbols i hi)))))) k=
    (W.symbols (CommRingCat.of R)).g^(PathRhoConfiguration.rank I j)*
      ((W.symbols (CommRingCat.of R)).g^(j/2)*
        realize (W.symbols (CommRingCat.of R)).toCoefficients
          (PathActualResidueCoordinates.zColumn hI j i (PathActualWordIndices.zWordEquiv hJ k).val)) := by
  have h := PathOriginalStrictBlockMatrix.z_matrix J L G E R P H site M N V hV Cg hCg O W QO MW
    T CR empty Q K Norm hI j hj ha (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)) i) (PathOriginalEdgeProjection.zProjection J L G R site M N V W hI j hj ha T Z₀ Symbols i hi) k
  have hc := PathOriginalEdgeProjection.z_coordinates J L G R H site M N V hV W Cg MW hI j hj ha T Z₀ Symbols i hi
  refine h.trans ?_
  apply congrArg (fun x => (W.symbols (CommRingCat.of R)).g^(PathRhoConfiguration.rank I j)*x)
  calc
    _ = ∑ l : SI, ((W.symbols (CommRingCat.of R)).g^(j/2)*
        realize (W.symbols (CommRingCat.of R)).toCoefficients
          (PathActualResidueCoordinates.zColumn hI j l (PathActualWordIndices.zWordEquiv hJ k).val))*
        ((Pi.single i 1 : SI → W.Total (CommRingCat.of R)) l) := by
      apply Finset.sum_congr rfl
      intro l _
      exact congrArg (fun x => ((W.symbols (CommRingCat.of R)).g^(j/2)*
        realize (W.symbols (CommRingCat.of R)).toCoefficients
          (PathActualResidueCoordinates.zColumn hI j l (PathActualWordIndices.zWordEquiv hJ k).val))*x)
        (congrFun hc l)
    _ = _ := by simp [Pi.single_apply]

#print axioms z_column
end Z

end Verification.PathOriginalStrictBlockColumns
