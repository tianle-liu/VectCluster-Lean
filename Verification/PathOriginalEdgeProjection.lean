/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalProjectionCoordinates
import Verification.OriginalStrictIndexTransport

/-!
# Path Original Edge Projection

Actual positive projections in edge-source indices retain their genuine signed path word coordinates.
-/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 4096
namespace Verification.PathOriginalEdgeProjection
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.PathCompression Verification.PathSignedStratumCoefficients
open Verification.PathOriginalStratumTransport Verification.PathOriginalIndependence
open Verification.PathCanonicalCoefficientSection
open Verification.IndependentChartIndex
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasBinaryBiproducts A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
variable [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive]
variable [Pretriangulated D]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ] [J.IsTriangulated]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
variable (G : Scheme ⥤ CochainComplex C ℤ) (R : Type) [CommRing R]
variable (H : LocalizedAffineThomInvariance.Standard L R G)
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (hV : LocalizedThomSections.Naturality J L G R site M N V)
variable (W : GradedMilnorWittSheaf.Standard site N)

variable (K : StandardThomContractionNormalization.Grading R site N)

open Verification.PathSignedFaceUnits Verification.PathMilnorWittCoefficients

variable (P : GradedMilnorWittLaurent.Standard R site N W K)

section Y
variable {d : ℕ} {I : Finset ℕ} (hI : Admissible (2*d) I)
local notation "B" => PathOriginalYPresentation.matrix (2*d)
local notation "μ" => PathEvenEndpointTorus.FreeCoordinates hI
local notation "Layer" => GlobalNormalFrame.ZeroLayer R Empty (2*d) (mutableSet (2*d) I) B
local notation "Fiber" => PathOriginalCoefficientTransport.Fiber (I:=I) R Empty B
local notation "Std" => TorusThomInput.BaseRing R I μ
local notation "SI" => BinaryWordCoordinates.Index (Fintype.card μ)
local notation "pos" => positive_order B y_mutable
local notation "neg" => negative_order B y_mutable
local notation "supp" => support B y_mutable
local notation "indep" => independent B y_mutable hI
local notation "idx" => PathOriginalStrictCells.yIndex hI
local notation "hf" => fun I hI => (PathOriginalAS.y d I hI).1
local notation "hs" => fun I hI => (PathOriginalAS.y d I hI).2

variable (j : ℕ) (hj : j∈Finset.Icc 1 (2*d)) (ha : Addable I j)
local notation "b" => PathOriginalFlagIndex.target B y_mutable hI j hj ha
local notation "v" => PathOriginalFaceIndex.selectedNormal (I:=I) j hj
local notation "Edge" => ActualGlobalBoundary.edgeIndex Empty (2*d) B I.card b v
local notation "Source" => GlobalNormalFrame.ZeroLayer R Empty (2*d) (Edge).val B

theorem y_edge_eq : idx=Edge :=
  Subtype.ext (PathOriginalFaceIndex.mutable_erase j hj ha).symm

variable [Nontrivial R] [HasFiniteBiproducts D]
variable (T : StrictLocalizedCells.TorusCells J L G R) (Z₀ : A)
variable (Q : StrictTorusSymbolInput.Standard J L G R T Z₀ M site N W V)

def yProjection (i : SI)
    (hi : StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card μ) i≠0) :
    (StrictLocalizedCells.localCell J L G R T Empty (2*d) B pos neg supp hf hs I.card Edge).term ⟶ M (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card μ) i) :=
  eqToHom (congrArg (fun x => (StrictLocalizedCells.localCell J L G R T Empty (2*d) B pos neg supp hf hs I.card x).term) (y_edge_eq hI j hj ha).symm) ≫ OriginalCoordinateProjectionSymbols.projection J L G R T Empty (2*d) B pos neg supp hf hs I.card idx I μ (PathOriginalStrictCells.yBase R hI) site M N V Z₀ W Q i hi

include P in
omit [HasBinaryBiproducts A] [HasZeroObject D] [∀ m : ℤ, (shiftFunctor D m).Additive]
  [Pretriangulated D] [J.CommShift ℤ] [J.IsTriangulated] [L.Additive] [L.CommShift ℤ]
  [L.IsTriangulated] [Nontrivial R] [HasFiniteBiproducts D] [HasShift D ℤ] in
theorem y_coordinates (i : SI)
    (hi : StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card μ) i≠0) :
    (PathOriginalResidueMatrix.ySourceBasis J L G R H site M N V hV W K hI j hj ha).symm
      (GradedSectionTotal.includeDegree (W.grading (CommRingCat.of Source))
        (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card μ) i-I.card)
        (OriginalOrderedStrictSections.localEquiv J L G R Empty (2*d) B pos neg supp hf hs site M N V I.card _ Edge
          (StrictCellTests.testAddEquiv J (StrictLocalizedCells.localCell J L G R T Empty (2*d) B pos neg supp hf hs I.card Edge) _
            (yProjection J L G R site M N V W hI j hj ha T Z₀ Q i hi))))=Pi.single i 1 := by
  apply (PathOriginalResidueMatrix.ySourceBasis J L G R H site M N V hV W K hI j hj ha).injective
  rw [AddEquiv.apply_symm_apply,PathOriginalLayerWordBasis.y_source]
  have h := OriginalStrictIndexTransport.total_cast J L G R T Empty (2*d) B pos neg supp hf hs site M N V
    I.card idx Edge (y_edge_eq hI j hj ha) _ W (OriginalCoordinateProjectionSymbols.projection J L G R T Empty (2*d) B pos neg supp hf hs I.card idx I μ (PathOriginalStrictCells.yBase R hI) site M N V Z₀ W Q i hi)
  refine h.symm.trans ?_
  exact congrArg (GradedMilnorWittSheaf.pullback site N W
    (S:=CommRingCat.of Layer) (T:=CommRingCat.of Source)
    (OriginalZeroLayerCast.equiv R Empty (2*d) B (congrArg Subtype.val (y_edge_eq hI j hj ha))).toRingHom)
    (PathOriginalProjectionCoordinates.y_projection J L G R H site M N V hV W K P hI T Z₀ Q i hi)

#print axioms y_edge_eq
#print axioms yProjection
#print axioms y_coordinates
end Y

section Z
variable {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
local notation "B" => PathOriginalZPresentation.matrix n
local notation "μ" => PathVariableEndpointMaps.FreeCoordinates hI
local notation "Layer" => GlobalNormalFrame.ZeroLayer R (Fin 1) n (mutableSet n I) B
local notation "Fiber" => PathOriginalCoefficientTransport.Fiber (I:=I) R (Fin 1) B
local notation "Std" => TorusThomInput.BaseRing R I μ
local notation "SI" => BinaryWordCoordinates.Index (Fintype.card μ)
local notation "pos" => positive_order B z_mutable
local notation "neg" => negative_order B z_mutable
local notation "supp" => support B z_mutable
local notation "indep" => independent B z_mutable hI
local notation "idx" => PathOriginalStrictCells.zIndex hI
local notation "hf" => fun I hI => (PathOriginalAS.z n I hI).1
local notation "hs" => fun I hI => (PathOriginalAS.z n I hI).2

variable (j : ℕ) (hj : j∈Finset.Icc 1 n) (ha : Addable I j)
local notation "b" => PathOriginalFlagIndex.target B z_mutable hI j hj ha
local notation "v" => PathOriginalFaceIndex.selectedNormal (I:=I) j hj
local notation "Edge" => ActualGlobalBoundary.edgeIndex (Fin 1) n B I.card b v
local notation "Source" => GlobalNormalFrame.ZeroLayer R (Fin 1) n (Edge).val B

theorem z_edge_eq : idx=Edge :=
  Subtype.ext (PathOriginalFaceIndex.mutable_erase j hj ha).symm

variable [Nontrivial R] [HasFiniteBiproducts D]
variable (T : StrictLocalizedCells.TorusCells J L G R) (Z₀ : A)
variable (Q : StrictTorusSymbolInput.Standard J L G R T Z₀ M site N W V)

def zProjection (i : SI)
    (hi : StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card μ) i≠0) :
    (StrictLocalizedCells.localCell J L G R T (Fin 1) n B pos neg supp hf hs I.card Edge).term ⟶ M (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card μ) i) :=
  eqToHom (congrArg (fun x => (StrictLocalizedCells.localCell J L G R T (Fin 1) n B pos neg supp hf hs I.card x).term) (z_edge_eq hI j hj ha).symm) ≫ OriginalCoordinateProjectionSymbols.projection J L G R T (Fin 1) n B pos neg supp hf hs I.card idx I μ (PathOriginalStrictCells.zBase R hI) site M N V Z₀ W Q i hi

include P in
omit [HasBinaryBiproducts A] [HasZeroObject D] [∀ m : ℤ, (shiftFunctor D m).Additive]
  [Pretriangulated D] [J.CommShift ℤ] [J.IsTriangulated] [L.Additive] [L.CommShift ℤ]
  [L.IsTriangulated] [Nontrivial R] [HasFiniteBiproducts D] [HasShift D ℤ] in
theorem z_coordinates (i : SI)
    (hi : StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card μ) i≠0) :
    (PathOriginalResidueMatrix.zSourceBasis J L G R H site M N V hV W K hI j hj ha).symm
      (GradedSectionTotal.includeDegree (W.grading (CommRingCat.of Source))
        (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card μ) i-I.card)
        (OriginalOrderedStrictSections.localEquiv J L G R (Fin 1) n B pos neg supp hf hs site M N V I.card _ Edge
          (StrictCellTests.testAddEquiv J (StrictLocalizedCells.localCell J L G R T (Fin 1) n B pos neg supp hf hs I.card Edge) _
            (zProjection J L G R site M N V W hI j hj ha T Z₀ Q i hi))))=Pi.single i 1 := by
  apply (PathOriginalResidueMatrix.zSourceBasis J L G R H site M N V hV W K hI j hj ha).injective
  rw [AddEquiv.apply_symm_apply,PathOriginalLayerWordBasis.z_source]
  have h := OriginalStrictIndexTransport.total_cast J L G R T (Fin 1) n B pos neg supp hf hs site M N V
    I.card idx Edge (z_edge_eq hI j hj ha) _ W (OriginalCoordinateProjectionSymbols.projection J L G R T (Fin 1) n B pos neg supp hf hs I.card idx I μ (PathOriginalStrictCells.zBase R hI) site M N V Z₀ W Q i hi)
  refine h.symm.trans ?_
  exact congrArg (GradedMilnorWittSheaf.pullback site N W
    (S:=CommRingCat.of Layer) (T:=CommRingCat.of Source)
    (OriginalZeroLayerCast.equiv R (Fin 1) n B (congrArg Subtype.val (z_edge_eq hI j hj ha))).toRingHom)
    (PathOriginalProjectionCoordinates.z_projection J L G R H site M N V hV W K P hI T Z₀ Q i hi)

#print axioms z_edge_eq
#print axioms zProjection
#print axioms z_coordinates
end Z

end Verification.PathOriginalEdgeProjection
