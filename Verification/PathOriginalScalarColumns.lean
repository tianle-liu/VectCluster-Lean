/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalTargetFiberProjection
import Verification.OriginalFiberScalarEvaluation
import Verification.PathActualColumnDegrees
import Verification.PathMilnorWittGradedRealization

/-!
# Path Original Scalar Columns

Literal homogeneous path columns are realized as finite sums of genuine strict-sheaf scalar arrows, with their actual fiber values proved internally.
-/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 4096
namespace Verification.PathOriginalScalarColumns
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.PathCompression Verification.PathSignedStratumCoefficients
open Verification.PathOriginalStratumTransport Verification.PathOriginalIndependence
open Verification.PathCanonicalCoefficientSection
open Verification.IndependentChartIndex
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
variable [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ]
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

variable (PH : GradedMilnorWittHomogeneity.Standard site N W)
variable (SC : GradedMilnorWittStrictScalars.Standard J L G R site M N W PH V)

open scoped BigOperators

section Y
variable {d : ℕ} {I : Finset ℕ} (hI : Admissible (2*d) I)
local notation "B" => PathOriginalYPresentation.matrix (2*d)
variable (j : ℕ) (hj : j∈Finset.Icc 1 (2*d)) (ha : Addable I j)
local notation "hJ" => nextAdmissible hI j hj ha
local notation "μ" => PathEvenEndpointTorus.FreeCoordinates hJ
local notation "Layer" => GlobalNormalFrame.ZeroLayer R Empty (2*d) (mutableSet (2*d) (insert j I)) B
local notation "Fiber" => PathOriginalCoefficientTransport.Fiber (I:=insert j I) R Empty B
local notation "Std" => TorusThomInput.BaseRing R {x : ℕ // x∈insert j I} μ
local notation "TI" => BinaryWordCoordinates.Index (Fintype.card μ)
local notation "pos" => positive_order B y_mutable
local notation "neg" => negative_order B y_mutable
local notation "supp" => support B y_mutable
local notation "hf" => fun I hI => (PathOriginalAS.y d I hI).1
local notation "hs" => fun I hI => (PathOriginalAS.y d I hI).2
local notation "b" => PathOriginalFlagIndex.target B y_mutable hI j hj ha
variable [Nontrivial R] [HasFiniteBiproducts D]
variable (T : StrictLocalizedCells.TorusCells J L G R) (Z₀ : A)
variable (Q : StrictTorusSymbolInput.Standard J L G R T Z₀ M site N W V)

local notation "SI" => BinaryWordCoordinates.Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI))

def yEntry (i : SI) (k : TI) :
    GradedMilnorWittDegreeSpaces.space site N W (CommRingCat.of R) ((StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)) i)-(StrictTorusSymbolInput.degree (Fintype.card (Fin (I.card+1))) (Fintype.card μ) k)) :=
  ⟨PathMilnorWittCoefficients.realize (W.symbols (CommRingCat.of R)).toCoefficients
      (PathActualColumnDegrees.yEntry hI j hj ha i k),
    PathMilnorWittGradedRealization.homogeneous PH (CommRingCat.of R)
      (PathActualColumnDegrees.y_entry_degree hI j hj ha i k)⟩

def yColumn (i : SI) : (StrictLocalizedCells.localCell J L G R T Empty (2*d) B pos neg supp hf hs (I.card+1) b).term ⟶ M (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)) i) :=
  ∑ k : TI, PathOriginalTargetProjection.yProjection J L G R site M N V W hI j hj ha T Z₀ Q k ≫
    SC.scalar (StrictTorusSymbolInput.degree (Fintype.card (Fin (I.card+1))) (Fintype.card μ) k) (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)) i) (yEntry R site N W PH hI j hj ha i k)

include P H hV in
omit [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [J.CommShift ℤ] [L.CommShift ℤ]
  [HasShift D ℤ] [L.Additive] [Nontrivial R] [HasFiniteBiproducts D] in
theorem y_value (i : SI) :
    OriginalFiberTotalEvaluation.total J L G R T Empty (2*d) B pos neg supp hf hs (I.card+1) b site M N V W
      (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)) i) (yColumn J L G R site M N V W PH SC hI j hj ha T Z₀ Q i)=
    PathYWordBasis.basis R hJ site N W K (fun k =>
      PathMilnorWittCoefficients.realize (W.symbols (CommRingCat.of R)).toCoefficients
        (PathActualColumnDegrees.yEntry hI j hj ha i k)) := by
  rw [yColumn,map_sum,PathYWordBasis.basis_expansion R hJ site N W K P]
  apply Finset.sum_congr rfl
  intro k _
  rw [OriginalFiberTotalEvaluation.total_apply,OriginalFiberScalarEvaluation.evaluate J L G R T Empty (2*d) B
    pos neg supp hf hs (I.card+1) b site M N V W PH SC]
  refine (congrArg (fun x : W.Total (CommRingCat.of Fiber) => x*
    GradedMilnorWittScalarNaturality.scalar R Fiber site N W (yEntry R site N W PH hI j hj ha i k).val)
    (PathOriginalTargetFiberProjection.y_fiber J L G R H site M N V hV W K P hI j hj ha T Z₀ Q k)).trans ?_
  rw [PathYWordBasis.basis_single R hJ site N W K P,map_one,mul_one]
  rfl

#print axioms yEntry
#print axioms yColumn
#print axioms y_value
end Y

section Z
variable {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
local notation "B" => PathOriginalZPresentation.matrix n
variable (j : ℕ) (hj : j∈Finset.Icc 1 n) (ha : Addable I j)
local notation "hJ" => nextAdmissible hI j hj ha
local notation "μ" => PathVariableEndpointMaps.FreeCoordinates hJ
local notation "Layer" => GlobalNormalFrame.ZeroLayer R (Fin 1) n (mutableSet n (insert j I)) B
local notation "Fiber" => PathOriginalCoefficientTransport.Fiber (I:=insert j I) R (Fin 1) B
local notation "Std" => TorusThomInput.BaseRing R {x : ℕ // x∈insert j I} μ
local notation "TI" => BinaryWordCoordinates.Index (Fintype.card μ)
local notation "pos" => positive_order B z_mutable
local notation "neg" => negative_order B z_mutable
local notation "supp" => support B z_mutable
local notation "hf" => fun I hI => (PathOriginalAS.z n I hI).1
local notation "hs" => fun I hI => (PathOriginalAS.z n I hI).2
local notation "b" => PathOriginalFlagIndex.target B z_mutable hI j hj ha
variable [Nontrivial R] [HasFiniteBiproducts D]
variable (T : StrictLocalizedCells.TorusCells J L G R) (Z₀ : A)
variable (Q : StrictTorusSymbolInput.Standard J L G R T Z₀ M site N W V)

local notation "SI" => BinaryWordCoordinates.Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI))

def zEntry (i : SI) (k : TI) :
    GradedMilnorWittDegreeSpaces.space site N W (CommRingCat.of R) ((StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)) i)-(StrictTorusSymbolInput.degree (Fintype.card (Fin (I.card+1))) (Fintype.card μ) k)) :=
  ⟨PathMilnorWittCoefficients.realize (W.symbols (CommRingCat.of R)).toCoefficients
      (PathActualColumnDegrees.zEntry hI j hj ha i k),
    PathMilnorWittGradedRealization.homogeneous PH (CommRingCat.of R)
      (PathActualColumnDegrees.z_entry_degree hI j hj ha i k)⟩

def zColumn (i : SI) : (StrictLocalizedCells.localCell J L G R T (Fin 1) n B pos neg supp hf hs (I.card+1) b).term ⟶ M (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)) i) :=
  ∑ k : TI, PathOriginalTargetProjection.zProjection J L G R site M N V W hI j hj ha T Z₀ Q k ≫
    SC.scalar (StrictTorusSymbolInput.degree (Fintype.card (Fin (I.card+1))) (Fintype.card μ) k) (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)) i) (zEntry R site N W PH hI j hj ha i k)

include P H hV in
omit [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [J.CommShift ℤ] [L.CommShift ℤ]
  [HasShift D ℤ] [L.Additive] [Nontrivial R] [HasFiniteBiproducts D] in
theorem z_value (i : SI) :
    OriginalFiberTotalEvaluation.total J L G R T (Fin 1) n B pos neg supp hf hs (I.card+1) b site M N V W
      (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)) i) (zColumn J L G R site M N V W PH SC hI j hj ha T Z₀ Q i)=
    PathZWordBasis.basis R hJ site N W K (fun k =>
      PathMilnorWittCoefficients.realize (W.symbols (CommRingCat.of R)).toCoefficients
        (PathActualColumnDegrees.zEntry hI j hj ha i k)) := by
  rw [zColumn,map_sum,PathZWordBasis.basis_expansion R hJ site N W K P]
  apply Finset.sum_congr rfl
  intro k _
  rw [OriginalFiberTotalEvaluation.total_apply,OriginalFiberScalarEvaluation.evaluate J L G R T (Fin 1) n B
    pos neg supp hf hs (I.card+1) b site M N V W PH SC]
  refine (congrArg (fun x : W.Total (CommRingCat.of Fiber) => x*
    GradedMilnorWittScalarNaturality.scalar R Fiber site N W (zEntry R site N W PH hI j hj ha i k).val)
    (PathOriginalTargetFiberProjection.z_fiber J L G R H site M N V hV W K P hI j hj ha T Z₀ Q k)).trans ?_
  rw [PathZWordBasis.basis_single R hJ site N W K P,map_one,mul_one]
  rfl

#print axioms zEntry
#print axioms zColumn
#print axioms z_value
end Z

end Verification.PathOriginalScalarColumns
