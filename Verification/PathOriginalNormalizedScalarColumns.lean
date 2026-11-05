/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathStrictFrameTwist
import Verification.PathOriginalScalarColumns

/-!
# Path Original Normalized Scalar Columns

Genuine scalar entries of the original path blocks become the normalized full-rho entries under the actual four-periodic strict frame isomorphisms.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.PathOriginalNormalizedScalarColumns
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


open Classical Verification.PathCoefficientGrading Verification.PathCompression Verification.PathSignedFaceUnits
section Y
variable {d : ℕ} {I : Finset ℕ} (hI : Admissible (2*d) I)
variable (j : ℕ) (hj : j∈Finset.Icc 1 (2*d)) (ha : Addable I j)
local notation "hJ" => nextAdmissible hI j hj ha
local notation "SI" => BinaryWordCoordinates.Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI))
local notation "TI" => BinaryWordCoordinates.Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hJ))
local notation "sourceDegree" => fun i : SI => StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)) i
local notation "targetDegree" => fun k : TI => StrictTorusSymbolInput.degree (Fintype.card (Fin (I.card+1))) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hJ)) k
local notation "raw" => fun (i : SI) (k : TI) => PathCoefficientRing.g^(PathRhoConfiguration.rank I j)*
  PathActualResidueCoordinates.yColumn hI j i (PathActualWordIndices.yWordEquiv hJ k).val

theorem y_degree (i : SI) (k : TI) : Homogeneous (sourceDegree i-targetDegree k) (raw i k) := by
  have hp : Homogeneous 0 (PathCoefficientRing.g^(PathRhoConfiguration.rank I j)) := by
    simpa only [mul_zero] using PathMatrixCoefficientGrading.power _ 0 homogeneous_g (PathRhoConfiguration.rank I j)
  simpa only [zero_add] using homogeneous_mul hp (PathActualColumnDegrees.y_column_degree hI j hj ha i k)

def yEntry (i : SI) (k : TI) : space site N W (CommRingCat.of R) (sourceDegree i-targetDegree k) :=
  PathStrictFrameTwist.realized R site N W P (raw i k) (y_degree hI j hj ha i k)

omit [J.Additive] [L.Additive] in
theorem y_conjugate (i : SI) (k : TI) :
    (PathStrictFrameTwist.twist J L G R site M N W P V H (insert j I) (targetDegree k)).hom ≫
      H.scalar (targetDegree k) (sourceDegree i) (PathOriginalScalarColumns.yEntry R site N W P hI j hj ha i k) ≫
      (PathStrictFrameTwist.twist J L G R site M N W P V H I (sourceDegree i)).hom =
    H.scalar (targetDegree k) (sourceDegree i) (yEntry R site N W P hI j hj ha i k) := by
  have he : PathOriginalScalarColumns.yEntry R site N W P hI j hj ha i k=
      PathStrictFrameTwist.realized R site N W P (PathCoefficientRing.g^(j/2)*(raw i k))
        (PathStrictFrameTwist.signed_degree j (y_degree hI j hj ha i k)) := by
    apply Subtype.ext
    apply congrArg (PathMilnorWittCoefficients.realize (W.symbols (CommRingCat.of R)).toCoefficients)
    change PathActualColumnDegrees.yEntry hI j hj ha i k=_
    dsimp only [PathActualColumnDegrees.yEntry]
    ring
  rw [he]
  exact PathStrictFrameTwist.conjugate J L G R site M N W P V H I j
    (fun hh=>ha.1 (Finset.mem_union_left _ hh)) (targetDegree k) (sourceDegree i) (raw i k) (y_degree hI j hj ha i k)

#print axioms y_degree
#print axioms yEntry
#print axioms y_conjugate
end Y
section Z
variable {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
variable (j : ℕ) (hj : j∈Finset.Icc 1 n) (ha : Addable I j)
local notation "hJ" => nextAdmissible hI j hj ha
local notation "SI" => BinaryWordCoordinates.Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI))
local notation "TI" => BinaryWordCoordinates.Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hJ))
local notation "sourceDegree" => fun i : SI => StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)) i
local notation "targetDegree" => fun k : TI => StrictTorusSymbolInput.degree (Fintype.card (Fin (I.card+1))) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hJ)) k
local notation "raw" => fun (i : SI) (k : TI) => PathCoefficientRing.g^(PathRhoConfiguration.rank I j)*
  PathActualResidueCoordinates.zColumn hI j i (PathActualWordIndices.zWordEquiv hJ k).val

theorem z_degree (i : SI) (k : TI) : Homogeneous (sourceDegree i-targetDegree k) (raw i k) := by
  have hp : Homogeneous 0 (PathCoefficientRing.g^(PathRhoConfiguration.rank I j)) := by
    simpa only [mul_zero] using PathMatrixCoefficientGrading.power _ 0 homogeneous_g (PathRhoConfiguration.rank I j)
  simpa only [zero_add] using homogeneous_mul hp (PathActualColumnDegrees.z_column_degree hI j hj ha i k)

def zEntry (i : SI) (k : TI) : space site N W (CommRingCat.of R) (sourceDegree i-targetDegree k) :=
  PathStrictFrameTwist.realized R site N W P (raw i k) (z_degree hI j hj ha i k)

omit [J.Additive] [L.Additive] in
theorem z_conjugate (i : SI) (k : TI) :
    (PathStrictFrameTwist.twist J L G R site M N W P V H (insert j I) (targetDegree k)).hom ≫
      H.scalar (targetDegree k) (sourceDegree i) (PathOriginalScalarColumns.zEntry R site N W P hI j hj ha i k) ≫
      (PathStrictFrameTwist.twist J L G R site M N W P V H I (sourceDegree i)).hom =
    H.scalar (targetDegree k) (sourceDegree i) (zEntry R site N W P hI j hj ha i k) := by
  have he : PathOriginalScalarColumns.zEntry R site N W P hI j hj ha i k=
      PathStrictFrameTwist.realized R site N W P (PathCoefficientRing.g^(j/2)*(raw i k))
        (PathStrictFrameTwist.signed_degree j (z_degree hI j hj ha i k)) := by
    apply Subtype.ext
    apply congrArg (PathMilnorWittCoefficients.realize (W.symbols (CommRingCat.of R)).toCoefficients)
    change PathActualColumnDegrees.zEntry hI j hj ha i k=_
    dsimp only [PathActualColumnDegrees.zEntry]
    ring
  rw [he]
  exact PathStrictFrameTwist.conjugate J L G R site M N W P V H I j
    (fun hh=>ha.1 (Finset.mem_union_left _ hh)) (targetDegree k) (sourceDegree i) (raw i k) (z_degree hI j hj ha i k)

#print axioms z_degree
#print axioms zEntry
#print axioms z_conjugate
end Z

end Verification.PathOriginalNormalizedScalarColumns
