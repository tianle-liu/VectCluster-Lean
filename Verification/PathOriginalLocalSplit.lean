/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalDegreeTerms

/-!
# Path Original Local Split

The degreewise actual local splitting equals its literal split at the current normal rank, removing dependent cardinal transports.
-/
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace Verification.PathOriginalLocalSplit
open Classical CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.PathCochains Verification.PathCompression Verification.PathNormalizedBasis
open Verification.PathEndpointWords Verification.PathActualWordIndices
open Verification.PathOriginalIndependence Verification.PathStrictTermIndices
attribute [local instance] Abelian.hasFiniteBiproducts
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ) (R : Type) [CommRing R] [Nontrivial R]
variable (T : StrictLocalizedCells.TorusCells J L G R)
variable (Z : A) (M : ℤ → A)
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (W : GradedMilnorWittSheaf.Standard site N)
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (S : StrictTorusSymbolInput.Standard J L G R T Z M site N W V)

section Y
variable (a p : ℕ)
local notation "B" => PathOriginalYPresentation.matrix (2*a)
local notation "hf" => fun I hI => (PathOriginalAS.y a I hI).1
local notation "hs" => fun I hI => (PathOriginalAS.y a I hI).2

omit [HasFiniteBiproducts D] [L.Additive] [Nontrivial R] in
theorem y_eq (I : {I : Config (2*a) // I.val.card=p}) :
    PathOriginalDegreeTerms.yLocal J L G R T Z M site N W V S a p I=
    OriginalStrictProjectionDetection.splitSource J L G R T (Empty) (2*a) B
      (positive_order B y_mutable) (negative_order B y_mutable) (support B y_mutable) hf hs
      p (configDegree B y_mutable p I) I.val.val (PathEvenEndpointTorus.FreeCoordinates I.val.property)
      (PathOriginalStrictCells.yBase R I.val.property) site M N V Z W S := by
  rcases I with ⟨I,hI⟩
  subst p
  rfl
#print axioms y_eq
end Y
section Z
variable (n p : ℕ)
local notation "B" => PathOriginalZPresentation.matrix (n)
local notation "hf" => fun I hI => (PathOriginalAS.z n I hI).1
local notation "hs" => fun I hI => (PathOriginalAS.z n I hI).2

omit [HasFiniteBiproducts D] [L.Additive] [Nontrivial R] in
theorem z_eq (I : {I : Config (n) // I.val.card=p}) :
    PathOriginalDegreeTerms.zLocal J L G R T Z M site N W V S n p I=
    OriginalStrictProjectionDetection.splitSource J L G R T (Fin 1) (n) B
      (positive_order B z_mutable) (negative_order B z_mutable) (support B z_mutable) hf hs
      p (configDegree B z_mutable p I) I.val.val (PathVariableEndpointMaps.FreeCoordinates I.val.property)
      (PathOriginalStrictCells.zBase R I.val.property) site M N V Z W S := by
  rcases I with ⟨I,hI⟩
  subst p
  rfl
#print axioms z_eq
end Z

end Verification.PathOriginalLocalSplit
