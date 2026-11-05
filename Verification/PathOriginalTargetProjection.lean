/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalProjectionCoordinates

/-!
# Path Original Target Projection

Target projections in the literal adjacent normal rank give the same genuine signed word basis.
-/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 4096
namespace Verification.PathOriginalTargetProjection
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

def yProjection (i : TI) :
    (StrictLocalizedCells.localCell J L G R T Empty (2*d) B pos neg supp hf hs (I.card+1) b).term ⟶
      M (StrictTorusSymbolInput.degree (Fintype.card (Fin (I.card+1))) (Fintype.card μ) i) :=
  OriginalCoordinateProjectionSymbols.projection J L G R T Empty (2*d) B pos neg supp hf hs (I.card+1) b
    {x : ℕ // x∈insert j I} μ (PathOriginalStrictCells.yBase R hJ) site M N V Z₀ W Q i
    (ne_of_gt (StrictTorusSymbolInput.degree_positive _ _ (by simp only [Fintype.card_fin]; omega) i))

include P in
omit [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [J.CommShift ℤ] [L.CommShift ℤ]
  [HasShift D ℤ] [L.Additive] [Nontrivial R] [HasFiniteBiproducts D] in
theorem y_layer (i : TI) :
    GradedSectionTotal.includeDegree (W.grading (CommRingCat.of Layer))
      (StrictTorusSymbolInput.degree (Fintype.card (Fin (I.card+1))) (Fintype.card μ) i-(I.card+1 : ℕ))
      (OriginalOrderedStrictSections.localEquiv J L G R Empty (2*d) B pos neg supp hf hs site M N V (I.card+1) _ b
        (StrictCellTests.testAddEquiv J
          (StrictLocalizedCells.localCell J L G R T Empty (2*d) B pos neg supp hf hs (I.card+1) b) _
          (yProjection J L G R site M N V W hI j hj ha T Z₀ Q i)))=
      PathOriginalLayerWordBasis.yBasis J L G R H site M N V hV W K hJ (Pi.single i 1) := by
  rw [←PathOriginalProjectionCoordinates.y_standard_word J L G R H site M N V hV W K P hJ i]
  let e := GradedMilnorWittSheafEquiv.equiv site N W (S:=CommRingCat.of Layer) (T:=CommRingCat.of Std)
    (PathOriginalStrictCells.yBase R hJ).toRingEquiv
  apply e.injective
  change GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Layer) (T:=CommRingCat.of Std)
    (PathOriginalStrictCells.yBase R hJ).toRingHom _=e (e.symm _)
  rw [RingEquiv.apply_symm_apply,GradedMilnorWittSheaf.pullback_degree]
  exact OriginalCoordinateProjectionSymbols.symbols J L G R T Empty (2*d) B pos neg supp hf hs
    (I.card+1) b {x : ℕ // x∈insert j I} μ (PathOriginalStrictCells.yBase R hJ) site M N V hV Z₀ W Q i _

#print axioms yProjection
#print axioms y_layer
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

def zProjection (i : TI) :
    (StrictLocalizedCells.localCell J L G R T (Fin 1) n B pos neg supp hf hs (I.card+1) b).term ⟶
      M (StrictTorusSymbolInput.degree (Fintype.card (Fin (I.card+1))) (Fintype.card μ) i) :=
  OriginalCoordinateProjectionSymbols.projection J L G R T (Fin 1) n B pos neg supp hf hs (I.card+1) b
    {x : ℕ // x∈insert j I} μ (PathOriginalStrictCells.zBase R hJ) site M N V Z₀ W Q i
    (ne_of_gt (StrictTorusSymbolInput.degree_positive _ _ (by simp only [Fintype.card_fin]; omega) i))

include P in
omit [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [J.CommShift ℤ] [L.CommShift ℤ]
  [HasShift D ℤ] [L.Additive] [Nontrivial R] [HasFiniteBiproducts D] in
theorem z_layer (i : TI) :
    GradedSectionTotal.includeDegree (W.grading (CommRingCat.of Layer))
      (StrictTorusSymbolInput.degree (Fintype.card (Fin (I.card+1))) (Fintype.card μ) i-(I.card+1 : ℕ))
      (OriginalOrderedStrictSections.localEquiv J L G R (Fin 1) n B pos neg supp hf hs site M N V (I.card+1) _ b
        (StrictCellTests.testAddEquiv J
          (StrictLocalizedCells.localCell J L G R T (Fin 1) n B pos neg supp hf hs (I.card+1) b) _
          (zProjection J L G R site M N V W hI j hj ha T Z₀ Q i)))=
      PathOriginalLayerWordBasis.zBasis J L G R H site M N V hV W K hJ (Pi.single i 1) := by
  rw [←PathOriginalProjectionCoordinates.z_standard_word J L G R H site M N V hV W K P hJ i]
  let e := GradedMilnorWittSheafEquiv.equiv site N W (S:=CommRingCat.of Layer) (T:=CommRingCat.of Std)
    (PathOriginalStrictCells.zBase R hJ).toRingEquiv
  apply e.injective
  change GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Layer) (T:=CommRingCat.of Std)
    (PathOriginalStrictCells.zBase R hJ).toRingHom _=e (e.symm _)
  rw [RingEquiv.apply_symm_apply,GradedMilnorWittSheaf.pullback_degree]
  exact OriginalCoordinateProjectionSymbols.symbols J L G R T (Fin 1) n B pos neg supp hf hs
    (I.card+1) b {x : ℕ // x∈insert j I} μ (PathOriginalStrictCells.zBase R hJ) site M N V hV Z₀ W Q i _

#print axioms zProjection
#print axioms z_layer
end Z

end Verification.PathOriginalTargetProjection
