/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalLayerWordBasis
import Verification.PathOriginalStrictCoordinateUnits
import Verification.OriginalCoordinateProjectionSymbols

/-!
# Path Original Projection Coordinates

The actual positive universal projections of each path strict cell
are exactly its constructed signed word basis vectors.
-/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 4096
namespace Verification.PathOriginalProjectionCoordinates
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

include P in
omit [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [J.Additive] [J.CommShift ℤ] [L.Additive] [L.CommShift ℤ] [HasShift D ℤ] in
theorem y_standard_word (i : SI) :
    GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Std) (T:=CommRingCat.of Layer)
      (PathOriginalStrictCells.yBase R hI).symm.toRingHom
      (OrderedBinaryWords.word (Fintype.card μ)
        (fun k => (W.symbols (CommRingCat.of Std)).symbol (StrictTorusSymbolInput.baseUnit R I μ k)) i)=
    PathOriginalLayerWordBasis.yBasis J L G R H site M N V hV W K hI (Pi.single i 1) := by
  rw [PathOriginalStrictCoordinateUnits.y_word]
  change _=(PathCanonicalSectionTotal.yProjection J L G R H site M N V hV W hI).symm
    (PathYWordBasis.basis R hI site N W K (Pi.single i 1))
  rw [PathYWordBasis.basis_single R hI site N W K P,map_one,mul_one]
  exact (OriginalCanonicalSectionTotal.inverse_section R Empty (2*d) (mutableSet (2*d) I) B pos neg supp indep
    (y_fiber_smooth R hI) J L G H site M N V hV W (y_section R hI) (y_split R hI) _).symm

variable [Nontrivial R] [HasFiniteBiproducts D]
variable (T : StrictLocalizedCells.TorusCells J L G R) (Z₀ : A)
variable (Q : StrictTorusSymbolInput.Standard J L G R T Z₀ M site N W V)

include P in
omit [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [J.CommShift ℤ] [L.CommShift ℤ] [HasShift D ℤ] [L.Additive] [Nontrivial R] [HasFiniteBiproducts D] in
theorem y_projection (i : SI)
    (hi : StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card μ) i≠0) :
    GradedSectionTotal.includeDegree (W.grading (CommRingCat.of Layer))
      (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card μ) i-I.card)
      (OriginalOrderedStrictSections.localEquiv J L G R Empty (2*d) B pos neg supp hf hs site M N V I.card _ idx
        (StrictCellTests.testAddEquiv J
          (StrictLocalizedCells.localCell J L G R T Empty (2*d) B pos neg supp hf hs I.card idx) _
          (OriginalCoordinateProjectionSymbols.projection J L G R T Empty (2*d) B pos neg supp hf hs
            I.card idx I μ (PathOriginalStrictCells.yBase R hI) site M N V Z₀ W Q i hi)))=
      PathOriginalLayerWordBasis.yBasis J L G R H site M N V hV W K hI (Pi.single i 1) := by
  rw [←y_standard_word J L G R H site M N V hV W K P hI i]
  let e := GradedMilnorWittSheafEquiv.equiv site N W (S:=CommRingCat.of Layer) (T:=CommRingCat.of Std)
    (PathOriginalStrictCells.yBase R hI).toRingEquiv
  apply e.injective
  change GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Layer) (T:=CommRingCat.of Std)
    (PathOriginalStrictCells.yBase R hI).toRingHom _=e (e.symm _)
  rw [RingEquiv.apply_symm_apply,GradedMilnorWittSheaf.pullback_degree]
  exact OriginalCoordinateProjectionSymbols.symbols J L G R T Empty (2*d) B pos neg supp hf hs
    I.card idx I μ (PathOriginalStrictCells.yBase R hI) site M N V hV Z₀ W Q i hi

#print axioms y_standard_word
#print axioms y_projection
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

include P in
omit [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [J.Additive] [J.CommShift ℤ] [L.Additive] [L.CommShift ℤ] [HasShift D ℤ] in
theorem z_standard_word (i : SI) :
    GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Std) (T:=CommRingCat.of Layer)
      (PathOriginalStrictCells.zBase R hI).symm.toRingHom
      (OrderedBinaryWords.word (Fintype.card μ)
        (fun k => (W.symbols (CommRingCat.of Std)).symbol (StrictTorusSymbolInput.baseUnit R I μ k)) i)=
    PathOriginalLayerWordBasis.zBasis J L G R H site M N V hV W K hI (Pi.single i 1) := by
  rw [PathOriginalStrictCoordinateUnits.z_word]
  change _=(PathCanonicalSectionTotal.zProjection J L G R H site M N V hV W hI).symm
    (PathZWordBasis.basis R hI site N W K (Pi.single i 1))
  rw [PathZWordBasis.basis_single R hI site N W K P,map_one,mul_one]
  exact (OriginalCanonicalSectionTotal.inverse_section R (Fin 1) n (mutableSet n I) B pos neg supp indep
    (z_fiber_smooth R hI) J L G H site M N V hV W (z_section R hI) (z_split R hI) _).symm

variable [Nontrivial R] [HasFiniteBiproducts D]
variable (T : StrictLocalizedCells.TorusCells J L G R) (Z₀ : A)
variable (Q : StrictTorusSymbolInput.Standard J L G R T Z₀ M site N W V)

include P in
omit [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [J.CommShift ℤ] [L.CommShift ℤ] [HasShift D ℤ] [L.Additive] [Nontrivial R] [HasFiniteBiproducts D] in
theorem z_projection (i : SI)
    (hi : StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card μ) i≠0) :
    GradedSectionTotal.includeDegree (W.grading (CommRingCat.of Layer))
      (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card μ) i-I.card)
      (OriginalOrderedStrictSections.localEquiv J L G R (Fin 1) n B pos neg supp hf hs site M N V I.card _ idx
        (StrictCellTests.testAddEquiv J
          (StrictLocalizedCells.localCell J L G R T (Fin 1) n B pos neg supp hf hs I.card idx) _
          (OriginalCoordinateProjectionSymbols.projection J L G R T (Fin 1) n B pos neg supp hf hs
            I.card idx I μ (PathOriginalStrictCells.zBase R hI) site M N V Z₀ W Q i hi)))=
      PathOriginalLayerWordBasis.zBasis J L G R H site M N V hV W K hI (Pi.single i 1) := by
  rw [←z_standard_word J L G R H site M N V hV W K P hI i]
  let e := GradedMilnorWittSheafEquiv.equiv site N W (S:=CommRingCat.of Layer) (T:=CommRingCat.of Std)
    (PathOriginalStrictCells.zBase R hI).toRingEquiv
  apply e.injective
  change GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Layer) (T:=CommRingCat.of Std)
    (PathOriginalStrictCells.zBase R hI).toRingHom _=e (e.symm _)
  rw [RingEquiv.apply_symm_apply,GradedMilnorWittSheaf.pullback_degree]
  exact OriginalCoordinateProjectionSymbols.symbols J L G R T (Fin 1) n B pos neg supp hf hs
    I.card idx I μ (PathOriginalStrictCells.zBase R hI) site M N V hV Z₀ W Q i hi

#print axioms z_standard_word
#print axioms z_projection
end Z

end Verification.PathOriginalProjectionCoordinates
