/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathCanonicalSectionTotal
import Verification.PathOriginalYWordResidue
import Verification.PathOriginalZWordResidue
import Verification.GradedMilnorWittResidueNaturality

/-!
# Path Original Residue Transport

The full original adjacent source, including arbitrary sections rather
than only Laurent words, transports to the computed path coefficient residue.
-/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 4096
namespace Verification.PathOriginalResidueTransport
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
variable (hK : SheafContractionNaturality.Standard R site N K)

section Y
variable {d : ℕ} {I : Finset ℕ} (hI : Admissible (2*d) I)
variable (j : ℕ) (hj : j∈Finset.Icc 1 (2*d)) (ha : Addable I j)
local notation "B" => PathOriginalYPresentation.matrix (2*d)
local notation "hJ" => PathSignedFaceUnits.nextAdmissible hI j hj ha
local notation "Coef" => Coefficients R hI (1:R) 1
local notation "NewCoef" => Coefficients R hJ (1:R) 1
local notation "Target" => mutableSet (2*d) (insert j I)
local notation "v" => PathOriginalFaceIndex.selectedNormal (I:=I) j hj
local notation "New" => PathOriginalCoefficientTransport.Fiber (I:=insert j I) R Empty B
local notation "Source" => GlobalNormalFrame.ZeroLayer R Empty (2*d) ((Target).erase (v).val) B
local notation "pos" => positive_order B y_mutable
local notation "neg" => negative_order B y_mutable
local notation "supp" => support B y_mutable
local notation "indep" => independent B y_mutable hJ
local notation "hD" => matrix_zero_block Empty (2*d) Target B pos neg supp indep

def yResidue : W.Total (CommRingCat.of Source) →+ W.Total (CommRingCat.of New) :=
  (GradedMilnorWittLaurent.residue R site N W K New (y_fiber_smooth R hJ)).comp
    (GradedMilnorWittSheaf.pullback site N W
      (S:=CommRingCat.of Source) (T:=CommRingCat.of (LaurentBasepoint.Laurent New))
      (OriginalSourceLaurentGenerators.map R Empty (2*d) Target B v hD).toRingHom).toAddMonoidHom

include hK in
omit [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [J.Additive] [J.CommShift ℤ] [L.Additive] [L.CommShift ℤ] [HasShift D ℤ] in
theorem y_coordinates (a : W.Total (CommRingCat.of Coef)) :
    GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of New) (T:=CommRingCat.of NewCoef)
      (PathOriginalYCoefficient.coefficientEquiv R hJ).symm.toRingHom
      (yResidue R site N W K hI j hj ha
        (PathCanonicalSectionTotal.ySourceCoordinates J L G R H site M N V hV W hI j hj ha a))=
    PathOriginalYWordResidue.residue R hI j hj ha site N W K a := by
  rw [PathCanonicalSectionTotal.ySourceCoordinates_apply]
  change GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of New) (T:=CommRingCat.of NewCoef)
    (PathOriginalYCoefficient.coefficientEquiv R hJ).symm.toRingHom
    (GradedMilnorWittLaurent.residue R site N W K New (y_fiber_smooth R hJ)
      (GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Source)
        (T:=CommRingCat.of (LaurentBasepoint.Laurent New))
        (OriginalSourceLaurentGenerators.map R Empty (2*d) Target B v hD).toRingHom _))=_
  have hh := GradedMilnorWittResidueNaturality.total_naturality R New NewCoef site N
    (PathOriginalYCoefficient.coefficientEquiv R hJ).symm.toAlgHom K hK
    (y_fiber_smooth R hJ) (PathOriginalYWordResidue.smooth R hI j hj ha) W
    (GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Source)
      (T:=CommRingCat.of (LaurentBasepoint.Laurent New))
      (OriginalSourceLaurentGenerators.map R Empty (2*d) Target B v hD).toRingHom
      (GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Coef) (T:=CommRingCat.of Source)
        ((PathOriginalYFaceCoordinates.sourceEquiv R hI j hj ha).toAlgHom.comp
          ((toLayer R hI (1:R) 1))).toRingHom a))
  refine hh.symm.trans ?_
  rw [←RingHom.comp_apply,←GradedMilnorWittSheaf.pullback_comp,
    ←RingHom.comp_apply,←GradedMilnorWittSheaf.pullback_comp]
  rfl

include hK in
omit [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [J.Additive] [J.CommShift ℤ] [L.Additive] [L.CommShift ℤ] [HasShift D ℤ] in
theorem y_arbitrary (a : W.Total (CommRingCat.of Source)) :
    GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of New) (T:=CommRingCat.of NewCoef)
      (PathOriginalYCoefficient.coefficientEquiv R hJ).symm.toRingHom
      (yResidue R site N W K hI j hj ha a)=
    PathOriginalYWordResidue.residue R hI j hj ha site N W K
      ((PathCanonicalSectionTotal.ySourceCoordinates J L G R H site M N V hV W hI j hj ha).symm a) := by
  simpa only [RingEquiv.apply_symm_apply] using y_coordinates J L G R H site M N V hV W K hK hI j hj ha
    ((PathCanonicalSectionTotal.ySourceCoordinates J L G R H site M N V hV W hI j hj ha).symm a)

#print axioms yResidue
#print axioms y_coordinates
#print axioms y_arbitrary
end Y

section Z
variable {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
variable (j : ℕ) (hj : j∈Finset.Icc 1 n) (ha : Addable I j)
local notation "B" => PathOriginalZPresentation.matrix n
local notation "hJ" => PathSignedFaceUnits.nextAdmissible hI j hj ha
local notation "Coef" => Coefficients (PathOriginalZPresentation.Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1
local notation "NewCoef" => Coefficients (PathOriginalZPresentation.Coefficient R) hJ (LaurentPolynomialUniversal.parameter R) 1
local notation "Target" => mutableSet n (insert j I)
local notation "v" => PathOriginalFaceIndex.selectedNormal (I:=I) j hj
local notation "New" => PathOriginalCoefficientTransport.Fiber (I:=insert j I) R (Fin 1) B
local notation "Source" => GlobalNormalFrame.ZeroLayer R (Fin 1) n ((Target).erase (v).val) B
local notation "pos" => positive_order B z_mutable
local notation "neg" => negative_order B z_mutable
local notation "supp" => support B z_mutable
local notation "indep" => independent B z_mutable hJ
local notation "hD" => matrix_zero_block (Fin 1) n Target B pos neg supp indep

def zResidue : W.Total (CommRingCat.of Source) →+ W.Total (CommRingCat.of New) :=
  (GradedMilnorWittLaurent.residue R site N W K New (z_fiber_smooth R hJ)).comp
    (GradedMilnorWittSheaf.pullback site N W
      (S:=CommRingCat.of Source) (T:=CommRingCat.of (LaurentBasepoint.Laurent New))
      (OriginalSourceLaurentGenerators.map R (Fin 1) n Target B v hD).toRingHom).toAddMonoidHom

include hK in
omit [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [J.Additive] [J.CommShift ℤ] [L.Additive] [L.CommShift ℤ] [HasShift D ℤ] in
theorem z_coordinates (a : W.Total (CommRingCat.of Coef)) :
    GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of New) (T:=CommRingCat.of NewCoef)
      (PathOriginalZCoefficient.coefficientEquiv R hJ).symm.toRingHom
      (zResidue R site N W K hI j hj ha
        (PathCanonicalSectionTotal.zSourceCoordinates J L G R H site M N V hV W hI j hj ha a))=
    PathOriginalZWordResidue.residue R hI j hj ha site N W K a := by
  rw [PathCanonicalSectionTotal.zSourceCoordinates_apply]
  change GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of New) (T:=CommRingCat.of NewCoef)
    (PathOriginalZCoefficient.coefficientEquiv R hJ).symm.toRingHom
    (GradedMilnorWittLaurent.residue R site N W K New (z_fiber_smooth R hJ)
      (GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Source)
        (T:=CommRingCat.of (LaurentBasepoint.Laurent New))
        (OriginalSourceLaurentGenerators.map R (Fin 1) n Target B v hD).toRingHom _))=_
  have hh := GradedMilnorWittResidueNaturality.total_naturality R New NewCoef site N
    (PathOriginalZCoefficient.coefficientEquiv R hJ).symm.toAlgHom K hK
    (z_fiber_smooth R hJ) (PathOriginalZWordResidue.smooth R hI j hj ha) W
    (GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Source)
      (T:=CommRingCat.of (LaurentBasepoint.Laurent New))
      (OriginalSourceLaurentGenerators.map R (Fin 1) n Target B v hD).toRingHom
      (GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Coef) (T:=CommRingCat.of Source)
        ((PathOriginalZFaceCoordinates.sourceEquiv R hI j hj ha).toAlgHom.comp
          ((toLayer (PathOriginalZPresentation.Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1).restrictScalars R)).toRingHom a))
  refine hh.symm.trans ?_
  rw [←RingHom.comp_apply,←GradedMilnorWittSheaf.pullback_comp,
    ←RingHom.comp_apply,←GradedMilnorWittSheaf.pullback_comp]
  rfl

include hK in
omit [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [J.Additive] [J.CommShift ℤ] [L.Additive] [L.CommShift ℤ] [HasShift D ℤ] in
theorem z_arbitrary (a : W.Total (CommRingCat.of Source)) :
    GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of New) (T:=CommRingCat.of NewCoef)
      (PathOriginalZCoefficient.coefficientEquiv R hJ).symm.toRingHom
      (zResidue R site N W K hI j hj ha a)=
    PathOriginalZWordResidue.residue R hI j hj ha site N W K
      ((PathCanonicalSectionTotal.zSourceCoordinates J L G R H site M N V hV W hI j hj ha).symm a) := by
  simpa only [RingEquiv.apply_symm_apply] using z_coordinates J L G R H site M N V hV W K hK hI j hj ha
    ((PathCanonicalSectionTotal.zSourceCoordinates J L G R H site M N V hV W hI j hj ha).symm a)

#print axioms zResidue
#print axioms z_coordinates
#print axioms z_arbitrary
end Z

end Verification.PathOriginalResidueTransport
