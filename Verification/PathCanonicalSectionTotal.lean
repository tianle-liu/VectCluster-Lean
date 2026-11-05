/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalCanonicalSectionTotal
import Verification.PathCanonicalCoefficientSection
import Verification.PathOriginalYFaceCoordinates
import Verification.PathOriginalZFaceCoordinates

/-!
# Path Canonical Section Total

Actual original path-stratum sections in canonical coefficient
coordinates. The inverse is the literal toLayer inclusion, including the
finite-index cast of an adjacent source stratum.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.PathCanonicalSectionTotal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.PathCompression Verification.PathSignedStratumCoefficients
open Verification.PathOriginalStratumTransport Verification.PathOriginalIndependence
open Verification.PathCanonicalCoefficientSection
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

section Y
variable {d : ℕ} {I : Finset ℕ} (hI : Admissible (2*d) I)
local notation "B" => PathOriginalYPresentation.matrix (2*d)
local notation "Coef" => Coefficients R hI (1:R) 1
local notation "Fiber" => PathOriginalCoefficientTransport.Fiber (I:=I) R Empty B
local notation "Layer" => GlobalNormalFrame.ZeroLayer R Empty (2*d) (mutableSet (2*d) I) B
local notation "pos" => positive_order B y_mutable
local notation "neg" => negative_order B y_mutable
local notation "supp" => support B y_mutable
local notation "indep" => independent B y_mutable hI

def yProjection : W.Total (CommRingCat.of Layer) ≃+* W.Total (CommRingCat.of Fiber) :=
  OriginalCanonicalSectionTotal.equiv R Empty (2*d) (mutableSet (2*d) I) B pos neg supp indep
    (y_fiber_smooth R hI) J L G H site M N V hV W

def yCoordinates : W.Total (CommRingCat.of Coef) ≃+* W.Total (CommRingCat.of Layer) :=
  (GradedMilnorWittSheafEquiv.equiv site N W (S:=CommRingCat.of Coef) (T:=CommRingCat.of Fiber)
    (PathOriginalYCoefficient.coefficientEquiv R hI).toRingEquiv).trans
    (yProjection J L G R H site M N V hV W hI).symm

omit [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [J.Additive] [J.CommShift ℤ] [L.Additive] [L.CommShift ℤ] [HasShift D ℤ] in
theorem yCoordinates_apply (a : W.Total (CommRingCat.of Coef)) :
    yCoordinates J L G R H site M N V hV W hI a=
      GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Coef) (T:=CommRingCat.of Layer)
        ((PathOriginalYStratum.equiv R hI).toAlgHom.comp ((toLayer R hI (1:R) 1))).toRingHom a := by
  change (OriginalCanonicalSectionTotal.equiv R Empty (2*d) (mutableSet (2*d) I) B pos neg supp indep
    (y_fiber_smooth R hI) J L G H site M N V hV W).symm
    (GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Coef) (T:=CommRingCat.of Fiber)
      (PathOriginalYCoefficient.coefficientEquiv R hI).toRingHom a)=_
  rw [OriginalCanonicalSectionTotal.inverse_section R Empty (2*d) (mutableSet (2*d) I) B pos neg supp indep
    (y_fiber_smooth R hI) J L G H site M N V hV W (y_section R hI) (y_split R hI)]
  rw [←RingHom.comp_apply,←GradedMilnorWittSheaf.pullback_comp]
  have he:=congrArg AlgHom.toRingHom (y_inclusion R hI)
  change ((y_section R hI).toRingHom.comp (PathOriginalYCoefficient.coefficientEquiv R hI).toRingHom)=_ at he
  rw [he]

variable (j : ℕ) (hj : j∈Finset.Icc 1 (2*d)) (ha : Addable I j)
local notation "Source" => GlobalNormalFrame.ZeroLayer R Empty (2*d)
  ((mutableSet (2*d) (insert j I)).erase (PathOriginalFaceIndex.selectedNormal (I:=I) j hj).val) B

def ySourceCoordinates : W.Total (CommRingCat.of Coef) ≃+* W.Total (CommRingCat.of Source) :=
  (yCoordinates J L G R H site M N V hV W hI).trans
    (GradedMilnorWittSheafEquiv.equiv site N W (S:=CommRingCat.of Layer) (T:=CommRingCat.of Source)
      (OriginalZeroLayerCast.equiv R Empty (2*d) B (PathOriginalFaceIndex.mutable_erase j hj ha).symm).toRingEquiv)

omit [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [J.Additive] [J.CommShift ℤ] [L.Additive] [L.CommShift ℤ] [HasShift D ℤ] in
theorem ySourceCoordinates_apply (a : W.Total (CommRingCat.of Coef)) :
    ySourceCoordinates J L G R H site M N V hV W hI j hj ha a=
      GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Coef) (T:=CommRingCat.of Source)
        ((PathOriginalYFaceCoordinates.sourceEquiv R hI j hj ha).toAlgHom.comp ((toLayer R hI (1:R) 1))).toRingHom a := by
  change GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Layer) (T:=CommRingCat.of Source)
    (OriginalZeroLayerCast.equiv R Empty (2*d) B (PathOriginalFaceIndex.mutable_erase j hj ha).symm).toRingHom
    (yCoordinates J L G R H site M N V hV W hI a)=_
  rw [yCoordinates_apply,←RingHom.comp_apply,←GradedMilnorWittSheaf.pullback_comp]
  rfl

#print axioms yProjection
#print axioms yCoordinates
#print axioms yCoordinates_apply
#print axioms ySourceCoordinates
#print axioms ySourceCoordinates_apply
end Y

section Z
variable {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
local notation "B" => PathOriginalZPresentation.matrix n
local notation "Coef" => Coefficients (PathOriginalZPresentation.Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1
local notation "Fiber" => PathOriginalCoefficientTransport.Fiber (I:=I) R (Fin 1) B
local notation "Layer" => GlobalNormalFrame.ZeroLayer R (Fin 1) n (mutableSet n I) B
local notation "pos" => positive_order B z_mutable
local notation "neg" => negative_order B z_mutable
local notation "supp" => support B z_mutable
local notation "indep" => independent B z_mutable hI

def zProjection : W.Total (CommRingCat.of Layer) ≃+* W.Total (CommRingCat.of Fiber) :=
  OriginalCanonicalSectionTotal.equiv R (Fin 1) n (mutableSet n I) B pos neg supp indep
    (z_fiber_smooth R hI) J L G H site M N V hV W

def zCoordinates : W.Total (CommRingCat.of Coef) ≃+* W.Total (CommRingCat.of Layer) :=
  (GradedMilnorWittSheafEquiv.equiv site N W (S:=CommRingCat.of Coef) (T:=CommRingCat.of Fiber)
    (PathOriginalZCoefficient.coefficientEquiv R hI).toRingEquiv).trans
    (zProjection J L G R H site M N V hV W hI).symm

omit [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [J.Additive] [J.CommShift ℤ] [L.Additive] [L.CommShift ℤ] [HasShift D ℤ] in
theorem zCoordinates_apply (a : W.Total (CommRingCat.of Coef)) :
    zCoordinates J L G R H site M N V hV W hI a=
      GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Coef) (T:=CommRingCat.of Layer)
        ((PathOriginalZStratum.equiv R hI).toAlgHom.comp ((toLayer (PathOriginalZPresentation.Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1).restrictScalars R)).toRingHom a := by
  change (OriginalCanonicalSectionTotal.equiv R (Fin 1) n (mutableSet n I) B pos neg supp indep
    (z_fiber_smooth R hI) J L G H site M N V hV W).symm
    (GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Coef) (T:=CommRingCat.of Fiber)
      (PathOriginalZCoefficient.coefficientEquiv R hI).toRingHom a)=_
  rw [OriginalCanonicalSectionTotal.inverse_section R (Fin 1) n (mutableSet n I) B pos neg supp indep
    (z_fiber_smooth R hI) J L G H site M N V hV W (z_section R hI) (z_split R hI)]
  rw [←RingHom.comp_apply,←GradedMilnorWittSheaf.pullback_comp]
  have he:=congrArg AlgHom.toRingHom (z_inclusion R hI)
  change ((z_section R hI).toRingHom.comp (PathOriginalZCoefficient.coefficientEquiv R hI).toRingHom)=_ at he
  rw [he]

variable (j : ℕ) (hj : j∈Finset.Icc 1 n) (ha : Addable I j)
local notation "Source" => GlobalNormalFrame.ZeroLayer R (Fin 1) n
  ((mutableSet n (insert j I)).erase (PathOriginalFaceIndex.selectedNormal (I:=I) j hj).val) B

def zSourceCoordinates : W.Total (CommRingCat.of Coef) ≃+* W.Total (CommRingCat.of Source) :=
  (zCoordinates J L G R H site M N V hV W hI).trans
    (GradedMilnorWittSheafEquiv.equiv site N W (S:=CommRingCat.of Layer) (T:=CommRingCat.of Source)
      (OriginalZeroLayerCast.equiv R (Fin 1) n B (PathOriginalFaceIndex.mutable_erase j hj ha).symm).toRingEquiv)

omit [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [J.Additive] [J.CommShift ℤ] [L.Additive] [L.CommShift ℤ] [HasShift D ℤ] in
theorem zSourceCoordinates_apply (a : W.Total (CommRingCat.of Coef)) :
    zSourceCoordinates J L G R H site M N V hV W hI j hj ha a=
      GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Coef) (T:=CommRingCat.of Source)
        ((PathOriginalZFaceCoordinates.sourceEquiv R hI j hj ha).toAlgHom.comp ((toLayer (PathOriginalZPresentation.Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1).restrictScalars R)).toRingHom a := by
  change GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Layer) (T:=CommRingCat.of Source)
    (OriginalZeroLayerCast.equiv R (Fin 1) n B (PathOriginalFaceIndex.mutable_erase j hj ha).symm).toRingHom
    (zCoordinates J L G R H site M N V hV W hI a)=_
  rw [zCoordinates_apply,←RingHom.comp_apply,←GradedMilnorWittSheaf.pullback_comp]
  rfl

#print axioms zProjection
#print axioms zCoordinates
#print axioms zCoordinates_apply
#print axioms zSourceCoordinates
#print axioms zSourceCoordinates_apply
end Z

end Verification.PathCanonicalSectionTotal
