/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OrderedFlagEvaluation
import Verification.OrderedOptionFlagNumbering
import Verification.AffineShiftedThomSections

/-!
# Ordered Affine Flag Evaluation

The flag orientation formula on literal affine-relative-Thom tests.
The comparison to finite numbered tests is eliminated by the proved
none-first numbering equality and inverse coordinate maps.
-/
noncomputable section
namespace Verification.OrderedAffineFlagEvaluation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.OrderedFlagNormalCoordinates Verification.OrderedFlagThomFactorization
universe w₁ w₂
variable {A₀ C : Type*} [Category A₀] [Abelian A₀] [HasDerivedCategory.{w₁} A₀]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A₀ ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R A ι : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype ι] [LinearOrder ι]
variable (x : ι → A) (v : ι)
local notation "S" => CoordinateFlag.ClosedAll A ι x v
local notation "Q" => A ⧸ ConormalFrame.ideal x
local notation "Normals" => FlagNormalCoordinates.Normals ι v
local instance optionOrder : LinearOrder Normals :=
  inferInstanceAs (LinearOrder (WithBot (CoordinateFlag.Old ι v)))

theorem numberingIso_eq : numberingIso ι v R A x G =
    OrderedThomSections.thomIso Normals (count ι v)
      (OrderedOptionFlagNumbering.card_count ι v) S G := by
  simp only [numberingIso,normalNumbering,OrderedThomSections.thomIso,
    OrderedOptionFlagNumbering.normalOrder_numbering]
  rfl

variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A₀) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (T : LocalizedThomSections.Standard J L G R site M N)
variable (O : ThomPermutationInput.Standard J L G R site M N T)
variable (hT : LocalizedThomSections.Naturality J L G R site M N T)
variable (hs : Algebra.Smooth R (CoordinateFlag.ClosedAll A ι x v))
variable (hq : Algebra.Smooth R (A ⧸ ConormalFrame.ideal x)) (j : ℤ)
local notation "F" => AffineRelativeThom.theory R Normals G
local notation "Z" => J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(count ι v : ℤ)) (M j)))
local notation "e" => AlgEquiv.symm (CoordinateFlagTotalQuotient.equiv R A ι x v)

include hs in
omit [J.Additive] [L.Additive] in
theorem affine_evaluation
    (a : L.obj (DerivedCategory.Q.obj ((F).obj
      (Opposite.op (CommRingCat.mkUnder (CommRingCat.of R) S)))) ⟶ Z) :
    AffineShiftedThomSections.evaluate J L G R S Normals (count ι v)
      (OrderedOptionFlagNumbering.card_count ι v) site M N T hs j a =
    OrderedThomEvaluation.finEvaluate J L G R site M N T S (count ι v) hs j
      (L.map (numberingIso ι v R A x G).inv ≫
        L.map (RelativeProductConeNaturality.derivedIso R S Normals G).inv ≫ a) := by
  change OrderedThomSections.evaluate _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (L.map (RelativeProductConeNaturality.derivedIso R S Normals G).inv ≫ a)=_
  rw [OrderedThomEvaluation.evaluate_apply,numberingIso_eq G R A ι x v]

include hT hs hq in
omit [J.Additive] [L.Additive] in
theorem full_quotient_affine_evaluation
    (a : L.obj (DerivedCategory.Q.obj ((F).obj
      (Opposite.op (CommRingCat.mkUnder (CommRingCat.of R) S)))) ⟶ Z) :
    (N (j-count ι v)).val.map (Spec.map (CommRingCat.ofHom (e).toRingHom)).op
      (OrderedThomSections.evaluate ι (count ι v) (OrderedFlagNumbering.card_count ι v) Q
        J L G R site M N T hq j
        (L.map (FlagNormalCoordinates.thomIso R A ι x v G).hom ≫ a)) =
    (O.orientation S (j-count ι v) (-1) ^
      ((Finset.univ.erase v).filter (fun i : ι => i < v)).card)
      (AffineShiftedThomSections.evaluate J L G R S Normals (count ι v)
        (OrderedOptionFlagNumbering.card_count ι v) site M N T hs j a) := by
  rw [affine_evaluation J L G R A ι x v site M N T hs j]
  have h := OrderedFlagEvaluation.full_quotient_flag_evaluation J L G R A ι x v
    site M N T O hT hs hq j
    (L.map (numberingIso ι v R A x G).inv ≫
      L.map (RelativeProductConeNaturality.derivedIso R S Normals G).inv ≫ a)
  simpa only [← Functor.mapIso_hom,← Functor.mapIso_inv,Category.assoc,
    Iso.hom_inv_id_assoc] using h

#print axioms optionOrder
#print axioms numberingIso_eq
#print axioms affine_evaluation
#print axioms full_quotient_affine_evaluation
end Verification.OrderedAffineFlagEvaluation
