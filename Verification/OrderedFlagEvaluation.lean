/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OrderedFlagBaseFactorization
import Verification.OrderedThomPermutationEvaluation

/-!
# Ordered Flag Evaluation

The genuine flag action in canonical numbered coefficient tests,
including the pullback from the literal full-coordinate quotient.
-/
noncomputable section
namespace Verification.OrderedFlagEvaluation
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
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A₀) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (T : LocalizedThomSections.Standard J L G R site M N)
variable (O : ThomPermutationInput.Standard J L G R site M N T)
variable (hT : LocalizedThomSections.Naturality J L G R site M N T)
variable (hs : Algebra.Smooth R (CoordinateFlag.ClosedAll A ι x v))
variable (hq : Algebra.Smooth R (A ⧸ ConormalFrame.ideal x)) (j : ℤ)
local notation "S" => CoordinateFlag.ClosedAll A ι x v
local notation "Q" => A ⧸ ConormalFrame.ideal x
local notation "F" => Fin (count ι v)
local notation "e" => AlgEquiv.symm (CoordinateFlagTotalQuotient.equiv R A ι x v)

omit [J.Additive] [L.Additive] in
theorem flag_fin_evaluation
    (a : L.obj (LocalizedThomSections.thom G S F) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(count ι v : ℤ)) (M j)))) :
    OrderedThomEvaluation.finEvaluate J L G R site M N T S (count ι v) hs j
      (L.map (increasingIso ι v R A x G).inv ≫
        (L.map (FlagNormalCoordinates.thomIso R A ι x v G).hom ≫
          L.map (RelativeProductConeNaturality.derivedIso R S (FlagNormalCoordinates.Normals ι v) G).hom ≫
            L.map (numberingIso ι v R A x G).hom) ≫ a) =
    (O.orientation S (j-count ι v) (-1) ^
      ((Finset.univ.erase v).filter (fun i : ι => i < v)).card)
      (OrderedThomEvaluation.finEvaluate J L G R site M N T S (count ι v) hs j a) := by
  have hh := congrArg (fun f => L.map f) (actual_thom_factorization ι v R A x G)
  simp only [Functor.map_comp] at hh
  rw [hh]
  simp only [← Category.assoc]
  rw [← Functor.map_comp,Iso.inv_hom_id,CategoryTheory.Functor.map_id,Category.id_comp]
  rw [OrderedThomPermutationEvaluation.fin_permutation J L G R site M N T O,
    Equiv.Perm.sign_symm,OrderedFlagNormalCoordinates.insertion_sign,map_pow]

include hT in
omit [J.Additive] [L.Additive] in
theorem increasing_evaluation
    (a : L.obj (CoordinatePurityInput.normalThom A ι x G) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(count ι v : ℤ)) (M j)))) :
    OrderedThomEvaluation.finEvaluate J L G R site M N T S (count ι v) hs j
      (L.map (increasingIso ι v R A x G).inv ≫ a) =
    (N (j-count ι v)).val.map (Spec.map (CommRingCat.ofHom (e).toRingHom)).op
      (OrderedThomSections.evaluate ι (count ι v) (OrderedFlagNumbering.card_count ι v) Q
        J L G R site M N T hq j a) := by
  rw [OrderedFlagBaseFactorization.increasing_inverse,Functor.map_comp,Category.assoc,
    OrderedThomBaseChange.base_inv,OrderedThomEvaluation.evaluate_apply]
  exact OrderedThomEvaluation.fin_naturality J L G R site M N T Q (count ι v) hT S hq hs (e).toAlgHom j _

include hT in
omit [J.Additive] [L.Additive] in
theorem full_quotient_flag_evaluation
    (a : L.obj (LocalizedThomSections.thom G S F) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(count ι v : ℤ)) (M j)))) :
    (N (j-count ι v)).val.map (Spec.map (CommRingCat.ofHom (e).toRingHom)).op
      (OrderedThomSections.evaluate ι (count ι v) (OrderedFlagNumbering.card_count ι v) Q
        J L G R site M N T hq j
        ((L.map (FlagNormalCoordinates.thomIso R A ι x v G).hom ≫
          L.map (RelativeProductConeNaturality.derivedIso R S (FlagNormalCoordinates.Normals ι v) G).hom ≫
            L.map (numberingIso ι v R A x G).hom) ≫ a)) =
    (O.orientation S (j-count ι v) (-1) ^
      ((Finset.univ.erase v).filter (fun i : ι => i < v)).card)
      (OrderedThomEvaluation.finEvaluate J L G R site M N T S (count ι v) hs j a) := by
  rw [← increasing_evaluation J L G R A ι x v site M N T hT hs hq j]
  exact flag_fin_evaluation J L G R A ι x v site M N T O hs j a

#print axioms flag_fin_evaluation
#print axioms increasing_evaluation
#print axioms full_quotient_flag_evaluation
end Verification.OrderedFlagEvaluation
