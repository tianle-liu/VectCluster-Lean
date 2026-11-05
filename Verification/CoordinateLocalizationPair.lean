/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinateFlagExcision
import Verification.CoordinatePairMap

/-!
# Coordinate Localization Pair

The principal-open old-coordinate pair in a coordinate flag is the
literal pair on A[x_v inverse]. Its coordinate maps and localization-cone
isomorphisms are constructed from the actual open immersion.
-/
noncomputable section
namespace Verification.CoordinateLocalizationPair
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.CoordinateFlag Verification.CoordinatePurityInput
variable (A ι : Type) [CommRing A] [Fintype ι] [DecidableEq ι] (x : ι → A) (v : ι)

abbrev OpenRing := Localization.Away (x v)
def coordinate (i : Old ι v) : OpenRing A ι x v := algebraMap A _ (x i.val)
def chart : (Spec (CommRingCat.of A)).Opens := PrimeSpectrum.basicOpen (x v)
def inclusion : Spec (CommRingCat.of (OpenRing A ι x v)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A _))

instance inclusion_open : IsOpenImmersion (inclusion A ι x v) :=
  inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (x v))))))

omit [Fintype ι] [DecidableEq ι] in
theorem inclusion_range : Set.range (inclusion A ι x v).base = (chart A ι x v : Set (Spec (CommRingCat.of A))) :=
  PrimeSpectrum.localization_away_comap_range (OpenRing A ι x v) (x v)

def ambientIso : Spec (CommRingCat.of (OpenRing A ι x v)) ≅ (chart A ι x v).toScheme :=
  IsOpenImmersion.isoOfRangeEq (inclusion A ι x v) (chart A ι x v).ι
    ((inclusion_range A ι x v).trans (Scheme.Opens.range_ι _).symm)

omit [Fintype ι] [DecidableEq ι] in
theorem ambientIso_inclusion : (ambientIso A ι x v).hom ≫ (chart A ι x v).ι = inclusion A ι x v :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

omit [Fintype ι] [DecidableEq ι] in
theorem puncture_preimage : inclusion A ι x v ⁻¹ᵁ oldComplement A ι x v =
    puncture (OpenRing A ι x v) (Old ι v) (coordinate A ι x v) :=
  CoordinatePairMap.puncture_preimage (oldCoordinate A ι x v) (coordinate A ι x v)
    (algebraMap A (OpenRing A ι x v)) (fun _ => rfl)

omit [Fintype ι] [DecidableEq ι] in
theorem puncture_image : inclusion A ι x v ''ᵁ puncture (OpenRing A ι x v) (Old ι v) (coordinate A ι x v) =
    oldComplement A ι x v ⊓ chart A ι x v := by
  rw [← puncture_preimage,Scheme.Hom.image_preimage_eq_opensRange_inter]
  have hr : (inclusion A ι x v).opensRange = chart A ι x v :=
    TopologicalSpace.Opens.ext (inclusion_range A ι x v)
  rw [hr,inf_comm]

def punctureIso : (puncture (OpenRing A ι x v) (Old ι v) (coordinate A ι x v)).toScheme ≅
    (oldComplement A ι x v ⊓ chart A ι x v).toScheme :=
  (inclusion A ι x v).isoImage _ ≪≫ (Spec (CommRingCat.of A)).isoOfEq (puncture_image A ι x v)

omit [Fintype ι] [DecidableEq ι] in
theorem punctureIso_square : (puncture (OpenRing A ι x v) (Old ι v) (coordinate A ι x v)).ι ≫
    (ambientIso A ι x v).hom =
      (punctureIso A ι x v).hom ≫ (Spec (CommRingCat.of A)).homOfLE inf_le_right := by
  rw [← cancel_mono (chart A ι x v).ι]
  simp only [Category.assoc,ambientIso_inclusion,Scheme.homOfLE_ι,punctureIso,Iso.trans_hom,
    Scheme.isoOfEq_hom_ι,Scheme.Hom.isoImage_hom_ι]

universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)

def relativeIso : relative (OpenRing A ι x v) (Old ι v) (coordinate A ι x v) G ≅
    CoordinateFlagExcision.principalCone A ι x v G :=
  ConeDerivedComparison.coneIso _ _ (G.map (punctureIso A ι x v).hom)
    (G.map (ambientIso A ι x v).hom) (by
      change G.map _ ≫ G.map _ = G.map _ ≫ G.map _
      rw [← CategoryTheory.Functor.map_comp,← CategoryTheory.Functor.map_comp]
      exact congrArg G.map (punctureIso_square A ι x v))

def oldRelativeIso : relative (OpenRing A ι x v) (Old ι v) (coordinate A ι x v) G ≅ oldRelative A ι x v G :=
  relativeIso A ι x v G ≪≫ CoordinateFlagExcision.relativeIso A ι x v G E

#print axioms OpenRing
#print axioms coordinate
#print axioms chart
#print axioms inclusion
#print axioms inclusion_open
#print axioms inclusion_range
#print axioms ambientIso
#print axioms ambientIso_inclusion
#print axioms puncture_preimage
#print axioms puncture_image
#print axioms punctureIso
#print axioms punctureIso_square
#print axioms relativeIso
#print axioms oldRelativeIso
end Verification.CoordinateLocalizationPair
