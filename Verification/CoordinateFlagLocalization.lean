/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinateFlag
import Verification.QuotientAwayAlgebra

/-!
# Coordinate Flag Localization

The old closed subscheme after localizing the ambient chart is exactly
the principal open of the old closed subscheme, with the actual quotient
and localization maps.
-/
noncomputable section
namespace Verification.CoordinateFlagLocalization
open Verification.CoordinateFlag
variable (R A ι : Type) [CommRing R] [CommRing A] [Algebra R A]
variable (x : ι → A) (v : ι)

abbrev Ambient := Localization.Away (x v)
def coordinate (i : Old ι v) : Ambient A ι x v := algebraMap A _ (x i.val)

theorem ideal_eq : ConormalFrame.ideal (coordinate A ι x v) =
    (oldIdeal A ι x v).map (algebraMap A (Ambient A ι x v)) := by
  simp only [ConormalFrame.ideal, oldIdeal, Ideal.map_span, ← Set.range_comp]
  rfl

def closedEquiv : (Ambient A ι x v ⧸ ConormalFrame.ideal (coordinate A ι x v)) ≃ₐ[R]
    OpenOld A ι x v :=
  (Ideal.quotientEquivAlgOfEq R (ideal_eq A ι x v)).trans
    (QuotientAwayAlgebra.equiv R A (oldIdeal A ι x v) (x v))

theorem closedEquiv_generator (a : A) :
    closedEquiv R A ι x v (Ideal.Quotient.mk (ConormalFrame.ideal (coordinate A ι x v))
      (algebraMap A (Ambient A ι x v) a)) =
      algebraMap (ClosedOld A ι x v) (OpenOld A ι x v) (Ideal.Quotient.mk (oldIdeal A ι x v) a) := by
  dsimp only [closedEquiv, AlgEquiv.trans_apply]
  rw [Ideal.quotientEquivAlgOfEq_mk]
  exact QuotientAwayAlgebra.equiv_generator R A (oldIdeal A ι x v) (x v) a

def openMap : Ambient A ι x v →ₐ[R] OpenOld A ι x v :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (x v))
    (f := (IsScalarTower.toAlgHom R (ClosedOld A ι x v) (OpenOld A ι x v)).comp
      (Ideal.Quotient.mkₐ R (oldIdeal A ι x v))) (by
        intro m
        obtain ⟨n, hn⟩ := m.property
        change IsUnit (algebraMap (ClosedOld A ι x v) _ (Ideal.Quotient.mk _ m.val))
        rw [← hn, map_pow, map_pow]
        exact (IsLocalization.Away.algebraMap_isUnit (parameter A ι x v)).pow n)

theorem openMap_generator (a : A) :
    openMap R A ι x v (algebraMap A (Ambient A ι x v) a) =
    algebraMap (ClosedOld A ι x v) (OpenOld A ι x v) (Ideal.Quotient.mk (oldIdeal A ι x v) a) :=
  IsLocalization.lift_eq _ a

theorem closed_square :
    (closedEquiv R A ι x v).toAlgHom.comp (Ideal.Quotient.mkₐ R (ConormalFrame.ideal (coordinate A ι x v))) =
      openMap R A ι x v := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (x v))
  ext a
  exact (closedEquiv_generator R A ι x v a).trans (openMap_generator R A ι x v a).symm

open CategoryTheory AlgebraicGeometry Opposite

def schemeIso : Spec (CommRingCat.of (OpenOld A ι x v)) ≅
    Spec (CommRingCat.of (Ambient A ι x v ⧸ ConormalFrame.ideal (coordinate A ι x v))) :=
  Scheme.Spec.mapIso (closedEquiv R A ι x v).toRingEquiv.toCommRingCatIso.op

theorem scheme_closed_square :
    (schemeIso R A ι x v).hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (ConormalFrame.ideal (coordinate A ι x v)))) =
    Spec.map (CommRingCat.ofHom (openMap R A ι x v).toRingHom) := by
  change Spec.map (CommRingCat.ofHom (closedEquiv R A ι x v).toRingHom) ≫ _ = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  exact congrArg (fun f => CommRingCat.ofHom f.toRingHom) (closed_square R A ι x v)

instance ambient_open : IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap A (Ambient A ι x v)))) := inferInstance

instance closed_open : IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap (ClosedOld A ι x v) (OpenOld A ι x v)))) := inferInstance

#print axioms Ambient
#print axioms coordinate
#print axioms ideal_eq
#print axioms closedEquiv
#print axioms closedEquiv_generator
#print axioms openMap
#print axioms openMap_generator
#print axioms closed_square
#print axioms schemeIso
#print axioms scheme_closed_square
#print axioms ambient_open
#print axioms closed_open
end Verification.CoordinateFlagLocalization
