/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.IntegralSplitting
import Verification.FinitePerturbation

/-!
# Contraction Homology

For every normalized contraction, the actual fixed module of 1-UH-HU is the
literal homology quotient ker U/im U.  This applies after degree/weight
normalization, so its finite basis does not depend on the earlier choice of section.
-/

namespace Verification.ContractionHomology

open Verification.FinitePerturbation

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (U H : Module.End R M)
variable (hU : U*U=0) (hH : H*H=0) (hHUH : H*U*H=H) (hUHU : U*H*U=U)

/-- Actual fixed vectors of the specified contraction's survivor projection. -/
def survivorModule : Submodule R M := LinearMap.ker (pureProjection U H-LinearMap.id)

theorem fixed_property (x : survivorModule U H) : pureProjection U H x.val=x.val :=
  sub_eq_zero.mp x.property

include hU hUHU in
/-- Every survivor is an actual cycle. -/
theorem survivor_cycle (x : survivorModule U H) : U x.val = 0 := by
  have he := LinearMap.congr_fun (u_pureProjection U H hU hUHU) x.val
  change U (pureProjection U H x.val)=0 at he
  rw [fixed_property U H x] at he
  exact he

/-- Projection of cycles onto the specified survivor module. -/
def projectCycles : LinearMap.ker U →ₗ[R] survivorModule U H where
  toFun x := ⟨pureProjection U H x.val, by
    have he := LinearMap.congr_fun (pureProjection_square U H hU hH hHUH hUHU) x.val
    change pureProjection U H (pureProjection U H x.val)=pureProjection U H x.val at he
    change pureProjection U H (pureProjection U H x.val)-pureProjection U H x.val=0
    exact sub_eq_zero.mpr he⟩
  map_add' x y := by apply Subtype.ext; exact map_add (pureProjection U H) _ _
  map_smul' a x := by apply Subtype.ext; exact map_smul (pureProjection U H) _ _

theorem projectCycles_boundaries : Verification.IntegralSplitting.boundaryCycles U ≤
    LinearMap.ker (projectCycles U H hU hH hHUH hUHU) := by
  intro x hx
  obtain ⟨y,hy⟩ := hx
  apply Subtype.ext
  change pureProjection U H x.val=0
  change U y=x.val at hy
  rw [← hy]
  exact LinearMap.congr_fun (pureProjection_u U H hU hUHU) y

/-- Homology classes map into actual survivors by quotient descent. -/
def fromHomology : Verification.IntegralSplitting.Homology U →ₗ[R] survivorModule U H :=
  (Verification.IntegralSplitting.boundaryCycles U).liftQ
    (projectCycles U H hU hH hHUH hUHU) (projectCycles_boundaries U H hU hH hHUH hUHU)

/-- The inverse is the actual cycle's class in ker U/im U. -/
def toHomology : survivorModule U H →ₗ[R] Verification.IntegralSplitting.Homology U :=
  (Verification.IntegralSplitting.boundaryCycles U).mkQ.comp (show survivorModule U H →ₗ[R] LinearMap.ker U from {
    toFun x := ⟨x.val,survivor_cycle U H hU hUHU x⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl })

/-- Projecting a cycle changes it only by an actual boundary. -/
theorem to_from_homology (q : Verification.IntegralSplitting.Homology U) :
    toHomology U H hU hUHU (fromHomology U H hU hH hHUH hUHU q)=q := by
  refine Submodule.Quotient.induction_on (Verification.IntegralSplitting.boundaryCycles U) q ?_
  intro x
  change (Verification.IntegralSplitting.boundaryCycles U).mkQ
    ⟨pureProjection U H x.val, _⟩ = (Verification.IntegralSplitting.boundaryCycles U).mkQ x
  apply (Submodule.Quotient.eq _).mpr
  change pureProjection U H x.val-x.val ∈ LinearMap.range U
  refine ⟨-H x.val, ?_⟩
  have hx : U x.val=0 := x.property
  change U (-H x.val)=((LinearMap.id-U*H-H*U : Module.End R M) x.val)-x.val
  simp only [LinearMap.sub_apply, LinearMap.id_apply, Module.End.mul_apply, map_neg, hx, map_zero]
  abel

/-- On an actual fixed vector the projection is exactly the identity. -/
theorem from_to_homology (x : survivorModule U H) :
    fromHomology U H hU hH hHUH hUHU (toHomology U H hU hUHU x)=x := by
  apply Subtype.ext
  exact fixed_property U H x

/-- The precise survivor module is canonically identified with actual homology. -/
def homologyEquiv : Verification.IntegralSplitting.Homology U ≃ₗ[R] survivorModule U H where
  toLinearMap := fromHomology U H hU hH hHUH hUHU
  invFun := toHomology U H hU hUHU
  left_inv := to_from_homology U H hU hH hHUH hUHU
  right_inv := from_to_homology U H hU hH hHUH hUHU

section FiniteTF

variable [IsDomain R] [IsPrincipalIdealRing R] [Module.Free R M] [Module.Finite R M]
variable [NoZeroSMulDivisors R (Verification.IntegralSplitting.Homology U)]

/-- A finite basis for this normalized survivor module, obtained from TF rather than assumed. -/
noncomputable def survivorBasis :
    Basis (Fin (Module.finrank R (Verification.IntegralSplitting.Homology U))) R (survivorModule U H) :=
  (Module.finBasis R (Verification.IntegralSplitting.Homology U)).map
    (homologyEquiv U H hU hH hHUH hUHU)

end FiniteTF

#print axioms survivorModule
#print axioms fixed_property
#print axioms survivor_cycle
#print axioms projectCycles
#print axioms projectCycles_boundaries
#print axioms fromHomology
#print axioms toHomology
#print axioms to_from_homology
#print axioms from_to_homology
#print axioms homologyEquiv
#print axioms survivorBasis

end Verification.ContractionHomology
