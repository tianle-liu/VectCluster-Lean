/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOpenLayer
import Verification.PathZeroRing
import Verification.SingleLaurent
import Verification.UniversalExchangeChart
import Verification.PrincipalConormal
import Mathlib.RingTheory.Localization.Integral

/-!
# Hyperbola Geometry

The closed hypersurface xy=1 is the actual one-dimensional torus.
This uses the already constructed path principal-open maps: on this
hypersurface x is a unit, so that principal open is the whole scheme.
-/
noncomputable section
namespace Verification.HyperbolaGeometry
open MvPolynomial Verification.PathPresentation
variable (R : Type) [CommRing R]
attribute [local instance] MvPolynomial.algebraMvPolynomial

abbrev Plane := UniversalExchangeChart.Polynomial R (Fin 1)
def equation : Plane R := X (Sum.inl (0 : Fin 1)) * X (Sum.inr (0 : Fin 1)) - 1
abbrev Closed := Plane R ⧸ Ideal.span {equation R}

theorem relation_eq (i : Fin 1) : relation (1 : R) 0 i = equation R := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change X (Sum.inl (0 : Fin 1)) * X (Sum.inr (0 : Fin 1)) -
    boundary (C (1 : R)) (C 0) (fun j : Fin 1 => X (Sum.inl j)) 0 -
    boundary (C (1 : R)) (C 0) (fun j : Fin 1 => X (Sum.inl j)) (Fin.last 2) = _
  rw [boundary_zero, boundary_last]
  simp [equation]

theorem ideal_eq : relations 1 (1 : R) 0 = Ideal.span {equation R} := by
  unfold relations
  congr 1
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    exact Set.mem_singleton_iff.mpr (relation_eq R i)
  · intro hp
    exact ⟨0, (relation_eq R 0).trans (Set.mem_singleton_iff.mp hp).symm⟩

def closedPathEquiv : Closed R ≃ₐ[R] PathAlgebra 1 (1 : R) 0 :=
  Ideal.quotientEquivAlgOfEq R (ideal_eq R).symm

theorem path_coordinate_unit : IsUnit (x (n := 1) (1 : R) 0 0) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨y (n := 1) (1 : R) 0 0, ?_⟩
  have h := equations 1 (1 : R) 0 (0 : Fin 1)
  change x (n := 1) (1 : R) 0 0 * y (1 : R) 0 0 =
    boundary (algebraMap R _ 1) (algebraMap R _ 0) (x (1 : R) 0) 0 +
    boundary (algebraMap R _ 1) (algebraMap R _ 0) (x (1 : R) 0) (Fin.last 2) at h
  simpa only [boundary_zero, boundary_last, map_one, map_zero, add_zero] using h

def pathOpenEquiv : PathAlgebra 1 (1 : R) 0 ≃ₐ[R] PathOpenLayer.Open 0 (1 : R) 0 :=
  (IsLocalization.atUnit (PathAlgebra 1 (1 : R) 0) (PathOpenLayer.Open 0 (1 : R) 0)
    (x (n := 1) (1 : R) 0 0) (path_coordinate_unit R)).restrictScalars R

def closedEquiv : Closed R ≃ₐ[R] SingleLaurent.Laurent.{0,0} R :=
  ((closedPathEquiv R).trans (pathOpenEquiv R)).trans
    ((PathOpenLayer.openEquiv.{0,0} 0 (1 : R) 0).trans
      ((PathZeroRing.emptyEquiv (PathOpenLayer.parameter.{0,0} R)
        (algebraMap R (PathOpenLayer.Laurent.{0,0} R) 0)).restrictScalars R))

theorem equation_ne_zero [Nontrivial R] : equation R ≠ 0 := by
  intro h
  have hc := congrArg (constantCoeff : Plane R →+* R) h
  simp [equation] at hc

theorem equation_regular [IsDomain R] : IsSMulRegular (Plane R) (equation R) := by
  intro a b h
  exact mul_left_cancel₀ (equation_ne_zero R) h

def normalBasis [IsDomain R] : Basis PUnit (Closed R) (Ideal.span {equation R}).Cotangent :=
  PrincipalConormal.basis (equation R) (equation_regular R)

theorem normalBasis_equation [IsDomain R] (i : PUnit) : normalBasis R i =
    (Ideal.span {equation R}).toCotangent ⟨equation R, Ideal.subset_span (Set.mem_singleton _)⟩ :=
  PrincipalConormal.basis_apply _ _ i

#print axioms Plane
#print axioms equation
#print axioms Closed
#print axioms relation_eq
#print axioms ideal_eq
#print axioms closedPathEquiv
#print axioms path_coordinate_unit
#print axioms pathOpenEquiv
#print axioms closedEquiv
#print axioms equation_ne_zero
#print axioms equation_regular
#print axioms normalBasis
#print axioms normalBasis_equation
end Verification.HyperbolaGeometry
