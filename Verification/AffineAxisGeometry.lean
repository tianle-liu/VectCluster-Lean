/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SingleLaurent
import Mathlib.RingTheory.Localization.Integral

/-!
# Affine Axis Geometry

The zero section of the affine line and its genuine Laurent complement,
over an arbitrary coefficient algebra.
-/
noncomputable section
namespace Verification.AffineAxisGeometry
open MvPolynomial
variable (R : Type) [CommRing R]
attribute [local instance] MvPolynomial.algebraMvPolynomial

abbrev Line := MvPolynomial (PUnit : Type) R
def coordinate : Line R := X PUnit.unit
abbrev Closed := Line R ⧸ Ideal.span {coordinate R}

def closedEvaluation : Closed R →ₐ[R] R :=
  Ideal.Quotient.liftₐ (Ideal.span {coordinate R}) (aeval (fun _ : PUnit => (0 : R))) (by
    change Ideal.span {coordinate R} ≤ RingHom.ker (aeval (fun _ : PUnit => (0 : R))).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨rfl⟩
    change aeval (fun _ : PUnit => (0 : R)) (X PUnit.unit) = 0
    exact aeval_X _ _)

theorem closed_coordinate : Ideal.Quotient.mk (Ideal.span {coordinate R}) (coordinate R) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

def closedEquiv : Closed R ≃ₐ[R] R :=
  AlgEquiv.ofAlgHom (closedEvaluation R) (Algebra.ofId R (Closed R))
    (Subsingleton.elim _ _) (by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro i
      cases i
      change algebraMap R (Closed R) (aeval (fun _ : PUnit => (0 : R)) (X PUnit.unit)) =
        Ideal.Quotient.mk (Ideal.span {coordinate R}) (coordinate R)
      rw [aeval_X, map_zero, closed_coordinate])

theorem variableMonoid_eq : SplitExchangeChart.variableMonoid R (PUnit : Type) =
    Submonoid.powers (coordinate R) := by
  rw [SplitExchangeChart.variableMonoid, Submonoid.powers_eq_closure]
  congr 1
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    cases i
    exact Set.mem_singleton _
  · rintro ⟨rfl⟩
    exact ⟨PUnit.unit, rfl⟩

def openEquiv : SingleLaurent.Laurent.{0,0} R ≃ₐ[R] Localization.Away (coordinate R) := by
  letI : IsLocalization (SplitExchangeChart.variableMonoid R (PUnit : Type))
      (Localization.Away (coordinate R)) := by
    rw [variableMonoid_eq R]
    infer_instance
  exact (IsLocalization.algEquiv (SplitExchangeChart.variableMonoid R (PUnit : Type))
    (SingleLaurent.Laurent.{0,0} R) (Localization.Away (coordinate R))).restrictScalars R

theorem coordinate_regular [IsDomain R] : IsSMulRegular (Line R) (coordinate R) := by
  intro a b h
  exact mul_left_cancel₀ (MvPolynomial.X_ne_zero PUnit.unit) h

theorem laurent_smooth : Algebra.Smooth R (SingleLaurent.Laurent.{0,0} R) := by
  letI : Algebra.Smooth R (Line R) := {}
  letI : Algebra.Smooth (Line R) (Localization.Away (coordinate R)) :=
    Algebra.Smooth.of_isLocalization_Away (coordinate R)
  letI : Algebra.Smooth R (Localization.Away (coordinate R)) :=
    Algebra.Smooth.comp R (Line R) _
  exact Algebra.Smooth.of_equiv (openEquiv R).symm

#print axioms Line
#print axioms coordinate
#print axioms Closed
#print axioms closedEvaluation
#print axioms closed_coordinate
#print axioms closedEquiv
#print axioms variableMonoid_eq
#print axioms openEquiv
#print axioms coordinate_regular
#print axioms laurent_smooth
end Verification.AffineAxisGeometry
