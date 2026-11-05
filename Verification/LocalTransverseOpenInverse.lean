/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalTransverseOpen

/-!
# Local Transverse Open Inverse

The inverse presentation map for the actual open exchange slice. The
remaining character relations follow from the original exchange equations
after the old x-coordinates vanish.
-/
noncomputable section
universe u
namespace Verification.LocalTransverseOpenInverse
open MvPolynomial Verification.LocalExchangeSmooth Verification.ExchangeTransverseSlice
open Verification.LocalTransverseOpen
variable {S ι : Type u} [CommRing S] (χ : ι → Sˣ) (v : ι)

def sourceUnit : (Open χ v)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (parameter χ v)).unit

theorem sourceUnit_val : (sourceUnit χ v : Open χ v) = includeOpen χ v (x χ v) :=
  (IsLocalization.Away.algebraMap_isUnit _).unit_spec

theorem old_coefficient_relation (i : Old v) : algebraMap S (Open χ v) (1 + (χ i.1 : S)) = 0 := by
  have he := congrArg (includeOpen χ v) (equation χ i.1)
  rw [map_sub, map_mul, map_one, open_old, zero_mul, zero_sub, AlgHom.commutes] at he
  rw [map_add, map_one, ← he, add_neg_cancel]

def fiberCoefficient : OldFiber χ v →ₐ[S] Open χ v :=
  Ideal.Quotient.liftₐ (fiberIdeal (fun i : Old v => χ i.1)) (Algebra.ofId S (Open χ v)) (by
    change fiberIdeal (fun i : Old v => χ i.1) ≤ RingHom.ker (algebraMap S (Open χ v))
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact old_coefficient_relation χ v i)

def polynomialCoefficient : Polynomial (OldFiber χ v) →ₐ[S] Open χ v :=
  Polynomial.aevalTower (fiberCoefficient χ v) (sourceUnit χ v : Open χ v)

theorem polynomial_units (m : Submonoid.powers (Polynomial.X : Polynomial (OldFiber χ v))) :
    IsUnit (polynomialCoefficient χ v m) := by
  obtain ⟨n,hn⟩ := m.2
  rw [← hn, map_pow]
  change IsUnit ((Polynomial.aevalTower (fiberCoefficient χ v) (sourceUnit χ v : Open χ v) Polynomial.X) ^ n)
  rw [Polynomial.aevalTower_X]
  exact (sourceUnit χ v).isUnit.pow n

def fromLaurent : Laurent χ v →ₐ[S] Open χ v :=
  IsLocalization.liftAlgHom (polynomial_units χ v)

theorem fromLaurent_polynomial (p : Polynomial (OldFiber χ v)) :
    fromLaurent χ v (algebraMap (Polynomial (OldFiber χ v)) (Laurent χ v) p) =
      polynomialCoefficient χ v p := IsLocalization.lift_eq _ _

theorem fromLaurent_unit : fromLaurent χ v (targetUnit χ v : Laurent χ v) =
    (sourceUnit χ v : Open χ v) := by
  rw [targetUnit_val, fromLaurent_polynomial]
  exact Polynomial.aevalTower_X _ _

theorem fromLaurent_unit_inverse : fromLaurent χ v (↑(targetUnit χ v)⁻¹ : Laurent χ v) =
    (↑(sourceUnit χ v)⁻¹ : Open χ v) := by
  have hu : Units.map (fromLaurent χ v).toMonoidHom (targetUnit χ v) = sourceUnit χ v :=
    Units.ext (fromLaurent_unit χ v)
  change (Units.map (fromLaurent χ v).toMonoidHom ((targetUnit χ v)⁻¹) : Open χ v) = _
  rw [map_inv, hu]

def fromAffine : Affine χ v →ₐ[S] Open χ v :=
  aevalTower (fromLaurent χ v) (fun i : Old v => includeOpen χ v (y χ i.1))

theorem fromAffine_X (i : Old v) : fromAffine χ v (X i) = includeOpen χ v (y χ i.1) :=
  aevalTower_X _ _ _

theorem fromAffine_C (l : Laurent χ v) : fromAffine χ v (C l) = fromLaurent χ v l :=
  aevalTower_C _ _ _

theorem fromAffine_targetX (i : ι) : fromAffine χ v (targetX χ v i) = includeOpen χ v (x χ i) := by
  classical
  by_cases hi : i = v
  · subst i
    simp only [targetX, eq_self_iff_true, if_true]
    rw [fromAffine_C, fromLaurent_unit, sourceUnit_val]
  · simp only [targetX, if_neg hi, map_zero]
    exact (open_old χ v ⟨i,hi⟩).symm

theorem fromAffine_targetY (i : ι) : fromAffine χ v (targetY χ v i) = includeOpen χ v (y χ i) := by
  classical
  by_cases hi : i = v
  · subst i
    simp only [targetY, eq_self_iff_true, dite_true]
    rw [fromAffine_C, map_mul, fromLaurent_unit_inverse, map_add, map_one, AlgHom.commutes]
    have he := congrArg (includeOpen χ v) (equation χ v)
    rw [map_sub, map_mul, map_one, AlgHom.commutes] at he
    have he' : 1 + algebraMap S (Open χ v) (χ v : S) =
        (sourceUnit χ v : Open χ v) * includeOpen χ v (y χ v) := by
      rw [sourceUnit_val, ← he]
      ring
    rw [he', ← mul_assoc, Units.inv_mul, one_mul]
  · simp only [targetY, dif_neg hi]
    exact fromAffine_X χ v ⟨i,hi⟩

theorem fromAffine_toAffine : (fromAffine χ v).comp (toAffine χ v) = AlgHom.id S (Open χ v) := by
  have hh : ((fromAffine χ v).comp (toAffine χ v)).comp (includeOpen χ v) = includeOpen χ v := by
    apply LocalExchangeSmooth.hom_ext χ
    · intro s
      simp only [AlgHom.comp_apply, AlgHom.commutes]
    · intro i
      change fromAffine χ v (toAffine χ v (includeOpen χ v (x χ i))) = includeOpen χ v (x χ i)
      rw [toAffine_include, toAffineRaw_x, fromAffine_targetX]
    · intro i
      change fromAffine χ v (toAffine χ v (includeOpen χ v (y χ i))) = includeOpen χ v (y χ i)
      rw [toAffine_include, toAffineRaw_y, fromAffine_targetY]
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (parameter χ v))
  apply Ideal.Quotient.ringHom_ext
  exact congrArg AlgHom.toRingHom hh

#print axioms sourceUnit
#print axioms sourceUnit_val
#print axioms old_coefficient_relation
#print axioms fiberCoefficient
#print axioms polynomialCoefficient
#print axioms polynomial_units
#print axioms fromLaurent
#print axioms fromLaurent_polynomial
#print axioms fromLaurent_unit
#print axioms fromLaurent_unit_inverse
#print axioms fromAffine
#print axioms fromAffine_X
#print axioms fromAffine_C
#print axioms fromAffine_targetX
#print axioms fromAffine_targetY
#print axioms fromAffine_toAffine
end Verification.LocalTransverseOpenInverse
