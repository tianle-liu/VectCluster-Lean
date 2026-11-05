/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ExchangeZeroFiber
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Local Transverse Open

The open side of the literal exchange slice: all old x-coordinates are
zero and the one new x-coordinate is inverted. Its target presentation has
the old mutated partners free over the actual old character fiber times Gm.
-/
noncomputable section
universe u
namespace Verification.LocalTransverseOpen
open MvPolynomial Verification.LocalExchangeSmooth Verification.ExchangeTransverseSlice
variable {S ι : Type u} [CommRing S] (χ : ι → Sˣ) (v : ι)

abbrev Old := {i : ι // i ≠ v}
abbrev OldFiber := Fiber (fun i : Old v => χ i.1)
abbrev Laurent := Localization.Away (Polynomial.X : Polynomial (OldFiber χ v))
abbrev Affine := MvPolynomial (Old v) (Laurent χ v)

def partialIdeal : Ideal (LocalAlgebra χ) :=
  Ideal.span (Set.range (fun i : Old v => x χ i.1))
abbrev Partial := LocalAlgebra χ ⧸ partialIdeal χ v
def parameter : Partial χ v := Ideal.Quotient.mk (partialIdeal χ v) (x χ v)
abbrev Open := Localization.Away (parameter χ v)

def quotient : LocalAlgebra χ →ₐ[S] Partial χ v := Ideal.Quotient.mkₐ S (partialIdeal χ v)
def includeOpen : LocalAlgebra χ →ₐ[S] Open χ v :=
  (IsScalarTower.toAlgHom S (Partial χ v) (Open χ v)).comp (quotient χ v)

theorem quotient_old (i : Old v) : quotient χ v (x χ i.1) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))

theorem open_old (i : Old v) : includeOpen χ v (x χ i.1) = 0 := by
  change algebraMap (Partial χ v) (Open χ v) (quotient χ v (x χ i.1)) = 0
  rw [quotient_old, map_zero]

def targetUnit : (Laurent χ v)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (Polynomial.X : Polynomial (OldFiber χ v))).unit

theorem targetUnit_val : (targetUnit χ v : Laurent χ v) =
    algebraMap (Polynomial (OldFiber χ v)) (Laurent χ v) Polynomial.X :=
  (IsLocalization.Away.algebraMap_isUnit _).unit_spec

def targetX (i : ι) : Affine χ v := by
  classical
  exact if i = v then C (targetUnit χ v : Laurent χ v) else 0

def targetY (i : ι) : Affine χ v := by
  classical
  exact if h : i = v then C (↑(targetUnit χ v)⁻¹ *
    (1 + algebraMap S (Laurent χ v) (χ i : S))) else X ⟨i,h⟩

theorem old_relation (i : Old v) : algebraMap S (Affine χ v) (1 + (χ i.1 : S)) = 0 := by
  have h : Ideal.Quotient.mk (fiberIdeal (fun i : Old v => χ i.1)) (1 + (χ i.1 : S)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
  change algebraMap (OldFiber χ v) (Affine χ v)
    (Ideal.Quotient.mk (fiberIdeal (fun i : Old v => χ i.1)) (1 + (χ i.1 : S))) = 0
  rw [h, map_zero]

theorem target_equation (i : ι) :
    targetX χ v i * targetY χ v i - 1 = algebraMap S (Affine χ v) (χ i : S) := by
  classical
  by_cases hi : i = v
  · subst i
    simp only [targetX, targetY, eq_self_iff_true, if_true, dite_true, ← map_mul]
    rw [← mul_assoc, Units.mul_inv, one_mul, map_add, map_one]
    change 1 + algebraMap S (Affine χ v) (χ v : S) - 1 = _
    exact add_sub_cancel_left _ _
  · simp only [targetX, targetY, if_neg hi, dif_neg hi, zero_mul, zero_sub]
    have h := old_relation χ v ⟨i,hi⟩
    rw [map_add, map_one] at h
    exact (eq_neg_of_add_eq_zero_right h).symm

def toAffineRaw : LocalAlgebra χ →ₐ[S] Affine χ v :=
  lift χ (Algebra.ofId S (Affine χ v)) (targetX χ v) (targetY χ v) (target_equation χ v)

theorem toAffineRaw_x (i : ι) : toAffineRaw χ v (x χ i) = targetX χ v i := lift_x _ _ _ _ _ _
theorem toAffineRaw_y (i : ι) : toAffineRaw χ v (y χ i) = targetY χ v i := lift_y _ _ _ _ _ _

def toAffinePartial : Partial χ v →ₐ[S] Affine χ v :=
  Ideal.Quotient.liftₐ (partialIdeal χ v) (toAffineRaw χ v) (by
    change partialIdeal χ v ≤ RingHom.ker (toAffineRaw χ v).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change toAffineRaw χ v (x χ i.1) = 0
    rw [toAffineRaw_x]
    classical
    simp [targetX,i.2])

theorem toAffinePartial_parameter : toAffinePartial χ v (parameter χ v) =
    C (targetUnit χ v : Laurent χ v) := by
  change toAffineRaw χ v (x χ v) = _
  rw [toAffineRaw_x]
  classical
  simp [targetX]

theorem parameter_image_unit (m : Submonoid.powers (parameter χ v)) :
    IsUnit (toAffinePartial χ v m) := by
  obtain ⟨n,hn⟩ := m.2
  rw [← hn, map_pow, toAffinePartial_parameter]
  exact ((targetUnit χ v).isUnit.map C).pow n

def toAffine : Open χ v →ₐ[S] Affine χ v :=
  IsLocalization.liftAlgHom (parameter_image_unit χ v)

theorem toAffine_include (z : LocalAlgebra χ) :
    toAffine χ v (includeOpen χ v z) = toAffineRaw χ v z := IsLocalization.lift_eq _ _

#print axioms Old
#print axioms OldFiber
#print axioms Laurent
#print axioms Affine
#print axioms partialIdeal
#print axioms Partial
#print axioms parameter
#print axioms Open
#print axioms quotient
#print axioms includeOpen
#print axioms quotient_old
#print axioms open_old
#print axioms targetUnit
#print axioms targetUnit_val
#print axioms targetX
#print axioms targetY
#print axioms old_relation
#print axioms target_equation
#print axioms toAffineRaw
#print axioms toAffineRaw_x
#print axioms toAffineRaw_y
#print axioms toAffinePartial
#print axioms toAffinePartial_parameter
#print axioms parameter_image_unit
#print axioms toAffine
#print axioms toAffine_include
end Verification.LocalTransverseOpen
