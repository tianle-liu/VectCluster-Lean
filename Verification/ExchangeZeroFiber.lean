/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ExchangeTransverseSlice

/-!
# Exchange Zero Fiber

The actual zero-coordinate closed layer of the local exchange quotient
is affine space in the retained mutated partners over the character fiber.
The maps and their coordinate formulas are constructed explicitly.
-/
noncomputable section
universe u
namespace Verification.ExchangeZeroFiber
open MvPolynomial Verification.LocalExchangeSmooth Verification.ExchangeTransverseSlice
variable {R S ι : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (χ : ι → Sˣ)

def zeroIdeal : Ideal (LocalAlgebra χ) := Ideal.span (Set.range (x χ))
abbrev Closed := LocalAlgebra χ ⧸ zeroIdeal χ
abbrev Affine := MvPolynomial ι (Fiber χ)


def quotient : LocalAlgebra χ →ₐ[R] Closed χ := Ideal.Quotient.mkₐ R (zeroIdeal χ)
def coefficient : S →ₐ[R] Closed χ :=
  (quotient (R := R) χ).comp (IsScalarTower.toAlgHom R S (LocalAlgebra χ))

theorem quotient_x (i : ι) : quotient (R := R) χ (x χ i) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))

theorem coefficient_relation (i : ι) : coefficient (R := R) χ (1 + (χ i : S)) = 0 := by
  have he := congrArg (quotient (R := R) χ) (equation χ i)
  rw [map_sub,map_mul,map_one,quotient_x,zero_mul,zero_sub] at he
  change (quotient (R := R) χ).toRingHom ((algebraMap S (LocalAlgebra χ)) (1 + (χ i : S))) = 0
  rw [map_add,map_one,map_add,map_one]
  change 1 + quotient (R := R) χ (algebraMap S (LocalAlgebra χ) (χ i : S)) = 0
  rw [← he]
  ring

def fiberCoefficient : Fiber χ →ₐ[R] Closed χ :=
  Ideal.Quotient.liftₐ (fiberIdeal χ) (coefficient (R := R) χ) (by
    change fiberIdeal χ ≤ RingHom.ker (coefficient (R := R) χ).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact coefficient_relation (R := R) χ i)

def fromAffine : Affine χ →ₐ[R] Closed χ :=
  aevalTower (fiberCoefficient (R := R) χ) (fun i => quotient (R := R) χ (y χ i))

theorem fromAffine_X (i : ι) : fromAffine (R := R) χ (X i) = quotient (R := R) χ (y χ i) :=
  aevalTower_X _ _ _

theorem fromAffine_C (s : Fiber χ) : fromAffine (R := R) χ (C s) = fiberCoefficient (R := R) χ s :=
  aevalTower_C _ _ _

def targetCoefficient : S →ₐ[R] Affine χ :=
  (IsScalarTower.toAlgHom R (Fiber χ) (Affine χ)).comp (Ideal.Quotient.mkₐ R (fiberIdeal χ))

theorem targetCoefficient_relation (i : ι) :
    (-1 : Affine χ) = targetCoefficient (R := R) χ (χ i : S) := by
  have hh : Ideal.Quotient.mk (fiberIdeal χ) (1 + (χ i : S)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
  have hp := congrArg (C : Fiber χ →+* Affine χ) hh
  simp only [map_add,map_one,map_zero] at hp
  change -1 = C (Ideal.Quotient.mk (fiberIdeal χ) (χ i : S))
  linear_combination -hp

def toAffineRaw : LocalAlgebra χ →ₐ[R] Affine χ :=
  lift χ (targetCoefficient (R := R) χ) (fun _ => 0) X
    (fun i => by rw [zero_mul,zero_sub]; exact targetCoefficient_relation (R := R) χ i)

theorem toAffineRaw_x (i : ι) : toAffineRaw (R := R) χ (x χ i) = 0 := lift_x _ _ _ _ _ _
theorem toAffineRaw_y (i : ι) : toAffineRaw (R := R) χ (y χ i) = X i := lift_y _ _ _ _ _ _
theorem toAffineRaw_coefficient (s : S) :
    toAffineRaw (R := R) χ (algebraMap S (LocalAlgebra χ) s) = C (Ideal.Quotient.mk (fiberIdeal χ) s) :=
  lift_coefficient _ _ _ _ _ _

def toAffine : Closed χ →ₐ[R] Affine χ :=
  Ideal.Quotient.liftₐ (zeroIdeal χ) (toAffineRaw (R := R) χ) (by
    change zeroIdeal χ ≤ RingHom.ker (toAffineRaw (R := R) χ).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact toAffineRaw_x (R := R) χ i)

theorem toAffine_quotient (z : LocalAlgebra χ) :
    toAffine (R := R) χ (quotient (R := R) χ z) = toAffineRaw (R := R) χ z := rfl

theorem toAffine_fromAffine : (toAffine (R := R) χ).comp (fromAffine (R := R) χ) = AlgHom.id R (Affine χ) := by
  apply AlgHom.coe_ringHom_injective
  apply MvPolynomial.ringHom_ext
  · intro s
    obtain ⟨s,rfl⟩ := Ideal.Quotient.mk_surjective s
    change toAffine (R := R) χ (fromAffine (R := R) χ (C (Ideal.Quotient.mk (fiberIdeal χ) s))) = _
    rw [fromAffine_C]
    change toAffine (R := R) χ (quotient (R := R) χ (algebraMap S (LocalAlgebra χ) s)) = _
    rw [toAffine_quotient,toAffineRaw_coefficient]
    rfl
  · intro i
    change toAffine (R := R) χ (fromAffine (R := R) χ (X i)) = X i
    rw [fromAffine_X,toAffine_quotient,toAffineRaw_y]

theorem fromAffine_toAffine : (fromAffine (R := R) χ).comp (toAffine (R := R) χ) = AlgHom.id R (Closed χ) := by
  apply Ideal.Quotient.algHom_ext
  apply LocalExchangeSmooth.hom_ext χ
  · intro s
    change fromAffine (R := R) χ (toAffine (R := R) χ (quotient (R := R) χ (algebraMap S (LocalAlgebra χ) s))) = _
    rw [toAffine_quotient,toAffineRaw_coefficient,fromAffine_C]
    rfl
  · intro i
    change fromAffine (R := R) χ (toAffine (R := R) χ (quotient (R := R) χ (x χ i))) = quotient (R := R) χ (x χ i)
    rw [quotient_x,map_zero,map_zero]
  · intro i
    change fromAffine (R := R) χ (toAffine (R := R) χ (quotient (R := R) χ (y χ i))) = quotient (R := R) χ (y χ i)
    rw [toAffine_quotient,toAffineRaw_y,fromAffine_X]

def affineEquiv : Closed χ ≃ₐ[R] Affine χ :=
  AlgEquiv.ofAlgHom (toAffine (R := R) χ) (fromAffine (R := R) χ)
    (toAffine_fromAffine (R := R) χ) (fromAffine_toAffine (R := R) χ)

theorem affineEquiv_partner (i : ι) :
    affineEquiv (R := R) χ (quotient (R := R) χ (y χ i)) = X i := toAffineRaw_y (R := R) χ i

#print axioms zeroIdeal
#print axioms Closed
#print axioms Affine
#print axioms quotient
#print axioms coefficient
#print axioms quotient_x
#print axioms coefficient_relation
#print axioms fiberCoefficient
#print axioms fromAffine
#print axioms fromAffine_X
#print axioms fromAffine_C
#print axioms targetCoefficient
#print axioms targetCoefficient_relation
#print axioms toAffineRaw
#print axioms toAffineRaw_x
#print axioms toAffineRaw_y
#print axioms toAffineRaw_coefficient
#print axioms toAffine
#print axioms toAffine_quotient
#print axioms toAffine_fromAffine
#print axioms fromAffine_toAffine
#print axioms affineEquiv
#print axioms affineEquiv_partner
end Verification.ExchangeZeroFiber
