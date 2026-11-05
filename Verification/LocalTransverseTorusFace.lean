/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalTransverseOpenEquiv

/-!
# Local Transverse Torus Face

The actual Laurent face map between the old and new character fibers.
It fixes the punctured-line parameter and specializes the additional
character to -1. Its composition with evaluation of every affine partner
at zero is exactly the original transverse morphism on the open layer.
-/
noncomputable section
universe u
namespace Verification.LocalTransverseTorusFace
open MvPolynomial Verification.LocalExchangeSmooth Verification.ExchangeTransverseSlice
open Verification.LocalTransverseOpen
variable {S ι : Type u} [CommRing S] (χ : ι → Sˣ) (v : ι)

abbrev NewLaurent := Localization.Away (Polynomial.X : Slice χ)

def fiberRestriction : OldFiber χ v →ₐ[S] Fiber χ :=
  Ideal.Quotient.liftₐ (fiberIdeal (fun i : Old v => χ i.1)) (Ideal.Quotient.mkₐ S (fiberIdeal χ)) (by
    change fiberIdeal (fun i : Old v => χ i.1) ≤ RingHom.ker (Ideal.Quotient.mk (fiberIdeal χ))
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i.1)))

def polynomialRestriction : Polynomial (OldFiber χ v) →ₐ[S] NewLaurent χ :=
  Polynomial.aevalTower
    ((IsScalarTower.toAlgHom S (Fiber χ) (NewLaurent χ)).comp (fiberRestriction χ v))
    (algebraMap (Slice χ) (NewLaurent χ) Polynomial.X)

theorem polynomial_units (m : Submonoid.powers (Polynomial.X : Polynomial (OldFiber χ v))) :
    IsUnit (polynomialRestriction χ v m) := by
  obtain ⟨n,hn⟩ := m.2
  rw [← hn,map_pow]
  change IsUnit ((Polynomial.aevalTower _ _ Polynomial.X) ^ n)
  rw [Polynomial.aevalTower_X]
  exact (IsLocalization.Away.algebraMap_isUnit (Polynomial.X : Slice χ)).pow n

def torusFace : Laurent χ v →ₐ[S] NewLaurent χ :=
  IsLocalization.liftAlgHom (polynomial_units χ v)

theorem torusFace_polynomial (p : Polynomial (OldFiber χ v)) :
    torusFace χ v (algebraMap (Polynomial (OldFiber χ v)) (Laurent χ v) p) =
      polynomialRestriction χ v p := IsLocalization.lift_eq _ _

theorem torusFace_parameter : torusFace χ v (targetUnit χ v : Laurent χ v) =
    algebraMap (Slice χ) (NewLaurent χ) Polynomial.X := by
  rw [targetUnit_val,torusFace_polynomial]
  exact Polynomial.aevalTower_X _ _

def affineFace : Affine χ v →ₐ[S] NewLaurent χ := aevalTower (torusFace χ v) (fun _ => 0)

theorem affineFace_C (a : Laurent χ v) : affineFace χ v (C a) = torusFace χ v a := aevalTower_C _ _ _
theorem affineFace_X (i : Old v) : affineFace χ v (X i) = 0 := aevalTower_X _ _ _

theorem new_relation (i : ι) : 1 + algebraMap S (NewLaurent χ) (χ i : S) = 0 := by
  have he : Ideal.Quotient.mk (fiberIdeal χ) (1 + (χ i : S)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
  have hh := congrArg (algebraMap (Fiber χ) (NewLaurent χ)) he
  simpa only [map_add,map_one,map_zero] using hh

theorem affineFace_targetX (i : ι) : affineFace χ v (targetX χ v i) =
    algebraMap (Slice χ) (NewLaurent χ) (coordinate χ v i) := by
  classical
  by_cases hi : i = v
  · subst i
    simp only [targetX,coordinate,eq_self_iff_true,if_true]
    rw [affineFace_C,torusFace_parameter]
  · simp only [targetX,coordinate,if_neg hi,map_zero]

theorem affineFace_targetY (i : ι) : affineFace χ v (targetY χ v i) = 0 := by
  classical
  by_cases hi : i = v
  · subst i
    simp only [targetY,eq_self_iff_true,dite_true]
    rw [affineFace_C,map_mul,map_add,map_one,AlgHom.commutes,new_relation,mul_zero]
  · simp only [targetY,dif_neg hi]
    exact affineFace_X χ v ⟨i,hi⟩

theorem raw_square : (affineFace χ v).comp (toAffineRaw χ v) =
    (IsScalarTower.toAlgHom S (Slice χ) (NewLaurent χ)).comp (sliceMap (R := S) χ v) := by
  apply LocalExchangeSmooth.hom_ext χ
  · intro s
    simp only [AlgHom.commutes]
  · intro i
    change affineFace χ v (toAffineRaw χ v (x χ i)) = algebraMap (Slice χ) (NewLaurent χ) (sliceMap (R := S) χ v (x χ i))
    rw [toAffineRaw_x,affineFace_targetX,slice_x]
  · intro i
    change affineFace χ v (toAffineRaw χ v (y χ i)) = algebraMap (Slice χ) (NewLaurent χ) (sliceMap (R := S) χ v (y χ i))
    rw [toAffineRaw_y,affineFace_targetY,slice_y,map_zero]

#print axioms NewLaurent
#print axioms fiberRestriction
#print axioms polynomialRestriction
#print axioms polynomial_units
#print axioms torusFace
#print axioms torusFace_polynomial
#print axioms torusFace_parameter
#print axioms affineFace
#print axioms affineFace_C
#print axioms affineFace_X
#print axioms new_relation
#print axioms affineFace_targetX
#print axioms affineFace_targetY
#print axioms raw_square
end Verification.LocalTransverseTorusFace
