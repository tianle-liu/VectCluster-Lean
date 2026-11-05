/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalTransverseOpenInverse

/-!
# Local Transverse Open Equiv

Actual inverse identities and the open-layer affine-times-torus algebra
equivalence, including the original parameter and retained partner images.
-/
noncomputable section
universe u
namespace Verification.LocalTransverseOpenEquiv
open MvPolynomial Verification.LocalExchangeSmooth Verification.ExchangeTransverseSlice
open Verification.LocalTransverseOpen Verification.LocalTransverseOpenInverse
variable {S ι : Type u} [CommRing S] (χ : ι → Sˣ) (v : ι)

theorem toAffine_fromLaurent : (toAffine χ v).comp (fromLaurent χ v) =
    IsScalarTower.toAlgHom S (Laurent χ v) (Affine χ v) := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial (OldFiber χ v)))
  apply Polynomial.ringHom_ext
  · intro a
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective a
    change toAffine χ v (fromLaurent χ v
      (algebraMap (Polynomial (OldFiber χ v)) (Laurent χ v)
        (Polynomial.C (Ideal.Quotient.mk (fiberIdeal (fun i : Old v => χ i.1)) a)))) = _
    rw [fromLaurent_polynomial]
    change toAffine χ v (Polynomial.aevalTower (fiberCoefficient χ v) (sourceUnit χ v : Open χ v)
      (Polynomial.C (Ideal.Quotient.mk (fiberIdeal (fun i : Old v => χ i.1)) a))) = _
    rw [Polynomial.aevalTower_C]
    change toAffine χ v (algebraMap S (Open χ v) a) = algebraMap S (Affine χ v) a
    exact (toAffine χ v).commutes a
  · change toAffine χ v (fromLaurent χ v
      (algebraMap (Polynomial (OldFiber χ v)) (Laurent χ v) Polynomial.X)) = _
    rw [← targetUnit_val, fromLaurent_unit, sourceUnit_val, toAffine_include, toAffineRaw_x]
    classical
    simp only [targetX, eq_self_iff_true, if_true]
    rfl

theorem toAffine_fromAffine : (toAffine χ v).comp (fromAffine χ v) = AlgHom.id S (Affine χ v) := by
  apply AlgHom.coe_ringHom_injective
  apply MvPolynomial.ringHom_ext
  · intro a
    change toAffine χ v (fromAffine χ v (C a)) = C a
    rw [fromAffine_C]
    exact AlgHom.congr_fun (toAffine_fromLaurent χ v) a
  · intro i
    change toAffine χ v (fromAffine χ v (X i)) = X i
    rw [fromAffine_X, toAffine_include, toAffineRaw_y]
    classical
    simp only [targetY, dif_neg i.2]

def affineEquiv : Open χ v ≃ₐ[S] Affine χ v :=
  AlgEquiv.ofAlgHom (toAffine χ v) (fromAffine χ v)
    (toAffine_fromAffine χ v) (fromAffine_toAffine χ v)

theorem affineEquiv_parameter : affineEquiv χ v (includeOpen χ v (x χ v)) =
    C (algebraMap (Polynomial (OldFiber χ v)) (Laurent χ v) Polynomial.X) := by
  change toAffine χ v (includeOpen χ v (x χ v)) = _
  rw [toAffine_include, toAffineRaw_x]
  classical
  simp only [targetX, eq_self_iff_true, if_true, targetUnit_val]

theorem affineEquiv_partner (i : Old v) :
    affineEquiv χ v (includeOpen χ v (y χ i.1)) = X i := by
  change toAffine χ v (includeOpen χ v (y χ i.1)) = _
  rw [toAffine_include, toAffineRaw_y]
  classical
  simp only [targetY, dif_neg i.2]

#print axioms toAffine_fromLaurent
#print axioms toAffine_fromAffine
#print axioms affineEquiv
#print axioms affineEquiv_parameter
#print axioms affineEquiv_partner
end Verification.LocalTransverseOpenEquiv
