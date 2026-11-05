/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathCoefficientGrading

/-!
# Path Coefficient Graded Realization

The formal Laurent coaction detects genuine homogeneous coefficients
after every graded realization. The proof uses polynomial representatives;
no compatibility of the realized coaction is assumed.
-/
noncomputable section
namespace Verification.PathCoefficientGradedRealization
open Verification.PathCoefficientRing Verification.PathCoefficientGrading
open LaurentPolynomial

variable {A : Type*} [Ring A] (f : Coeff →+* A) (H : ℤ → A → Prop)
variable (hz : ∀ k,H k 0) (hc : ∀ z : ℤ,H 0 (z : A))
variable (ha : ∀ k a b,H k a → H k b → H k (a+b))
variable (hg : ∀ k a,H k a → H k (a*f g))
variable (hr : ∀ k a,H k a → H (k+1) (a*f rho))

include hz hc ha hg hr
theorem coefficient (c : Coeff) (k : ℤ) : H k (f (scale c k)) := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective c
  induction p using MvPolynomial.induction_on generalizing k with
  | C z =>
    have he : Ideal.Quotient.mk relations (MvPolynomial.C z)=(z : Coeff) := by simp
    rw [he,map_intCast]
    change H k (f ((C (z : Coeff)) k))
    rw [C_apply]
    split_ifs with hk
    · subst k
      simpa using hc z
    · simpa using hz k
  | add p q hp hq =>
    rw [map_add,map_add]
    change H k (f (scale (Ideal.Quotient.mk relations p) k+scale (Ideal.Quotient.mk relations q) k))
    rw [map_add]
    exact ha k _ _ (hp k) (hq k)
  | mul_X p b hp =>
    rw [map_mul,map_mul]
    cases b
    · change H k (f ((scale (Ideal.Quotient.mk relations p)*scale g) k))
      rw [scale_g,← single_eq_C,AddMonoidAlgebra.mul_single_apply,sub_zero,map_mul]
      exact hg k _ (hp k)
    · change H k (f ((scale (Ideal.Quotient.mk relations p)*scale rho) k))
      rw [scale_rho,← single_eq_C_mul_T,AddMonoidAlgebra.mul_single_apply,map_mul]
      simpa only [sub_add_cancel] using hr (k-1) _ (hp (k-1))

theorem homogeneous {c : Coeff} {k : ℤ} (h : Homogeneous k c) : H k (f c) := by
  have he : scale c k=c := by
    rw [h,← single_eq_C_mul_T,Finsupp.single_eq_same]
  rw [← he]
  exact coefficient f H hz hc ha hg hr c k

#print axioms coefficient
#print axioms homogeneous
end Verification.PathCoefficientGradedRealization
