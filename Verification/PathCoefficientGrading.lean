/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathCoefficientRing
import Mathlib.Algebra.Polynomial.Laurent

/-!
# Path Coefficient Grading

The literal formal path ring has the manuscript's coefficient grading.
The coaction sends g to g and rho to rho*T; a degree statement is an equality
of actual Laurent polynomials, not an assigned label on an arbitrary scalar.
-/

namespace Verification.PathCoefficientGrading

open Verification.PathCoefficientRing LaurentPolynomial

noncomputable def scale : Coeff →+* LaurentPolynomial Coeff :=
  realize (C g) (C rho*T 1)
    (by rw [← map_mul,g_square,map_one])
    (by rw [← mul_assoc,← map_one C,← map_add,← map_mul,rho_relation,map_zero,zero_mul])

theorem scale_g : scale g=C g := realize_g _ _ _ _
theorem scale_rho : scale rho=C rho*T 1 := realize_rho _ _ _ _

def Homogeneous (k : ℤ) (r : Coeff) : Prop := scale r=C r*T k

theorem homogeneous_zero (k : ℤ) : Homogeneous k 0 := by simp [Homogeneous]
theorem homogeneous_one : Homogeneous 0 1 := by simp [Homogeneous]
theorem homogeneous_g : Homogeneous 0 g := by simp [Homogeneous,scale_g]
theorem homogeneous_rho : Homogeneous 1 rho := scale_rho

theorem homogeneous_add {k : ℤ} {r s : Coeff} (hr : Homogeneous k r) (hs : Homogeneous k s) :
    Homogeneous k (r+s) := by
  change scale (r+s)=C (r+s)*T k
  rw [map_add,map_add,hr,hs,add_mul]

theorem homogeneous_neg {k : ℤ} {r : Coeff} (hr : Homogeneous k r) : Homogeneous k (-r) := by
  change scale (-r)=C (-r)*T k
  rw [map_neg,map_neg,hr,neg_mul]

theorem homogeneous_sub {k : ℤ} {r s : Coeff} (hr : Homogeneous k r) (hs : Homogeneous k s) :
    Homogeneous k (r-s) := by
  rw [sub_eq_add_neg]
  exact homogeneous_add hr (homogeneous_neg hs)

theorem homogeneous_mul {k l : ℤ} {r s : Coeff} (hr : Homogeneous k r) (hs : Homogeneous l s) :
    Homogeneous (k+l) (r*s) := by
  change scale (r*s)=C (r*s)*T (k+l)
  rw [map_mul,map_mul,hr,hs,T_add]
  ring

theorem homogeneous_sum {α : Type*} (s : Finset α) (k : ℤ) (f : α → Coeff)
    (h : ∀ a∈s,Homogeneous k (f a)) : Homogeneous k (∑ a∈s,f a) := by
  induction s using Finset.cons_induction with
  | empty => simpa only [Finset.sum_empty] using homogeneous_zero k
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    exact homogeneous_add (h a (Finset.mem_cons_self _ _))
      (ih (fun b hb => h b (Finset.mem_cons_of_mem hb)))

noncomputable def pure : Coeff →+* Coeff := realize g 0 g_square (by simp)
theorem pure_g : pure g=g := realize_g _ _ _ _
theorem pure_rho : pure rho=0 := realize_rho _ _ _ _

theorem hom_ext {S : Type*} [CommRing S] (f h : Coeff →+* S)
    (hg : f g=h g) (hr : f rho=h rho) : f=h := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro z
    simp
  · intro b
    cases b
    · exact hg
    · exact hr

theorem pure_homogeneous (r : Coeff) : Homogeneous 0 (pure r) := by
  have he : scale.comp pure=C.comp pure := by
    apply hom_ext
    · simp only [RingHom.comp_apply,pure_g,scale_g]
    · simp only [RingHom.comp_apply,pure_rho,map_zero]
  have h := DFunLike.congr_fun he r
  simpa only [Homogeneous,RingHom.comp_apply,T_zero,mul_one] using h

#print axioms scale
#print axioms scale_g
#print axioms scale_rho
#print axioms Homogeneous
#print axioms homogeneous_zero
#print axioms homogeneous_one
#print axioms homogeneous_g
#print axioms homogeneous_rho
#print axioms homogeneous_add
#print axioms homogeneous_neg
#print axioms homogeneous_sub
#print axioms homogeneous_mul
#print axioms homogeneous_sum
#print axioms pure
#print axioms pure_g
#print axioms pure_rho
#print axioms hom_ext
#print axioms pure_homogeneous

end Verification.PathCoefficientGrading
