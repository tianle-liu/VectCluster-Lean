/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathFullComplex
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Path Coefficient Ring

The manuscript's unspecialized coefficient ring, with its actual universal
property and the full path chain complexes over that ring.
-/

namespace Verification.PathCoefficientRing

open Classical

noncomputable def relations : Ideal (MvPolynomial Bool ℤ) :=
  Ideal.span {MvPolynomial.X false*MvPolynomial.X false-1,
    (1+MvPolynomial.X false)*MvPolynomial.X true}

noncomputable abbrev Coeff := MvPolynomial Bool ℤ ⧸ relations

noncomputable def g : Coeff := Ideal.Quotient.mk relations (MvPolynomial.X false)
noncomputable def rho : Coeff := Ideal.Quotient.mk relations (MvPolynomial.X true)

theorem g_square : g*g=1 := by
  have hz : Ideal.Quotient.mk relations
      (MvPolynomial.X false*MvPolynomial.X false-1)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _))
  simpa only [map_sub,map_mul,map_one,sub_eq_zero] using hz

theorem rho_relation : (1+g)*rho=0 := by
  have hz : Ideal.Quotient.mk relations
      ((1+MvPolynomial.X false)*MvPolynomial.X true)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  simpa only [map_mul,map_add,map_one] using hz

/-- Every realization of the two formal relations factors through this literal ring. -/
noncomputable def realize {R : Type*} [CommRing R] (g' ρ' : R)
    (hg : g'*g'=1) (hρ : (1+g')*ρ'=0) : Coeff →+* R :=
  Ideal.Quotient.lift relations
    (MvPolynomial.eval₂Hom (Int.castRingHom R) (fun b : Bool => if b then ρ' else g')) (by
      change relations ≤ RingHom.ker _
      apply Ideal.span_le.mpr
      intro f hf
      rcases Set.mem_insert_iff.mp hf with rfl | hf
      · change (MvPolynomial.eval₂Hom (Int.castRingHom R)
          (fun b : Bool => if b then ρ' else g')) _=0
        simp [hg]
      · rw [Set.mem_singleton_iff] at hf
        subst f
        change (MvPolynomial.eval₂Hom (Int.castRingHom R)
          (fun b : Bool => if b then ρ' else g')) _=0
        simp [hρ])

theorem realize_g {R : Type*} [CommRing R] (g' ρ' : R)
    (hg : g'*g'=1) (hρ : (1+g')*ρ'=0) : realize g' ρ' hg hρ g=g' := by
  simp [realize,g]

theorem realize_rho {R : Type*} [CommRing R] (g' ρ' : R)
    (hg : g'*g'=1) (hρ : (1+g')*ρ'=0) : realize g' ρ' hg hρ rho=ρ' := by
  simp [realize,rho]

/-- No specialization of g or rho occurs in either original path model. -/
noncomputable def zChainComplex (n : ℕ) : CochainComplex (ModuleCat Coeff) ℤ :=
  Verification.PathFullComplex.zChainComplex g rho n g_square rho_relation

noncomputable def yChainComplex (a : ℕ) : CochainComplex (ModuleCat Coeff) ℤ :=
  Verification.PathFullComplex.yChainComplex g rho a g_square rho_relation

#print axioms relations
#print axioms Coeff
#print axioms g
#print axioms rho
#print axioms g_square
#print axioms rho_relation
#print axioms realize
#print axioms realize_g
#print axioms realize_rho
#print axioms zChainComplex
#print axioms yChainComplex

end Verification.PathCoefficientRing
