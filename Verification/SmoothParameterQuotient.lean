/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.RingTheory.Smooth.Basic

/-!
# Smooth Parameter Quotient

Killing any chosen polynomial parameters in a smooth parameter
algebra leaves a smooth algebra over the original base. The formal lift
sets killed parameters to zero and lifts each remaining parameter.
-/
noncomputable section
universe u
namespace Verification.SmoothParameterQuotient
open MvPolynomial
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
variable [Algebra (MvPolynomial ι R) A] [IsScalarTower R (MvPolynomial ι R) A]
variable (s : Set ι)

def ideal : Ideal A := Ideal.span (Set.range
  (fun i : s => algebraMap (MvPolynomial ι R) A (X i.val)))

theorem formallySmooth [Algebra.FormallySmooth (MvPolynomial ι R) A] :
    Algebra.FormallySmooth R (A ⧸ ideal R A ι s) := by
  classical
  constructor
  intro C _ _ J hJ g
  let q := Ideal.Quotient.mkₐ R (ideal R A ι s)
  choose w hw using fun i : ι => Ideal.Quotient.mk_surjective
    (g (q (algebraMap (MvPolynomial ι R) A (X i))))
  let t : MvPolynomial ι R →ₐ[R] C := aeval (fun i => if i ∈ s then 0 else w i)
  have ht : ∀ i, Ideal.Quotient.mk J (t (X i)) =
      g (q (algebraMap (MvPolynomial ι R) A (X i))) := by
    intro i
    rw [show t (X i) = if i ∈ s then 0 else w i from aeval_X _ _]
    by_cases hi : i ∈ s
    · rw [if_pos hi,map_zero]
      have hzero : q (algebraMap (MvPolynomial ι R) A (X i)) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range.mpr ⟨⟨i,hi⟩,rfl⟩))
      rw [hzero,map_zero]
    · rw [if_neg hi]
      exact hw i
  have hcomm : (g.comp q).comp (IsScalarTower.toAlgHom R (MvPolynomial ι R) A) =
      (Ideal.Quotient.mkₐ R J).comp t := by
    apply MvPolynomial.algHom_ext
    intro i
    exact (ht i).symm
  letI : Algebra (MvPolynomial ι R) C := t.toRingHom.toAlgebra
  letI : IsScalarTower R (MvPolynomial ι R) C := IsScalarTower.of_algHom t
  let h : A →ₐ[MvPolynomial ι R] C ⧸ J :=
    { (g.comp q).toRingHom with commutes' := fun p => AlgHom.congr_fun hcomm p }
  let f := Algebra.FormallySmooth.lift J ⟨2,hJ⟩ h
  have hfzero : ideal R A ι s ≤ RingHom.ker f.toRingHom := by
    apply Ideal.span_le.mpr
    rintro z ⟨i,rfl⟩
    change f (algebraMap (MvPolynomial ι R) A (X i.val)) = 0
    rw [AlgHom.commutes]
    change t (X i.val) = 0
    rw [show t (X i.val) = if i.val ∈ s then 0 else w i.val from aeval_X _ _]
    exact if_pos i.property
  let d : A ⧸ ideal R A ι s →ₐ[R] C :=
    Ideal.Quotient.liftₐ (ideal R A ι s) (f.restrictScalars R) hfzero
  refine ⟨d,?_⟩
  apply AlgHom.ext
  intro z
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective z
  exact Algebra.FormallySmooth.mk_lift J ⟨2,hJ⟩ h a

theorem smooth [Fintype ι] [Algebra.Smooth (MvPolynomial ι R) A] :
    Algebra.Smooth R (A ⧸ ideal R A ι s) := by
  letI : Algebra.FinitePresentation R A :=
    Algebra.FinitePresentation.trans R (MvPolynomial ι R) A
  letI : Algebra.FinitePresentation R (A ⧸ ideal R A ι s) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))
  exact ⟨formallySmooth R A ι s,inferInstance⟩

#print axioms ideal
#print axioms formallySmooth
#print axioms smooth
end Verification.SmoothParameterQuotient
