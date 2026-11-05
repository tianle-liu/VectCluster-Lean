/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PerturbedHomologyModel
import Verification.IntegralSplitting
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Graded Homology TF

Degreewise torsion-freeness of the actual categorical homology of a finite
matrix complex implies torsion-freeness of its literal total ker/im quotient.
The proof uses the finite sum of actual homogeneous projections and constructs
a boundary preimage separately in each degree.
-/

namespace Verification.GradedHomologyTF

open CategoryTheory Verification.GradedPerturbation
open Verification.PerturbedHomologyModel

variable {R : Type*} [CommRing R]

/-- A literal quotient is torsion-free exactly when its defining submodule is saturated. -/
theorem quotient_tf_iff {M : Type*} [AddCommGroup M] [Module R M] (N : Submodule R M) :
    NoZeroSMulDivisors R (M ⧸ N) ↔
      ∀ (a : R), a ≠ 0 → ∀ (x : M), a • x ∈ N → x ∈ N := by
  constructor
  · intro h a ha x hx
    letI := h
    have hz : a • N.mkQ x=0 := by
      rw [← map_smul]
      exact (Submodule.Quotient.mk_eq_zero N).mpr hx
    exact (Submodule.Quotient.mk_eq_zero N).mp
      ((eq_zero_or_eq_zero_of_smul_eq_zero hz).resolve_left ha)
  · intro h
    constructor
    intro a q hq
    by_cases ha : a=0
    · exact Or.inl ha
    right
    induction q using Submodule.Quotient.induction_on N with
    | _ x =>
      apply (Submodule.Quotient.mk_eq_zero N).mpr
      apply h a ha x
      apply (Submodule.Quotient.mk_eq_zero N).mp
      simpa only [map_smul] using hq

/-- TF categorical homology detects actual boundaries among cycles. -/
theorem shortComplex_boundary (S : ShortComplex (ModuleCat R))
    [NoZeroSMulDivisors R S.homology] (a : R) (ha : a ≠ 0)
    (x : S.X₂) (hx : S.g x=0) (hax : ∃ y : S.X₁, S.f y=a • x) :
    ∃ y : S.X₁, S.f y=x := by
  let e := S.moduleCatHomologyIso.symm.toLinearEquiv
  letI : NoZeroSMulDivisors R S.moduleCatHomology :=
    Function.Injective.noZeroSMulDivisors e e.injective e.map_zero e.map_smul
  let z : LinearMap.ker S.g.hom := ⟨x,hx⟩
  have haz : a • z ∈ LinearMap.range S.moduleCatToCycles := by
    obtain ⟨y,hy⟩ := hax
    exact ⟨y,Subtype.ext hy⟩
  have hz := (quotient_tf_iff (LinearMap.range S.moduleCatToCycles)).mp inferInstance a ha z haz
  obtain ⟨y,hy⟩ := hz
  exact ⟨y,congrArg Subtype.val hy⟩

/-- Saturation of actual boundaries constructs TF for categorical homology. -/
theorem shortComplex_tf_of_boundaries (S : ShortComplex (ModuleCat R))
    (hsat : ∀ (a : R), a ≠ 0 → ∀ (x : S.X₂), S.g x=0 →
      (∃ y : S.X₁, S.f y=a • x) → ∃ y : S.X₁, S.f y=x) :
    NoZeroSMulDivisors R S.homology := by
  have ht : NoZeroSMulDivisors R S.moduleCatHomology := by
    apply (quotient_tf_iff (LinearMap.range S.moduleCatToCycles)).mpr
    intro a ha x hx
    obtain ⟨y,hy⟩ := hx
    obtain ⟨z,hz⟩ := hsat a ha x.val x.property ⟨y,congrArg Subtype.val hy⟩
    exact ⟨z,Subtype.ext hz⟩
  letI := ht
  let e := S.moduleCatHomologyIso.toLinearEquiv
  exact Function.Injective.noZeroSMulDivisors e e.injective e.map_zero e.map_smul

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Projection onto a single degree of the finite coordinate module. -/
def degreePart (deg : ι → ℤ) (p : ℤ) : Module.End R (ι → R) where
  toFun x i := if deg i=p then x i else 0
  map_add' x y := by funext i; dsimp; split_ifs <;> simp
  map_smul' a x := by funext i; dsimp; split_ifs <;> simp

omit [Fintype ι] [DecidableEq ι] in
/-- Its values really belong to the stated homogeneous component. -/
theorem degreePart_mem (deg : ι → ℤ) (p : ℤ) (x : ι → R) :
    degreePart deg p x ∈ degreeModule deg p := by
  intro i hi
  simp [degreePart, hi]

omit [Fintype ι] [DecidableEq ι] in
/-- Projection fixes every vector already supported in its degree. -/
theorem degreePart_fixed (deg : ι → ℤ) (p : ℤ) (x : degreeModule (R := R) deg p) :
    degreePart deg p x.val=x.val := by
  funext i
  by_cases hi : deg i=p
  · simp [degreePart, hi]
  · simp [degreePart, hi, x.property i hi]

/-- A degree-one differential shifts literal homogeneous projections by one. -/
theorem degreePart_differential (deg : ι → ℤ) (D : Matrix ι ι R)
    (hD : Homogeneous deg 1 D) (p : ℤ) (x : ι → R) :
    Matrix.toLin' D (degreePart deg p x)=degreePart deg (p+1) (Matrix.toLin' D x) := by
  funext i
  change (∑ j, D i j*(if deg j=p then x j else 0)) =
    if deg i=p+1 then ∑ j, D i j*x j else 0
  by_cases hi : deg i=p+1
  · rw [if_pos hi]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : deg j=p
    · rw [if_pos hj]
    · rw [if_neg hj, mul_zero, hD i j (by omega), zero_mul]
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : deg j=p
    · rw [if_pos hj, hD i j (by omega), zero_mul]
    · rw [if_neg hj, mul_zero]

omit [DecidableEq ι] in
/-- Every vector is the finite sum of its actual degree components. -/
theorem sum_degreePart (deg : ι → ℤ) (x : ι → R) :
    ∑ p ∈ Finset.univ.image deg, degreePart deg p x = x := by
  classical
  funext i
  simp [Finset.sum_apply, degreePart]

/-- A torsion multiple of a total cycle gives a genuine boundary in each degree. -/
theorem degree_boundary (deg : ι → ℤ) (D : Matrix ι ι R)
    (hD : Homogeneous deg 1 D) (hsq : D*D=0)
    (htf : ∀ p, NoZeroSMulDivisors R ((matrixComplex deg D hD hsq).homology p))
    (a : R) (ha : a ≠ 0) (x : ι → R) (hx : Matrix.toLin' D x=0)
    (hax : ∃ y : ι → R, Matrix.toLin' D y=a • x) (p : ℤ) :
    ∃ z : ι → R, Matrix.toLin' D z=degreePart deg p x := by
  let K := matrixComplex deg D hD hsq
  let S := K.sc' (p-1) p (p+1)
  letI := htf p
  let e := (K.homologyIsoSc' (p-1) p (p+1) (by simp) (by simp)).symm.toLinearEquiv
  letI : NoZeroSMulDivisors R S.homology :=
    Function.Injective.noZeroSMulDivisors e e.injective e.map_zero e.map_smul
  let xp : S.X₂ := ⟨degreePart deg p x, degreePart_mem deg p x⟩
  have hxp : S.g xp=0 := by
    change (K.d p (p+1)) xp=0
    rw [matrixComplex_d deg D hD hsq p (p+1) rfl]
    apply Subtype.ext
    change Matrix.toLin' D (degreePart deg p x)=0
    rw [degreePart_differential deg D hD, hx, map_zero]
  have haxp : ∃ y : S.X₁, S.f y=a • xp := by
    obtain ⟨y,hy⟩ := hax
    refine ⟨⟨degreePart deg (p-1) y, degreePart_mem deg (p-1) y⟩, ?_⟩
    change (K.d (p-1) p) _=a • xp
    rw [matrixComplex_d deg D hD hsq (p-1) p (by omega)]
    apply Subtype.ext
    change Matrix.toLin' D (degreePart deg (p-1) y)=a • degreePart deg p x
    rw [degreePart_differential deg D hD, hy, map_smul]
    rw [show p-1+1=p by omega]
  obtain ⟨z,hz⟩ := shortComplex_boundary S a ha xp hxp haxp
  refine ⟨z.val, ?_⟩
  change (K.d (p-1) p) z=xp at hz
  rw [matrixComplex_d deg D hD hsq (p-1) p (by omega)] at hz
  exact congrArg Subtype.val hz

/-- Actual categorical TF in every degree implies TF for the total finite complex. -/
theorem total_tf (deg : ι → ℤ) (D : Matrix ι ι R)
    (hD : Homogeneous deg 1 D) (hsq : D*D=0)
    (htf : ∀ p, NoZeroSMulDivisors R ((matrixComplex deg D hD hsq).homology p)) :
    NoZeroSMulDivisors R (Verification.IntegralSplitting.Homology (Matrix.toLin' D)) := by
  classical
  apply (quotient_tf_iff (Verification.IntegralSplitting.boundaryCycles (Matrix.toLin' D))).mpr
  intro a ha x hx
  obtain ⟨y,hy⟩ := hx
  have hy' : Matrix.toLin' D y=a • x.val := hy
  have hb := fun p => degree_boundary deg D hD hsq htf a ha x.val x.property ⟨y,hy'⟩ p
  choose z hz using hb
  refine ⟨∑ p ∈ Finset.univ.image deg, z p, ?_⟩
  change Matrix.toLin' D (∑ p ∈ Finset.univ.image deg, z p)=x.val
  rw [map_sum]
  simp_rw [hz]
  exact sum_degreePart deg x.val

/-- TF of total homology implies TF of the actual homology object in every degree. -/
theorem degreewise_tf (deg : ι → ℤ) (D : Matrix ι ι R)
    (hD : Homogeneous deg 1 D) (hsq : D*D=0)
    [NoZeroSMulDivisors R (Verification.IntegralSplitting.Homology (Matrix.toLin' D))]
    (p : ℤ) : NoZeroSMulDivisors R ((matrixComplex deg D hD hsq).homology p) := by
  let K := matrixComplex deg D hD hsq
  let S := K.sc' (p-1) p (p+1)
  have hs : NoZeroSMulDivisors R S.homology := by
    apply shortComplex_tf_of_boundaries S
    intro a ha x hx hax
    have hxc : Matrix.toLin' D x.val=0 := by
      change (K.d p (p+1)) x=0 at hx
      rw [matrixComplex_d deg D hD hsq p (p+1) rfl] at hx
      exact congrArg Subtype.val hx
    let z : LinearMap.ker (Matrix.toLin' D) := ⟨x.val,hxc⟩
    have haz : a • z ∈ Verification.IntegralSplitting.boundaryCycles (Matrix.toLin' D) := by
      obtain ⟨y,hy⟩ := hax
      change (K.d (p-1) p) y=a • x at hy
      rw [matrixComplex_d deg D hD hsq (p-1) p (by omega)] at hy
      exact ⟨y.val,congrArg Subtype.val hy⟩
    have hz := (quotient_tf_iff (Verification.IntegralSplitting.boundaryCycles
      (Matrix.toLin' D))).mp inferInstance a ha z haz
    obtain ⟨y,hy⟩ := hz
    change Matrix.toLin' D y=x.val at hy
    refine ⟨⟨degreePart deg (p-1) y,degreePart_mem deg (p-1) y⟩, ?_⟩
    change (K.d (p-1) p) _=x
    rw [matrixComplex_d deg D hD hsq (p-1) p (by omega)]
    apply Subtype.ext
    change Matrix.toLin' D (degreePart deg (p-1) y)=x.val
    rw [degreePart_differential deg D hD, show p-1+1=p by omega, hy]
    exact degreePart_fixed deg p x
  letI := hs
  let e := (K.homologyIsoSc' (p-1) p (p+1) (by simp) (by simp)).toLinearEquiv
  exact Function.Injective.noZeroSMulDivisors e e.injective e.map_zero e.map_smul

/-- The total TF condition used in cancellation is equivalent to degreewise categorical TF. -/
theorem total_tf_iff (deg : ι → ℤ) (D : Matrix ι ι R)
    (hD : Homogeneous deg 1 D) (hsq : D*D=0) :
    NoZeroSMulDivisors R (Verification.IntegralSplitting.Homology (Matrix.toLin' D)) ↔
      ∀ p, NoZeroSMulDivisors R ((matrixComplex deg D hD hsq).homology p) := by
  constructor
  · intro h p
    letI := h
    exact degreewise_tf deg D hD hsq p
  · exact total_tf deg D hD hsq

#print axioms quotient_tf_iff
#print axioms shortComplex_boundary
#print axioms shortComplex_tf_of_boundaries
#print axioms degreePart
#print axioms degreePart_mem
#print axioms degreePart_fixed
#print axioms degreePart_differential
#print axioms sum_degreePart
#print axioms degree_boundary
#print axioms total_tf
#print axioms degreewise_tf
#print axioms total_tf_iff

end Verification.GradedHomologyTF
