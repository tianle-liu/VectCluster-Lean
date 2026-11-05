/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.NatFinsuppHomology

/-!
# Nat Finsupp Homology Reverse

The reverse direction for the actual natural-graded complex, including its
zero-degree endpoint. This lets finite integral duality supply categorical TF.
-/

namespace Verification.NatFinsuppHomologyReverse

open Classical CategoryTheory
open Verification.GraphBlockComplex Verification.GradedHomologyTF
open Verification.NatFinsuppHomology

variable {R α : Type*} [CommRing R] [IsDomain R]
  (deg : α → ℕ) (D : Module.End R (α →₀ R))
  (preserves : ∀ p, ∀ f : degreeModule R deg p, D f.val ∈ degreeModule R deg (p+1))
  (square : D.comp D=0)

omit [IsDomain R] in
/-- Positive natural degrees inherit saturated boundaries from the literal total complex. -/
theorem positive_tf (htf : NoZeroSMulDivisors R (Verification.IntegralSplitting.Homology D))
    (p : ℕ) : NoZeroSMulDivisors R
      ((gradedComplex R deg D preserves square).homology (p+1)) := by
  let K := gradedComplex R deg D preserves square
  let S := K.sc' p (p+1) (p+1+1)
  have hs : NoZeroSMulDivisors R S.homology := by
    apply shortComplex_tf_of_boundaries S
    intro a ha x hx hax
    have hxc : D x.val=0 := by
      change (K.d (p+1) (p+1+1)) x=0 at hx
      rw [gradedComplex_d] at hx
      exact congrArg Subtype.val hx
    let z : LinearMap.ker D := ⟨x.val,hxc⟩
    have haz : a • z ∈ Verification.IntegralSplitting.boundaryCycles D := by
      obtain ⟨y,hy⟩ := hax
      change (K.d p (p+1)) y=a • x at hy
      rw [gradedComplex_d] at hy
      exact ⟨y.val,congrArg Subtype.val hy⟩
    obtain ⟨y,hy⟩ := (quotient_tf_iff (Verification.IntegralSplitting.boundaryCycles D)).mp
      htf a ha z haz
    have hy' : D y=x.val := hy
    refine ⟨⟨part deg p y,part_mem deg p y⟩,?_⟩
    change (K.d p (p+1)) _=x
    rw [gradedComplex_d]
    apply Subtype.ext
    change D (part deg p y)=x.val
    have hc := LinearMap.congr_fun (part_differential deg D preserves p) y
    simp only [LinearMap.comp_apply,hy'] at hc
    rw [hc,part_of_degree deg (p+1) (p+1) x,if_pos rfl]
  letI := hs
  let e := (K.homologyIsoSc' p (p+1) (p+1+1) (by simp) (by simp)).toLinearEquiv
  exact Function.Injective.noZeroSMulDivisors e e.injective e.map_zero e.map_smul

/-- Natural degree zero has no entering map; its homology is a submodule of free coordinates. -/
theorem zero_tf : NoZeroSMulDivisors R ((gradedComplex R deg D preserves square).homology 0) := by
  let K := gradedComplex R deg D preserves square
  let S := K.sc' 0 0 1
  have hs : NoZeroSMulDivisors R S.homology := by
    apply shortComplex_tf_of_boundaries S
    intro a ha x _ hax
    obtain ⟨y,hy⟩ := hax
    have hf : S.f=0 := K.shape 0 0 (by simp)
    rw [hf] at hy
    have hz : a • x.val=0 := by
      have hh := congrArg Subtype.val hy
      exact hh.symm
    have hx : x=0 := Subtype.ext ((eq_zero_or_eq_zero_of_smul_eq_zero hz).resolve_left ha)
    exact ⟨0,by rw [hx,map_zero]⟩
  letI := hs
  let e := (K.homologyIsoSc' 0 0 1 (by simp) (by simp)).toLinearEquiv
  exact Function.Injective.noZeroSMulDivisors e e.injective e.map_zero e.map_smul

/-- Total TF yields TF in every actual natural cochain degree. -/
theorem degreewise_tf (htf : NoZeroSMulDivisors R (Verification.IntegralSplitting.Homology D))
    (p : ℕ) : NoZeroSMulDivisors R ((gradedComplex R deg D preserves square).homology p) := by
  cases p with
  | zero => exact zero_tf deg D preserves square
  | succ p => exact positive_tf deg D preserves square htf p

#print axioms positive_tf
#print axioms zero_tf
#print axioms degreewise_tf

end Verification.NatFinsuppHomologyReverse
