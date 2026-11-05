/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphBlockComplex
import Verification.GradedHomologyTF

/-!
# Nat Finsupp Homology

Explicit passage from natural-number graded Finsupp cohomology to total
ker/image homology. The degree-zero boundary is checked separately, so no
negative-index or truncation assumption is hidden in the change of indexing.
-/

namespace Verification.NatFinsuppHomology

open Classical CategoryTheory
open Verification.GraphBlockComplex Verification.GradedHomologyTF

variable {R α : Type*} [CommRing R]

noncomputable def part (deg : α → ℕ) (p : ℕ) : Module.End R (α →₀ R) where
  toFun f := f.filter (fun a => deg a=p)
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul

theorem part_apply (deg : α → ℕ) (p : ℕ) (f : α →₀ R) (a : α) :
    part deg p f a = if deg a=p then f a else 0 := rfl

theorem part_mem (deg : α → ℕ) (p : ℕ) (f : α →₀ R) :
    part deg p f ∈ degreeModule R deg p := by
  apply (mem_degreeModule R deg p _).mpr
  intro a ha
  simp [part_apply,ha]

theorem part_of_degree (deg : α → ℕ) (p q : ℕ)
    (f : degreeModule R deg q) : part deg p f.val = if q=p then f.val else 0 := by
  ext a
  rw [part_apply]
  by_cases hqp : q=p
  · subst q
    by_cases ha : deg a=p
    · simp [ha]
    · simp [ha,(mem_degreeModule R deg p _).mp f.property a ha]
  · by_cases ha : deg a=p
    · simp [ha,hqp,(mem_degreeModule R deg q _).mp f.property a (by omega)]
    · simp [ha,hqp]

theorem part_single (deg : α → ℕ) (p : ℕ) (a : α) (r : R) :
    part deg p (Finsupp.single a r) = if deg a=p then Finsupp.single a r else 0 := by
  exact part_of_degree deg p (deg a)
    ⟨Finsupp.single a r,Finsupp.single_mem_supported R r (by rfl)⟩

variable (deg : α → ℕ) (D : Module.End R (α →₀ R))
  (preserves : ∀ p, ∀ f : degreeModule R deg p, D f.val ∈ degreeModule R deg (p+1))
  (square : D.comp D=0)

include preserves in
theorem part_differential (p : ℕ) : D.comp (part deg p) = (part deg (p+1)).comp D := by
  apply Finsupp.lhom_ext
  intro a r
  simp only [LinearMap.comp_apply, part_single]
  have hm := preserves (deg a)
    ⟨Finsupp.single a r,Finsupp.single_mem_supported R r (by rfl)⟩
  rw [part_of_degree deg (p+1) (deg a+1) ⟨_,hm⟩]
  by_cases ha : deg a=p
  · simp [ha]
  · simp [ha]

include preserves in
theorem zero_part_differential : (part deg 0).comp D=0 := by
  apply Finsupp.lhom_ext
  intro a r
  have hm := preserves (deg a)
    ⟨Finsupp.single a r,Finsupp.single_mem_supported R r (by rfl)⟩
  change part deg 0 (D (Finsupp.single a r))=0
  rw [part_of_degree deg 0 (deg a+1) ⟨_,hm⟩, if_neg (by omega)]

theorem sum_part (f : α →₀ R) : ∑ p ∈ f.support.image deg, part deg p f=f := by
  ext a
  simp only [Finsupp.finset_sum_apply,part_apply]
  by_cases ha : f a=0
  · simp [ha]
  · have hp : deg a ∈ f.support.image deg :=
      Finset.mem_image.mpr ⟨a,Finsupp.mem_support_iff.mpr ha,rfl⟩
    simp [hp]

theorem gradedComplex_d (p : ℕ) :
    (gradedComplex R deg D preserves square).d p (p+1) =
      ModuleCat.ofHom (degreeDifferential R deg D preserves p) :=
  CochainComplex.of_d _ _ _ p

variable [IsDomain R]

omit [IsDomain R] in
/-- A torsion boundary is an actual boundary in every positive natural degree. -/
theorem positive_degree_boundary
    (htf : ∀ p, NoZeroSMulDivisors R ((gradedComplex R deg D preserves square).homology p))
    (a : R) (ha : a ≠ 0) (x : α →₀ R) (hx : D x=0)
    (hax : ∃ y, D y=a • x) (p : ℕ) : ∃ z, D z=part deg (p+1) x := by
  let K := gradedComplex R deg D preserves square
  let S := K.sc' p (p+1) (p+1+1)
  letI := htf (p+1)
  let e := (K.homologyIsoSc' p (p+1) (p+1+1) (by simp) (by simp)).symm.toLinearEquiv
  letI : NoZeroSMulDivisors R S.homology :=
    Function.Injective.noZeroSMulDivisors e e.injective e.map_zero e.map_smul
  let xp : S.X₂ := ⟨part deg (p+1) x,part_mem deg (p+1) x⟩
  have hxp : S.g xp=0 := by
    change (K.d (p+1) (p+1+1)) xp=0
    rw [gradedComplex_d]
    apply Subtype.ext
    change D (part deg (p+1) x)=0
    have hc := LinearMap.congr_fun (part_differential deg D preserves (p+1)) x
    simpa only [LinearMap.comp_apply,hx,map_zero] using hc
  have haxp : ∃ y : S.X₁, S.f y=a • xp := by
    obtain ⟨y,hy⟩ := hax
    refine ⟨⟨part deg p y,part_mem deg p y⟩,?_⟩
    change (K.d p (p+1)) _=a • xp
    rw [gradedComplex_d]
    apply Subtype.ext
    change D (part deg p y)=a • part deg (p+1) x
    have hc := LinearMap.congr_fun (part_differential deg D preserves p) y
    simpa only [LinearMap.comp_apply,hy,map_smul] using hc
  obtain ⟨z,hz⟩ := shortComplex_boundary S a ha xp hxp haxp
  refine ⟨z.val,?_⟩
  change (K.d p (p+1)) z=xp at hz
  rw [gradedComplex_d] at hz
  exact congrArg Subtype.val hz

include preserves in
/-- In degree zero no boundary enters, and the original free coordinates detect torsion. -/
theorem zero_degree_of_torsion_boundary (a : R) (ha : a ≠ 0) (x : α →₀ R)
    (hax : ∃ y, D y=a • x) : part deg 0 x=0 := by
  obtain ⟨y,hy⟩ := hax
  have hz := LinearMap.congr_fun (zero_part_differential deg D preserves) y
  change part deg 0 (D y)=0 at hz
  rw [hy,map_smul] at hz
  exact (eq_zero_or_eq_zero_of_smul_eq_zero hz).resolve_left ha

/-- The actual natural-graded cohomology TF condition implies literal total TF. -/
theorem total_tf
    (htf : ∀ p, NoZeroSMulDivisors R ((gradedComplex R deg D preserves square).homology p)) :
    NoZeroSMulDivisors R (Verification.IntegralSplitting.Homology D) := by
  apply (quotient_tf_iff (Verification.IntegralSplitting.boundaryCycles D)).mpr
  intro a ha x hx
  obtain ⟨y,hy⟩ := hx
  have hy' : D y=a • x.val := hy
  have hb : ∀ p, ∃ z, D z=part deg p x.val := by
    intro p
    cases p with
    | zero =>
      refine ⟨0,?_⟩
      rw [map_zero,zero_degree_of_torsion_boundary deg D preserves a ha x.val ⟨y,hy'⟩]
    | succ p =>
      exact positive_degree_boundary deg D preserves square htf a ha
        x.val x.property ⟨y,hy'⟩ p
  choose z hz using hb
  refine ⟨∑ p ∈ x.val.support.image deg,z p,?_⟩
  change D (∑ p ∈ x.val.support.image deg,z p)=x.val
  rw [map_sum]
  simp_rw [hz]
  exact sum_part deg x.val

#print axioms part
#print axioms part_apply
#print axioms part_mem
#print axioms part_of_degree
#print axioms part_single
#print axioms part_differential
#print axioms zero_part_differential
#print axioms sum_part
#print axioms gradedComplex_d
#print axioms positive_degree_boundary
#print axioms zero_degree_of_torsion_boundary
#print axioms total_tf

end Verification.NatFinsuppHomology
