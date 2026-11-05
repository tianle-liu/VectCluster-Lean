/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathFirstBoundary
import Verification.PathWordNormalForm
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Path Cokernel

Actual free cokernel of the normalized first path boundary. The only length
restriction is that the all-mutable Y word has even length.
-/

namespace Verification.PathCokernel

open Classical Verification.PathWords Verification.PathWordSlides Verification.PathWordKills
  Verification.PathWordNormalForm Verification.PathFirstBoundary

/-- Exactly the weights stated in the manuscript. -/
abbrev Weight (m : Bool) (n : ℕ) := {k : Fin (n+1) // m=true → k.val % 2=0}

def Good (m : Bool) (w : List Bool) : Prop := if m then GoodY w else GoodZ w

def weight {m : Bool} {n : ℕ} (w : Word n) (h : Good m w.val) : Weight m n :=
  ⟨⟨w.val.count true, by have hh := List.count_le_length (a := true) (l := w.val); omega⟩,
    by intro hm; subst m; exact goodY_weight_even h⟩

def representative {m : Bool} {n : ℕ} (k : Weight m n) : Word n :=
  ⟨normal n k.val.val, normal_length _ _ (by have hh := k.val.isLt; omega)⟩

theorem representative_good {m : Bool} {n : ℕ} (k : Weight m n) :
    Good m (representative k).val := by
  cases m with
  | false => exact normal_goodZ _ _
  | true => exact normal_goodY _ _ (k.property rfl)

theorem representative_weight {m : Bool} {n : ℕ} (k : Weight m n) :
    weight (representative k) (representative_good k) = k := by
  apply Subtype.ext
  apply Fin.ext
  exact normal_weight _ _

theorem connected_representative {m : Bool} {n : ℕ} (w : Word n) (h : Good m w.val) :
    WordConnected w.val (representative (weight w h)).val := by
  have hg : GoodZ w.val := by cases m with
                            | false => exact h
                            | true => exact goodY_goodZ h
  simpa only [representative, weight, w.property] using goodZ_normal w.val hg

theorem killed_not_good {m : Bool} {n : ℕ} (w : Word n) (h : Killed m w) : ¬Good m w.val := by
  cases m with
  | false => exact killedZ_not_good w.val h
  | true => exact killedY_not_good w.val h

theorem good_connected {m : Bool} {u v : List Bool} (h : WordConnected u v) :
    Good m u ↔ Good m v := by
  cases m with
  | false => exact goodZ_iff_of_connected h
  | true => exact goodY_iff_of_connected h

theorem weight_connected {m : Bool} {n : ℕ} {u v : Word n} (hu : Good m u.val)
    (hv : Good m v.val) (h : WordConnected u.val v.val) : weight u hu = weight v hv := by
  apply Subtype.ext
  apply Fin.ext
  exact ((wordConnected_iff _ _).mp h).2

variable {R : Type*} [CommRing R] (m : Bool) (n : ℕ)

noncomputable def projectionColumn (w : Word n) : Weight m n →₀ R :=
  if h : Good m w.val then Finsupp.single (weight w h) 1 else 0

/-- Finite, explicit surviving-weight projection. -/
noncomputable def projection : (Word n →₀ R) →ₗ[R] (Weight m n →₀ R) :=
  Finsupp.linearCombination R (projectionColumn m n)

/-- Actual standard binary words give a section of the weight projection. -/
noncomputable def sectionMap : (Weight m n →₀ R) →ₗ[R] (Word n →₀ R) :=
  Finsupp.linearCombination R (fun k => Finsupp.single (representative k) 1)

theorem projection_single (w : Word n) :
    projection (R := R) m n (Finsupp.single w 1)=projectionColumn m n w := by
  simp only [projection, Finsupp.linearCombination_single, one_smul]

theorem section_single (k : Weight m n) :
    sectionMap (R := R) m n (Finsupp.single k 1)=Finsupp.single (representative k) 1 := by
  simp only [sectionMap, Finsupp.linearCombination_single, one_smul]

theorem projection_section :
    (projection (R := R) m n).comp (sectionMap m n)=LinearMap.id := by
  apply Finsupp.lhom_ext
  intro k r
  have hr : Finsupp.single k r = r • Finsupp.single k (1 : R) := by simp
  rw [hr, map_smul, map_smul]
  congr 1
  simp only [LinearMap.comp_apply, section_single, projection_single, projectionColumn,
    dif_pos (representative_good k), representative_weight, LinearMap.id_apply]

theorem projection_connected (u v : Word n) (h : WordConnected u.val v.val) :
    projectionColumn (R := R) m n u=projectionColumn m n v := by
  by_cases hu : Good m u.val
  · have hv := (good_connected h).mp hu
    simp only [projectionColumn, dif_pos hu, dif_pos hv, weight_connected hu hv h]
  · have hv : ¬Good m v.val := fun hv => hu ((good_connected h).mpr hv)
    simp only [projectionColumn, dif_neg hu, dif_neg hv]

/-- No extra relation among the surviving weights is introduced by any source column. -/
theorem projection_boundary :
    (projection (R := R) m n).comp (firstBoundary m n)=0 := by
  apply Finsupp.lhom_ext
  intro j r
  have hr : Finsupp.single j r = r • Finsupp.single j (1 : R) := by simp
  rw [hr, map_smul, map_smul]
  suffices hh : projection (R := R) m n (relationColumn m n j)=0 by
    simpa only [LinearMap.comp_apply, firstBoundary, Finsupp.linearCombination_single,
      one_smul, LinearMap.zero_apply, smul_zero] using congrArg (r • ·) hh
  cases j with
  | inl w =>
    simp only [relationColumn, projection_single, projectionColumn,
      dif_neg (killed_not_good w.val w.property)]
  | inr uv =>
    obtain ⟨pre,post,h₁,h₂⟩ := uv.property
    have hc : WordConnected uv.val.1.val uv.val.2.val := by
      rw [h₁,h₂]
      exact WordConnected.slide pre post
    simp only [relationColumn, map_sub, projection_single, projection_connected m n _ _ hc, sub_self]

/-- Kernel inclusion using the actual finite source, without a rank argument. -/
theorem boundary_le_kernel :
    LinearMap.range (firstBoundary (R := R) m n) ≤ LinearMap.ker (projection m n) := by
  rintro _ ⟨x,rfl⟩
  exact congrArg (fun f : _ →ₗ[R] _ => f x) (projection_boundary (R := R) m n)

/-- Every original generator differs from its canonical survivor by an actual boundary. -/
theorem generator_reduction (heven : m=true → n % 2=0) (w : Word n) :
    Finsupp.single w (1 : R)-sectionMap m n (projection m n (Finsupp.single w 1)) ∈
      LinearMap.range (firstBoundary m n) := by
  rw [projection_single]
  by_cases hw : Good m w.val
  · rw [projectionColumn, dif_pos hw, section_single]
    exact connected_boundary m n (connected_representative w hw) w.property
      (representative (weight w hw)).property
  · rw [projectionColumn, dif_neg hw, map_zero, sub_zero]
    cases m with
    | false => exact badZ_boundary n w hw
    | true => exact badY_boundary n (heven rfl) w hw

/-- The whole finite free module reduces, not just its basis vectors. -/
theorem reduction (heven : m=true → n % 2=0) (x : Word n →₀ R) :
    x-sectionMap m n (projection m n x) ∈ LinearMap.range (firstBoundary m n) := by
  let E := LinearMap.id-(sectionMap (R := R) m n).comp (projection m n)
  change E x ∈ _
  induction x using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using (LinearMap.range (firstBoundary (R := R) m n)).zero_mem
  | add x y hx hy =>
    simpa only [map_add] using (LinearMap.range (firstBoundary (R := R) m n)).add_mem hx hy
  | single w r =>
    have hr : Finsupp.single w r=r • Finsupp.single w (1 : R) := by simp
    rw [hr, map_smul]
    exact (LinearMap.range (firstBoundary (R := R) m n)).smul_mem r (generator_reduction m n heven w)

theorem boundary_eq_kernel (heven : m=true → n % 2=0) :
    LinearMap.range (firstBoundary (R := R) m n)=LinearMap.ker (projection m n) := by
  apply le_antisymm (boundary_le_kernel m n)
  intro x hx
  have hh := reduction (R := R) m n heven x
  simpa only [LinearMap.mem_ker.mp hx, map_zero, sub_zero] using hh

theorem projection_surjective : Function.Surjective (projection (R := R) m n) := by
  intro x
  refine ⟨sectionMap m n x, ?_⟩
  exact congrArg (fun f : _ →ₗ[R] _ => f x) (projection_section (R := R) m n)

/-- Literal cokernel isomorphism to one free summand in each allowed weight. -/
noncomputable def cokernelEquiv (heven : m=true → n % 2=0) :
    Cokernel (R := R) m n ≃ₗ[R] (Weight m n →₀ R) :=
  (Submodule.quotEquivOfEq _ _ (boundary_eq_kernel m n heven)).trans
    ((projection m n).quotKerEquivOfSurjective (projection_surjective m n))

#print axioms Weight
#print axioms Good
#print axioms weight
#print axioms representative
#print axioms representative_good
#print axioms representative_weight
#print axioms connected_representative
#print axioms killed_not_good
#print axioms good_connected
#print axioms weight_connected
#print axioms projectionColumn
#print axioms projection
#print axioms sectionMap
#print axioms projection_single
#print axioms section_single
#print axioms projection_section
#print axioms projection_connected
#print axioms projection_boundary
#print axioms boundary_le_kernel
#print axioms generator_reduction
#print axioms reduction
#print axioms boundary_eq_kernel
#print axioms projection_surjective
#print axioms cokernelEquiv

end Verification.PathCokernel
