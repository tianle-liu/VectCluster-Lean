/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathRhoFinite
import Verification.PathRhoEndpoint

/-!
# Path Left Endpoint

The actual idempotent imposing a constant left endpoint symbol. Its
quotient compatibility with every rho face is proved, not assumed.
-/

namespace Verification.PathLeftEndpoint

open Classical Verification.PathRhoFaces Verification.PathRhoWords
  Verification.PathRhoFinite Verification.PathRhoEndpoint

variable {R : Type*} [CommRing R] (k : R)

noncomputable def projectionColumn : List Bool → (List Bool →₀ R)
  | [] => Finsupp.single [] 1
  | a::tail => evaluation k a • Finsupp.single (false::tail) 1

noncomputable def projection : (List Bool →₀ R) →ₗ[R] (List Bool →₀ R) :=
  Finsupp.linearCombination R (projectionColumn k)

theorem projection_single (w : List Bool) :
    projection k (Finsupp.single w 1)=projectionColumn k w := by
  simp only [projection,Finsupp.linearCombination_single,one_smul]

theorem projection_prepend (a : Bool) (x : List Bool →₀ R) :
    projection k (prepend a x)=evaluation k a • prepend false x := by
  have hh : (projection k).comp (prepend a)=evaluation k a • prepend false := by
    apply Finsupp.lhom_ext
    intro w r
    have hr : Finsupp.single w r=r • Finsupp.single w (1 : R) := by simp
    rw [hr,map_smul,map_smul]
    congr 1
    simp only [LinearMap.comp_apply,prepend_single,projection_single,projectionColumn,LinearMap.smul_apply]
  exact congrArg (fun f : _ →ₗ[R] _ => f x) hh

theorem projection_idempotent : (projection k).comp (projection k)=projection k := by
  apply Finsupp.lhom_ext
  intro w r
  have hr : Finsupp.single w r=r • Finsupp.single w (1 : R) := by simp
  rw [hr,map_smul,map_smul]
  congr 1
  cases w with
  | nil => simp only [LinearMap.comp_apply,projection_single,projectionColumn]
  | cons a tail =>
    simp only [LinearMap.comp_apply,projection_single,projectionColumn,map_smul,
      projection_single,evaluation,Bool.false_eq_true,↓reduceIte,one_smul]

theorem projection_mem_layer (n : ℕ) (x : List Bool →₀ R) (hx : x ∈ layer (R := R) n) :
    projection k x ∈ layer (R := R) n := by
  have hh : layer (R := R) n ≤ (layer n).comap (projection k) := by
    conv_lhs => rw [layer,Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    change projection k (Finsupp.single w 1) ∈ layer (R := R) n
    rw [projection_single]
    cases w with
    | nil => exact Finsupp.single_mem_supported R 1 hw
    | cons a tail =>
      apply (layer n).smul_mem
      exact Finsupp.single_mem_supported R 1 hw
  exact hh hx

variable (ε ρ : R)

theorem evaluation_product (hk : k*k=ρ*k) (a b : Bool) :
    evaluation k a*evaluation k b=repeatFactor ρ a b*evaluation k (a || b) := by
  cases a <;> cases b <;> simp [evaluation,repeatFactor,hk]

theorem evaluation_phase (hεk : ε*k=k) (a : Bool) :
    phase ε a*evaluation k a=evaluation k a := by
  cases a <;> simp [phase,evaluation,hεk]

theorem evaluation_merge (hεk : ε*k=k) (hk : k*k=ρ*k) (a b : Bool) :
    evaluation k a*evaluation k b=phase ε a*repeatFactor ρ a b*evaluation k (a || b) := by
  rw [mul_assoc,← evaluation_product k ρ hk]
  rw [← mul_assoc,evaluation_phase k ε hεk]

/-- A head face respects the endpoint relation even when both neighbor symbols are selected. -/
theorem head_quotient (hεk : ε*k=k) (hk : k*k=ρ*k) (a b c : Bool) (x : List Bool →₀ R) :
    projection k (face ε ρ 0 (projection k (prepend a (prepend b (prepend c x)))))=
      projection k (face ε ρ 0 (prepend a (prepend b (prepend c x)))) := by
  rw [projection_prepend,map_smul,face_head,face_head,map_smul]
  cases b with
  | false => simp only [Bool.false_eq_true,↓reduceIte,map_zero,smul_zero]
  | true =>
    simp only [↓reduceIte,map_smul,projection_prepend,phase,repeatFactor,
      Bool.false_eq_true,Bool.false_and,Bool.false_or,one_mul,evaluation,one_smul]
    simp only [smul_smul]
    congr 1
    exact evaluation_merge k ε ρ hεk hk a c

/-- Every face away from the endpoint also preserves its relation. -/
theorem tail_quotient (hεk : ε*k=k) (i : ℕ) (a : Bool) (x : List Bool →₀ R) :
    projection k (face ε ρ (i+1) (projection k (prepend a x)))=
      projection k (face ε ρ (i+1) (prepend a x)) := by
  simp only [projection_prepend,map_smul,face_prepend]
  simp only [phase,evaluation,Bool.false_eq_true,↓reduceIte,one_smul,smul_smul]
  cases a <;> simp only [Bool.false_eq_true,↓reduceIte,one_mul,hεk]

/-- The full all-position quotient identity for the actual left endpoint projection. -/
theorem projection_face_quotient (hεk : ε*k=k) (hk : k*k=ρ*k) (i : ℕ) :
    (projection k).comp ((face ε ρ i).comp (projection k))=
      (projection k).comp (face ε ρ i) := by
  apply Finsupp.lhom_ext
  intro w r
  have hr : Finsupp.single w r=r • Finsupp.single w (1 : R) := by simp
  rw [hr,map_smul,map_smul]
  congr 1
  change projection k (face ε ρ i (projection k (Finsupp.single w 1)))=
    projection k (face ε ρ i (Finsupp.single w 1))
  cases i with
  | zero =>
    cases w with
    | nil => simp only [projection_single,projectionColumn,face_nil,map_zero]
    | cons a w =>
      cases w with
      | nil => simp only [projection_single,projectionColumn,map_smul,face_single,faceColumn,map_zero,smul_zero]
      | cons b w =>
        cases w with
        | nil => simp only [projection_single,projectionColumn,map_smul,face_single,faceColumn,map_zero,smul_zero]
        | cons c tail =>
          simpa only [prepend_single] using head_quotient k ε ρ hεk hk a b c (Finsupp.single tail 1)
  | succ i =>
    cases w with
    | nil => simp only [projection_single,projectionColumn,face_nil,map_zero]
    | cons a w =>
      simpa only [prepend_single] using tail_quotient k ε ρ hεk i a (Finsupp.single w 1)

#print axioms projectionColumn
#print axioms projection
#print axioms projection_single
#print axioms projection_prepend
#print axioms projection_idempotent
#print axioms projection_mem_layer
#print axioms evaluation_product
#print axioms evaluation_phase
#print axioms evaluation_merge
#print axioms head_quotient
#print axioms tail_quotient
#print axioms projection_face_quotient

end Verification.PathLeftEndpoint
