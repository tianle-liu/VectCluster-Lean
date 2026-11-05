/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Real Orthants

Explicit logarithmic coordinates on every real torus orthant. These
are homeomorphisms, not just bijections or component-counting data.
-/
noncomputable section
namespace Verification.RealOrthants
variable {ι : Type*}

def signedExp (b : Bool) (t : ℝ) : ℝ := if b then -Real.exp t else Real.exp t

theorem signedExp_ne_zero (b : Bool) (t : ℝ) : signedExp b t ≠ 0 := by
  cases b <;> simp [signedExp,Real.exp_ne_zero]

theorem signedExp_sign (b : Bool) (t : ℝ) :
    if b then signedExp b t < 0 else 0 < signedExp b t := by
  cases b <;> simp [signedExp,Real.exp_pos]

theorem log_signedExp (b : Bool) (t : ℝ) : Real.log (signedExp b t)=t := by
  cases b <;> simp [signedExp,Real.log_neg_eq_log]

theorem signedExp_log (b : Bool) (x : ℝ) (hx : if b then x<0 else 0<x) :
    signedExp b (Real.log x)=x := by
  cases b with
  | false => exact Real.exp_log hx
  | true => simpa [signedExp] using congrArg Neg.neg (Real.exp_log_of_neg hx)

theorem signedExp_continuous (b : Bool) : Continuous (signedExp b) := by
  cases b
  · exact Real.continuous_exp
  · exact Real.continuous_exp.neg

def orthant (σ : ι → Bool) := {x : ι → ℝ // ∀ i, if σ i then x i<0 else 0<x i}

instance orthantTopology (σ : ι → Bool) : TopologicalSpace (orthant σ) :=
  inferInstanceAs (TopologicalSpace {x : ι → ℝ // ∀ i, if σ i then x i<0 else 0<x i})

theorem coordinate_ne_zero (σ : ι → Bool) (x : orthant σ) (i : ι) : x.val i ≠ 0 := by
  have hx := x.property i
  cases h : σ i
  · simp only [h,Bool.false_eq_true,if_false] at hx
    exact ne_of_gt hx
  · simp only [h,if_true] at hx
    exact ne_of_lt hx

def logCoordinates (σ : ι → Bool) : orthant σ ≃ₜ (ι → ℝ) where
  toFun x i := Real.log (x.val i)
  invFun t := ⟨fun i => signedExp (σ i) (t i),fun i => signedExp_sign (σ i) (t i)⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact signedExp_log (σ i) (x.val i) (x.property i)
  right_inv t := by
    funext i
    exact log_signedExp (σ i) (t i)
  continuous_toFun := continuous_pi (fun i =>
    ((continuous_apply i).comp continuous_subtype_val).log (fun x => coordinate_ne_zero σ x i))
  continuous_invFun := (continuous_pi (fun i =>
    (signedExp_continuous (σ i)).comp (continuous_apply i))).subtype_mk _

theorem contractible (σ : ι → Bool) : ContractibleSpace (orthant σ) :=
  (logCoordinates σ).contractibleSpace

theorem connected (σ : ι → Bool) : ConnectedSpace (orthant σ) := by
  letI := contractible σ
  infer_instance

#print axioms signedExp
#print axioms signedExp_ne_zero
#print axioms signedExp_sign
#print axioms log_signedExp
#print axioms signedExp_log
#print axioms signedExp_continuous
#print axioms orthant
#print axioms orthantTopology
#print axioms coordinate_ne_zero
#print axioms logCoordinates
#print axioms contractible
#print axioms connected
end Verification.RealOrthants
