/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathWordWeight
import Verification.PathFirstCofaces

/-!
# Path Endpoint Leading

Endpoint specialization only contributes strictly lower word weights.
The weight-preserving coefficient is independent of its constant symbol.
-/

namespace Verification.PathEndpointLeading

open Classical Verification.PathEndpointWords Verification.PathWordWeight

variable {R : Type*} [CommRing R]

theorem normalizeRight_eq_of_count (w : List Bool) :
    w.count true ≤ (normalizeRight w).count true → normalizeRight w=w := by
  induction w with
  | nil => intro _; rfl
  | cons a w ih =>
    cases w with
    | nil => cases a <;> simp [normalizeRight]
    | cons b tail =>
      intro h
      have ht : (b::tail).count true ≤ (normalizeRight (b::tail)).count true := by
        cases a <;> simpa only [normalizeRight,List.count_cons,Bool.false_eq_true,↓reduceIte,
          Nat.add_le_add_iff_right] using h
      exact congrArg (List.cons a) (ih ht)

theorem right_column_leading (k : R) (w v : List Bool) (h : w.count true ≤ v.count true) :
    Verification.PathRightEndpoint.projection k (Finsupp.single w 1) v=
      Verification.PathRightEndpoint.projection 0 (Finsupp.single w 1) v := by
  by_cases hn : RightNormal w
  · rw [right_projection_fixed k w hn,right_projection_fixed 0 w hn]
  · have hv : normalizeRight w ≠ v := by
      intro he
      exact hn (normalizeRight_eq_of_count w (by simpa only [he] using h))
    rw [right_projection_column,right_projection_column]
    simp only [Finsupp.smul_apply,Finsupp.single_apply,hv,↓reduceIte,smul_zero]

/-- Strict support uses '<' directly, including total weight zero. -/
def strictBounded (p s : ℕ) : Submodule R (List Bool →₀ R) :=
  Finsupp.supported R R {w | p+w.count true < s}

theorem right_difference_strict (k : R) (p s : ℕ) (x : List Bool →₀ R)
    (hx : x ∈ bounded (R := R) p s) :
    Verification.PathRightEndpoint.projection k x-Verification.PathRightEndpoint.projection 0 x ∈
      strictBounded (R := R) p s := by
  let D := Verification.PathRightEndpoint.projection k-Verification.PathRightEndpoint.projection (0:R)
  have hh : bounded (R := R) p s ≤ (strictBounded p s).comap D := by
    rw [bounded,Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    change D (Finsupp.single w 1) ∈ strictBounded (R := R) p s
    apply (Finsupp.mem_supported' R _).mpr
    intro v hv
    change (Verification.PathRightEndpoint.projection k (Finsupp.single w 1)-
      Verification.PathRightEndpoint.projection (0:R) (Finsupp.single w 1)) v=0
    change p+w.count true ≤ s at hw
    change ¬p+v.count true < s at hv
    rw [Finsupp.sub_apply,right_column_leading k w v (by omega),sub_self]
  exact hh hx

theorem left_strict (k : R) (p s : ℕ) (x : List Bool →₀ R)
    (hx : x ∈ strictBounded (R := R) p s) :
    Verification.PathLeftEndpoint.projection k x ∈ strictBounded (R := R) p s := by
  have hh : strictBounded (R := R) p s ≤ (strictBounded p s).comap (Verification.PathLeftEndpoint.projection k) := by
    conv_lhs => rw [strictBounded,Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    change Verification.PathLeftEndpoint.projection k (Finsupp.single w 1) ∈ strictBounded (R := R) p s
    rw [left_projection_column]
    apply (strictBounded p s).smul_mem
    apply Finsupp.single_mem_supported R 1
    change p+(normalizeLeft w).count true < s
    change p+w.count true < s at hw
    have hh := normalizeLeft_count w
    omega
  exact hh hx

theorem right_strict (k : R) (p s : ℕ) (x : List Bool →₀ R)
    (hx : x ∈ strictBounded (R := R) p s) :
    Verification.PathRightEndpoint.projection k x ∈ strictBounded (R := R) p s := by
  have hh : strictBounded (R := R) p s ≤ (strictBounded p s).comap (Verification.PathRightEndpoint.projection k) := by
    conv_lhs => rw [strictBounded,Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    change Verification.PathRightEndpoint.projection k (Finsupp.single w 1) ∈ strictBounded (R := R) p s
    rw [right_projection_column]
    apply (strictBounded p s).smul_mem
    apply Finsupp.single_mem_supported R 1
    change p+(normalizeRight w).count true < s
    change p+w.count true < s at hw
    have hh := normalizeRight_count w
    omega
  exact hh hx

#print axioms normalizeRight_eq_of_count
#print axioms right_column_leading
#print axioms strictBounded
#print axioms right_difference_strict
#print axioms left_strict
#print axioms right_strict

end Verification.PathEndpointLeading
