/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathEndpointWords
import Verification.PathRhoGrading

/-!
# Path Word Weight

Actual weight bounds for all full-rho word faces and endpoint evaluations.
-/

namespace Verification.PathWordWeight

open Classical Verification.PathRhoWords Verification.PathRhoGrading
  Verification.PathEndpointWords

variable {R : Type*} [CommRing R]

def bounded (p s : ℕ) : Submodule R (List Bool →₀ R) :=
  Finsupp.supported R R {w | p+w.count true ≤ s}

theorem normalizeLeft_count (w : List Bool) : (normalizeLeft w).count true ≤ w.count true := by
  cases w with
  | nil => rfl
  | cons a tail => cases a <;> simp [normalizeLeft]

theorem normalizeRight_count (w : List Bool) : (normalizeRight w).count true ≤ w.count true := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases w with
    | nil => cases a <;> simp [normalizeRight]
    | cons b tail =>
      cases a <;> simpa only [normalizeRight,List.count_cons,Bool.false_eq_true,
        ↓reduceIte,Nat.add_le_add_iff_right] using ih

/-- Every rho face replaces one normal symbol and possibly one repeated symbol. -/
theorem face_column_bounded (ε ρ : R) (i p s : ℕ) (w : List Bool)
    (hw : p+w.count true ≤ s) : faceColumn ε ρ i w ∈ bounded (R := R) (p+1) s := by
  rcases column_monomial ε ρ i w with hz | ⟨k,d,v,hd,hl,hc,hf⟩
  · rw [hz]; exact (bounded (p+1) s).zero_mem
  · rw [hf]
    apply (bounded (p+1) s).smul_mem
    exact Finsupp.single_mem_supported R 1 (by change p+1+v.count true ≤ s; omega)

theorem face_bounded (ε ρ : R) (i p s : ℕ) (x : List Bool →₀ R)
    (hx : x ∈ bounded (R := R) p s) : face ε ρ i x ∈ bounded (R := R) (p+1) s := by
  have hh : bounded (R := R) p s ≤ (bounded (p+1) s).comap (face ε ρ i) := by
    rw [bounded,Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    change face ε ρ i (Finsupp.single w 1) ∈ bounded (R := R) (p+1) s
    rw [face_single]
    exact face_column_bounded ε ρ i p s w hw
  exact hh hx

theorem left_bounded (k : R) (p s : ℕ) (x : List Bool →₀ R)
    (hx : x ∈ bounded (R := R) p s) :
    Verification.PathLeftEndpoint.projection k x ∈ bounded (R := R) p s := by
  have hh : bounded (R := R) p s ≤ (bounded p s).comap (Verification.PathLeftEndpoint.projection k) := by
    conv_lhs => rw [bounded,Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    change Verification.PathLeftEndpoint.projection k (Finsupp.single w 1) ∈ bounded (R := R) p s
    rw [left_projection_column]
    apply (bounded p s).smul_mem
    exact Finsupp.single_mem_supported R 1 (by
      change p+w.count true ≤ s at hw
      change p+(normalizeLeft w).count true ≤ s
      have hc := normalizeLeft_count w
      omega)
  exact hh hx

theorem right_bounded (k : R) (p s : ℕ) (x : List Bool →₀ R)
    (hx : x ∈ bounded (R := R) p s) :
    Verification.PathRightEndpoint.projection k x ∈ bounded (R := R) p s := by
  have hh : bounded (R := R) p s ≤ (bounded p s).comap (Verification.PathRightEndpoint.projection k) := by
    conv_lhs => rw [bounded,Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    change Verification.PathRightEndpoint.projection k (Finsupp.single w 1) ∈ bounded (R := R) p s
    rw [right_projection_column]
    apply (bounded p s).smul_mem
    exact Finsupp.single_mem_supported R 1 (by
      change p+w.count true ≤ s at hw
      change p+(normalizeRight w).count true ≤ s
      have hc := normalizeRight_count w
      omega)
  exact hh hx

#print axioms bounded
#print axioms normalizeLeft_count
#print axioms normalizeRight_count
#print axioms face_column_bounded
#print axioms face_bounded
#print axioms left_bounded
#print axioms right_bounded

end Verification.PathWordWeight
