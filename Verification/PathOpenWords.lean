/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathFirstCofaces
import Verification.PathRhoFinite

/-!
# Path Open Words

Literal splitting of the preceding free coordinate, before endpoint quotients.
The two summands carry precisely the phase appearing in the original faces.
-/

namespace Verification.PathOpenWords

open Classical Verification.PathRhoWords Verification.PathRhoFaces
  Verification.PathFirstCofaces Verification.PathRhoFinite

variable {R : Type*} [CommRing R]

noncomputable def unprepend (bit : Bool) : (List Bool →₀ R) →ₗ[R] (List Bool →₀ R) :=
  Finsupp.lcomapDomain (List.cons bit) (fun _ _ h => (List.cons.inj h).2)

theorem unprepend_apply (bit : Bool) (x : List Bool →₀ R) (w : List Bool) :
    unprepend bit x w=x (bit::w) := rfl

theorem unprepend_prepend (a b : Bool) (x : List Bool →₀ R) :
    unprepend a (prepend b x)=if a=b then x else 0 := by
  ext w
  by_cases hab : a=b
  · subst b
    simp only [unprepend_apply,prepend_same,↓reduceIte]
  · simp only [unprepend_apply,prepend_other b a (Ne.symm hab) x w,hab,↓reduceIte,Finsupp.zero_apply]

theorem split_word (x : List Bool →₀ R) (hx : x []=0) :
    prepend false (unprepend false x)+prepend true (unprepend true x)=x := by
  ext w
  cases w with
  | nil => simp only [Finsupp.add_apply,prepend_nil,hx,add_zero]
  | cons a w =>
    cases a <;> simp [prepend_same,prepend_other,unprepend_apply]

theorem prepend_mem_layer (n : ℕ) (bit : Bool) (x : List Bool →₀ R)
    (hx : x ∈ layer (R := R) n) : prepend bit x ∈ layer (R := R) (n+1) := by
  have hh : layer (R := R) n ≤ (layer (n+1)).comap (prepend bit) := by
    rw [layer,Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    change prepend bit (Finsupp.single w 1) ∈ layer (R := R) (n+1)
    rw [prepend_single]
    exact Finsupp.single_mem_supported R 1 (by simpa only [List.length_cons] using congrArg (·+1) hw)
  exact hh hx

theorem unprepend_mem_layer (n : ℕ) (bit : Bool) (x : List Bool →₀ R)
    (hx : x ∈ layer (R := R) (n+1)) : unprepend bit x ∈ layer (R := R) n := by
  apply (Finsupp.mem_supported' R _).mpr
  intro w hw
  apply (Finsupp.mem_supported' R x).mp hx (bit::w)
  change (bit::w).length ≠ n+1
  change w.length ≠ n at hw
  simp only [List.length_cons]
  omega

theorem unprepend_face (ε ρ : R) (i : ℕ) (bit : Bool) (x : List Bool →₀ R) :
    unprepend bit (face ε ρ (i+1) x)=phase ε bit • face ε ρ i (unprepend bit x) := by
  have hh : (unprepend bit).comp (face ε ρ (i+1))=
      phase ε bit • (face ε ρ i).comp (unprepend bit) := by
    apply Finsupp.lhom_ext
    intro w r
    have hs : Finsupp.single w r=r • Finsupp.single w (1:R) := by simp
    rw [hs,map_smul,map_smul]
    congr 1
    cases w with
    | nil =>
      have hz : unprepend (R := R) bit (Finsupp.single [] 1)=0 := by
        ext v
        simp [unprepend_apply,Finsupp.single_apply]
      simp only [LinearMap.comp_apply,LinearMap.smul_apply,face_nil,map_zero,hz,smul_zero]
    | cons a w =>
      rw [show Finsupp.single (a::w) (1:R)=prepend a (Finsupp.single w 1) by rw [prepend_single]]
      simp only [LinearMap.comp_apply,LinearMap.smul_apply,face_prepend,map_smul,unprepend_prepend]
      by_cases h : bit=a
      · subst a
        simp only [↓reduceIte]
      · simp only [h,↓reduceIte,map_zero,smul_zero]
  exact LinearMap.congr_fun hh x

#print axioms unprepend
#print axioms unprepend_apply
#print axioms unprepend_prepend
#print axioms split_word
#print axioms prepend_mem_layer
#print axioms unprepend_mem_layer
#print axioms unprepend_face

end Verification.PathOpenWords
