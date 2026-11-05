/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathAffineFaces
import Verification.PathRightEndpoint

/-!
# Path Affine Intertwiner

All-position, all-vector rho-face intertwining for actual affine signs,
with the finite word-layer restriction proved.
-/

namespace Verification.PathAffineIntertwiner

open Classical Verification.PathRhoWords Verification.PathRhoFaces Verification.PathRhoFinite
  Verification.PathAffineSigns Verification.PathAffineFaces

variable {R : Type*} [CommRing R] (g ρ : R)

def normalFactor : Bool → Bool → ℕ → R
  | _, b, 0 => if b then g else 1
  | a, b, i+1 => normalFactor b a i

theorem head_sign (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b l m r : Bool) (x : List Bool →₀ R) :
    face (-g) ρ 0 (signMap g ρ a b (prepend l (prepend m (prepend r x))))=
      normalFactor g a b 0 • signMap g ρ a b
        (face (-g) ρ 0 (prepend l (prepend m (prepend r x)))) := by
  rw [sign_prepend,sign_prepend,sign_prepend,head_prefix g ρ hg hr,face_head]
  cases m <;> simp only [Bool.false_eq_true,↓reduceIte,map_zero,smul_zero,map_smul,sign_prepend,normalFactor]

theorem word_intertwining (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (i : ℕ) (w : List Bool) (hw : i+3 ≤ w.length) :
    face (-g) ρ i (signMap g ρ a b (Finsupp.single w 1))=
      normalFactor g a b i • signMap g ρ a b (face (-g) ρ i (Finsupp.single w 1)) := by
  induction i generalizing a b w with
  | zero =>
    rcases Verification.PathRhoBraid.exists_prefix_three w hw with ⟨l,m,r,tail,rfl⟩
    simpa only [prepend_single] using head_sign g ρ hg hr a b l m r (Finsupp.single tail 1)
  | succ i ih =>
    cases w with
    | nil => simp only [List.length_nil] at hw; omega
    | cons bit tail =>
      have ht : i+3 ≤ tail.length := by simp only [List.length_cons] at hw; omega
      rw [← prepend_single,sign_prepend,far_prefix g ρ hr,ih b a tail ht,
        map_smul,face_prepend,map_smul,sign_prepend]
      simp only [normalFactor,smul_smul,mul_comm]

/-- The local formula extends to every vector of the literal finite source layer. -/
theorem layer_intertwining (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (i n : ℕ) (hn : i+3 ≤ n) (x : List Bool →₀ R) (hx : x ∈ layer (R := R) n) :
    face (-g) ρ i (signMap g ρ a b x)=
      normalFactor g a b i • signMap g ρ a b (face (-g) ρ i x) := by
  let D := (face (-g) ρ i).comp (signMap g ρ a b)-
    normalFactor g a b i • (signMap g ρ a b).comp (face (-g) ρ i)
  have hh : layer (R := R) n ≤ LinearMap.ker D := by
    rw [layer,Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    change face (-g) ρ i (signMap g ρ a b (Finsupp.single w 1))-
      normalFactor g a b i • signMap g ρ a b (face (-g) ρ i (Finsupp.single w 1))=0
    apply sub_eq_zero.mpr
    exact word_intertwining g ρ hg hr a b i w (by change w.length=n at hw; omega)
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp (hh hx))

theorem prefix_mem_layer (a bit : Bool) (n : ℕ) (x : List Bool →₀ R) (hx : x ∈ layer (R := R) n) :
    prefixMap g ρ a bit x ∈ layer (R := R) (n+1) := by
  have hfalse := Verification.PathRightEndpoint.prepend_mem_layer false n x hx
  have htrue := Verification.PathRightEndpoint.prepend_mem_layer true n x hx
  cases a <;> cases bit <;>
    simp only [prefixMap,Bool.false_eq_true,↓reduceIte,LinearMap.add_apply,LinearMap.smul_apply]
  · exact hfalse
  · exact htrue
  · exact hfalse
  · exact (layer (n+1)).add_mem ((layer (n+1)).smul_mem ρ hfalse) ((layer (n+1)).smul_mem g htrue)

theorem signColumn_mem_layer (a b : Bool) (w : List Bool) :
    signColumn g ρ a b w ∈ layer (R := R) w.length := by
  induction w generalizing a b with
  | nil => exact Finsupp.single_mem_supported R 1 rfl
  | cons bit tail ih =>
    exact prefix_mem_layer g ρ a bit tail.length _ (ih b a)

theorem signMap_mem_layer (a b : Bool) (n : ℕ) (x : List Bool →₀ R) (hx : x ∈ layer (R := R) n) :
    signMap g ρ a b x ∈ layer (R := R) n := by
  have hh : layer (R := R) n ≤ (layer n).comap (signMap g ρ a b) := by
    conv_lhs => rw [layer,Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    change signMap g ρ a b (Finsupp.single w 1) ∈ layer (R := R) n
    rw [sign_single]
    change w.length=n at hw
    simpa only [hw] using signColumn_mem_layer g ρ a b w
  exact hh hx

#print axioms normalFactor
#print axioms head_sign
#print axioms word_intertwining
#print axioms layer_intertwining
#print axioms prefix_mem_layer
#print axioms signColumn_mem_layer
#print axioms signMap_mem_layer

end Verification.PathAffineIntertwiner
