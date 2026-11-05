/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathAffineLeftEndpoint

/-!
# Path Affine Right Endpoint

The actual right endpoint quotient respects the full period-two affine
sign change, including the last-coordinate parity of each finite word layer.
-/

namespace Verification.PathAffineRightEndpoint

open Classical Verification.PathRhoWords Verification.PathRhoFinite
  Verification.PathRhoEndpoint Verification.PathAffineSigns Verification.PathAffineIntertwiner
  Verification.PathAffineLeftEndpoint

variable {R : Type*} [CommRing R] (g ρ : R)

def signAt : Bool → Bool → ℕ → Bool
  | a, _, 0 => a
  | a, b, i+1 => signAt b a i

theorem right_prefix (a bit : Bool) (k : R) (n : ℕ) (hn : 0 < n)
    (x : List Bool →₀ R) (hx : x ∈ layer (R := R) n) :
    Verification.PathRightEndpoint.projection k (prefixMap g ρ a bit x)=
      prefixMap g ρ a bit (Verification.PathRightEndpoint.projection k x) := by
  have hf := Verification.PathRightEndpoint.projection_prepend k false n hn x hx
  have ht := Verification.PathRightEndpoint.projection_prepend k true n hn x hx
  cases a <;> cases bit <;>
    simp only [prefixMap,Bool.false_eq_true,↓reduceIte,LinearMap.add_apply,LinearMap.smul_apply,
      map_add,map_smul,hf,ht]

/-- The length-one endpoint is evaluated by the same literal affine scalar formula. -/
theorem singleton_quotient (a b bit : Bool) (k : R) :
    Verification.PathRightEndpoint.projection k (signMap g ρ a b
      (Verification.PathRightEndpoint.projection (flipConstant g ρ a k) (Finsupp.single [bit] 1)))=
      Verification.PathRightEndpoint.projection k (signMap g ρ a b (Finsupp.single [bit] 1)) := by
  cases a <;> cases bit <;>
    simp [Verification.PathRightEndpoint.projection,signMap,Finsupp.linearCombination_single,
      Verification.PathRightEndpoint.projectionColumn,signColumn,prefixMap,prepend_single,
      evaluation,flipConstant,smul_smul,add_smul]

theorem cons_quotient (a b bit : Bool) (k old : R) (n : ℕ) (hn : 0 < n)
    (x : List Bool →₀ R) (hx : x ∈ layer (R := R) n)
    (ih : Verification.PathRightEndpoint.projection k (signMap g ρ b a
      (Verification.PathRightEndpoint.projection old x))=
        Verification.PathRightEndpoint.projection k (signMap g ρ b a x)) :
    Verification.PathRightEndpoint.projection k (signMap g ρ a b
      (Verification.PathRightEndpoint.projection old (prepend bit x)))=
        Verification.PathRightEndpoint.projection k (signMap g ρ a b (prepend bit x)) := by
  rw [Verification.PathRightEndpoint.projection_prepend old bit n hn x hx,
    sign_prepend,sign_prepend]
  rw [right_prefix g ρ a bit k n hn _
    (signMap_mem_layer g ρ b a n _ (Verification.PathRightEndpoint.projection_mem_layer old n x hx))]
  rw [right_prefix g ρ a bit k n hn _ (signMap_mem_layer g ρ b a n x hx),ih]

theorem word_quotient (a b : Bool) (k : R) (n : ℕ) (w : List Bool) (hw : w.length=n+1) :
    Verification.PathRightEndpoint.projection k (signMap g ρ a b
      (Verification.PathRightEndpoint.projection (flipConstant g ρ (signAt a b n) k)
        (Finsupp.single w 1)))=
      Verification.PathRightEndpoint.projection k (signMap g ρ a b (Finsupp.single w 1)) := by
  induction n generalizing a b w with
  | zero =>
    cases w with
    | nil => simp only [List.length_nil] at hw; omega
    | cons bit tail =>
      have ht : tail=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hw; omega)
      subst tail
      exact singleton_quotient g ρ a b bit k
  | succ n ih =>
    cases w with
    | nil => simp only [List.length_nil] at hw; omega
    | cons bit tail =>
      have ht : tail.length=n+1 := by simp only [List.length_cons] at hw; omega
      simpa only [prepend_single,signAt] using
        cons_quotient g ρ a b bit k (flipConstant g ρ (signAt b a n) k) (n+1) (by omega)
          (Finsupp.single tail 1) (Finsupp.single_mem_supported R 1 ht) (ih b a tail ht)

/-- The endpoint relation descends on every vector of a fixed positive word layer. -/
theorem layer_quotient (a b : Bool) (k : R) (n : ℕ)
    (x : List Bool →₀ R) (hx : x ∈ layer (R := R) (n+1)) :
    Verification.PathRightEndpoint.projection k (signMap g ρ a b
      (Verification.PathRightEndpoint.projection (flipConstant g ρ (signAt a b n) k) x))=
      Verification.PathRightEndpoint.projection k (signMap g ρ a b x) := by
  let D := (Verification.PathRightEndpoint.projection k).comp ((signMap g ρ a b).comp
      (Verification.PathRightEndpoint.projection (flipConstant g ρ (signAt a b n) k)))-
        (Verification.PathRightEndpoint.projection k).comp (signMap g ρ a b)
  have hh : layer (R := R) (n+1) ≤ LinearMap.ker D := by
    rw [layer,Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    change Verification.PathRightEndpoint.projection k (signMap g ρ a b
      (Verification.PathRightEndpoint.projection (flipConstant g ρ (signAt a b n) k) (Finsupp.single w 1)))-
        Verification.PathRightEndpoint.projection k (signMap g ρ a b (Finsupp.single w 1))=0
    exact sub_eq_zero.mpr (word_quotient g ρ a b k n w hw)
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp (hh hx))

theorem signAt_parity (a b : Bool) (i : ℕ) : signAt a b i=if i%2=0 then a else b := by
  induction i generalizing a b with
  | zero => rfl
  | succ i ih =>
    rw [signAt,ih b a]
    by_cases hi : i%2=0
    · have hn : (i+1)%2 ≠ 0 := by omega
      simp only [hi,hn,↓reduceIte]
    · have hn : (i+1)%2=0 := by omega
      simp only [hi,hn,↓reduceIte]

#print axioms signAt
#print axioms right_prefix
#print axioms singleton_quotient
#print axioms cons_quotient
#print axioms word_quotient
#print axioms layer_quotient
#print axioms signAt_parity

end Verification.PathAffineRightEndpoint
