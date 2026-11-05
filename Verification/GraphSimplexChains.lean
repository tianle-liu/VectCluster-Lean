/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphCover
import Verification.ExteriorTotalBasis
import Verification.AugmentedSimplexContraction

/-!
# Graph Simplex Chains

The literal augmented chain differential of the induced independence complex:
finite-support coefficients on actual independent sets, with signed deletion.
The square-zero proof uses the injective actual exterior-word realization.
-/

namespace Verification.GraphSimplexChains

open Verification.GraphCover Verification.EvenDifferential Verification.EvenGraphBridge

variable {R V : Type*} [CommRing R] [Fintype V] [LinearOrder V]
  (G : SimpleGraph V) (T : Finset V)

def eraseSimplex (J : Simplex G T) (i : V) : Simplex G T :=
  ⟨J.val.erase i, fun _ hv => J.property.1 (Finset.mem_of_mem_erase hv),
    J.property.2.mono (by intro v hv; exact Finset.mem_of_mem_erase hv)⟩

noncomputable def basisBoundary (J : Simplex G T) : Simplex G T →₀ R :=
  ∑ i ∈ J.val, Finsupp.single (eraseSimplex G T J i) ((-1 : R)^rankBelow J.val i)

noncomputable def boundary : (Simplex G T →₀ R) →ₗ[R] (Simplex G T →₀ R) :=
  Finsupp.linearCombination R (basisBoundary G T)

noncomputable def realization : (Simplex G T →₀ R) →ₗ[R] ExteriorAlgebra R (V → R) :=
  Finsupp.linearCombination R (fun J => word (J.val.sort (· ≤ ·)))

omit [Fintype V] in
theorem realization_single (J : Simplex G T) (r : R) :
    realization G T (Finsupp.single J r) = r • word (J.val.sort (· ≤ ·)) :=
  Finsupp.linearCombination_single R r J

theorem realization_injective : Function.Injective (realization (R := R) G T) := by
  exact ((Verification.ExteriorTotalBasis.word_independent (R := R) (α := V)).comp
    Subtype.val Subtype.val_injective).finsuppLinearCombination_injective

/-- Literal identification with the usual signed deletion boundary in an exterior algebra. -/
theorem realization_basisBoundary (J : Simplex G T) :
    realization G T (basisBoundary (R := R) G T J) =
      Verification.AugmentedSimplexContraction.boundary (word (J.val.sort (· ≤ ·))) := by
  rw [Verification.AugmentedSimplexContraction.boundary_word]
  simp only [basisBoundary, map_sum, realization_single]
  rfl

theorem realization_boundary :
    (realization (R := R) G T).comp (boundary G T) =
      Verification.AugmentedSimplexContraction.boundary.comp (realization G T) := by
  apply Finsupp.lhom_ext
  intro J r
  simp only [LinearMap.comp_apply, boundary, Finsupp.linearCombination_single, map_smul,
    realization_basisBoundary, realization_single]

theorem boundary_squared :
    (boundary (R := R) G T).comp (boundary G T) = 0 := by
  apply LinearMap.ext
  intro f
  apply realization_injective G T
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero]
  change realization G T (boundary G T (boundary G T f)) = 0
  rw [show realization G T (boundary G T (boundary G T f)) =
      Verification.AugmentedSimplexContraction.boundary (realization G T (boundary G T f)) from
      LinearMap.congr_fun (realization_boundary (R := R) G T) (boundary G T f)]
  rw [show realization G T (boundary G T f) =
      Verification.AugmentedSimplexContraction.boundary (realization G T f) from
      LinearMap.congr_fun (realization_boundary (R := R) G T) f]
  exact LinearMap.congr_fun
    (Verification.AugmentedSimplexContraction.boundary_squared (R := R) (α := V)) (realization G T f)

omit [Fintype V] in
theorem basisBoundary_degree (J K : Simplex G T) (h : K.val.card + 1 ≠ J.val.card) :
    basisBoundary (R := R) G T J K = 0 := by
  classical
  simp only [basisBoundary, Finsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  have hne : eraseSimplex G T J i ≠ K := by
    intro he
    apply h
    have he' := congrArg (fun x : Simplex G T => x.val.card) he
    have hcard := Finset.card_erase_add_one hi
    change (J.val.erase i).card = K.val.card at he'
    omega
  simp [hne]

#print axioms eraseSimplex
#print axioms basisBoundary
#print axioms boundary
#print axioms realization
#print axioms realization_single
#print axioms realization_injective
#print axioms realization_basisBoundary
#print axioms realization_boundary
#print axioms boundary_squared
#print axioms basisBoundary_degree

end Verification.GraphSimplexChains
