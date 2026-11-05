/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictEdgelessVanishing
import Verification.TorusLaurentRecursion
import Verification.OriginalEdgelessStandard
import Verification.RostEdgelessScalarModel
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-!
# Strict Edgeless Original

Arbitrary strictly A¹-invariant coefficients on the original
edgeless exchange algebra, including arbitrary unit scalar coefficients.
The torus and surface recursions are proved from the actual framed
principal opens; no torus-vanishing conclusion is an input.
-/
noncomputable section
namespace Verification.StrictEdgelessOriginal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.StrictEdgelessVanishing Verification.OriginalEdgelessStandard
universe u
variable {M : Type u} (T : StrictNisnevichInput.Theory M)
variable (k : Type) [Field k] (P : StrictNisnevichInput.Standard T k)

include P in
theorem torus_positive (n : ℕ) : Positive T (OriginalTorus.Torus k (Fin n)) := by
  induction n with
  | zero => exact of_equiv T (TorusZero.algebraEquiv k).symm.toRingEquiv P.field_zero
  | succ n ih =>
    letI : Algebra.Smooth k (OriginalTorus.Torus k (Fin n)) := TorusSmooth.torus_smooth k (Fin n)
    exact of_equiv T (TorusLaurentRecursion.successorEquiv k n).toRingEquiv
      (laurent_positive T k P (OriginalTorus.Torus k (Fin n)) ih)

variable (κ : Type) [Fintype κ] (n : ℕ)

include P in
theorem standard_positive : Positive T (StandardModel k κ n) := by
  letI : Algebra.Smooth k (OriginalTorus.Torus k (Fin (Fintype.card κ - n))) :=
    TorusSmooth.torus_smooth k (Fin (Fintype.card κ - n))
  exact factors_positive T k P (OriginalTorus.Torus k (Fin (Fintype.card κ - n)))
    (torus_positive T k P (Fintype.card κ - n)) n

variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hAS : AnticliqueSubcolumns.AS (fun a i => B a (Sum.inl i)) Finset.univ)
variable (hzero : ∀ a i : Fin n, B (Sum.inl a) (Sum.inl i) = 0)

include P hAS hzero in
theorem original_positive : Positive T (FrozenAcyclicCover.Global k κ n B) :=
  of_equiv T (standardEquiv k κ n B hAS hzero).toRingEquiv (standard_positive T k P κ n)

include P hAS hzero in
theorem scalar_positive (a b : Fin n → kˣ) : Positive T (ScalarFrozenGlobal.Global k κ n B a b) :=
  of_equiv T (RostEdgelessScalarModel.standardEquiv k κ n B a b hAS hzero).toRingEquiv
    (standard_positive T k P κ n)

include P hAS hzero in
theorem original_cohomology_zero (F : M) (q : ℕ) (hq : 0 < q) :
    IsZero (T.cohomology (Spec (CommRingCat.of (FrozenAcyclicCover.Global k κ n B))) F q) :=
  original_positive T k P κ n B hAS hzero F q hq

include P hAS hzero in
theorem scalar_cohomology_zero (a b : Fin n → kˣ) (F : M) (q : ℕ) (hq : 0 < q) :
    IsZero (T.cohomology (Spec (CommRingCat.of (ScalarFrozenGlobal.Global k κ n B a b))) F q) :=
  scalar_positive T k P κ n B hAS hzero a b F q hq

#print axioms torus_positive
#print axioms standard_positive
#print axioms original_positive
#print axioms scalar_positive
#print axioms original_cohomology_zero
#print axioms scalar_cohomology_zero
end Verification.StrictEdgelessOriginal
