/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Data.Fintype.Option

/-!
# Finite Tensor Free

Finite tensor products of free modules are free, including the empty
tensor product. Used for the actual multivariable monic power quotient.
-/
noncomputable section
universe u v w
namespace Verification.FiniteTensorFree
open scoped TensorProduct
variable (R : Type u) [CommRing R]

theorem finite_tensor_free (I : Type v) [Finite I] (A : I → Type w)
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] [∀ i, Module.Free R (A i)] :
    Module.Free R (⨂[R] i, A i) := by
  let P (I : Type v) := ∀ (A : I → Type w) [∀ i, AddCommGroup (A i)]
    [∀ i, Module R (A i)] [∀ i, Module.Free R (A i)], Module.Free R (⨂[R] i, A i)
  have hP : P I := by
    apply Finite.induction_empty_option (P := P)
    · intro X Y e h A _ _ _
      letI : Module.Free R (⨂[R] x : X, A (e.symm.symm x)) := by
        simpa only [Equiv.symm_symm] using h (fun x => A (e x))
      exact Module.Free.of_equiv (PiTensorProduct.reindex R A e.symm).symm
    · intro A _ _ _
      exact Module.Free.of_equiv (PiTensorProduct.isEmptyEquiv PEmpty).symm
    · intro X _ h A _ _ _
      let e := Equiv.optionEquivSumPUnit X
      let N : X ⊕ PUnit.{v+1} → Type w := fun x => A (e.symm x)
      letI : Module.Free R (⨂[R] x : X, N (Sum.inl x)) := h (fun x => A (some x))
      letI : Module.Free R (⨂[R] x : PUnit.{v+1}, N (Sum.inr x)) :=
        Module.Free.of_equiv (PiTensorProduct.subsingletonEquiv (R := R) (M := A none)
          PUnit.unit).symm
      exact Module.Free.of_equiv ((PiTensorProduct.tmulEquivDep R N).trans
        (PiTensorProduct.reindex R A e).symm)
  exact hP A

#print axioms finite_tensor_free
end Verification.FiniteTensorFree
