/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualScalarNormalization
import Verification.OriginalScalarOne

/-!
# Original Scalar Normalization

The scalar normalization lands in the manuscript's original scalar-free
Global algebra, with the original mutable and partner coordinates tracked.
-/
noncomputable section
namespace Verification.OriginalScalarNormalization
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : Matrix (Fin n ⊕ κ) (Fin n ⊕ Empty) ℤ)

theorem one_initial (r : Fin n ⊕ κ) :
    OriginalScalarOne.globalEquiv R κ n B (FrozenAcyclicCover.initial R κ n B r)=
      ScalarFrozenGlobal.initial R κ n B (fun _=>1) (fun _=>1) r := by
  unfold OriginalScalarOne.globalEquiv FrozenAcyclicCover.initial ScalarFrozenGlobal.initial
  rw [IsLocalization.algEquivOfAlgEquiv_eq,OriginalScalarOne.quotientEquiv_original]

theorem one_mutated (i : Fin n) :
    OriginalScalarOne.globalEquiv R κ n B (FrozenAcyclicCover.mutated R κ n B i)=
      ScalarFrozenGlobal.mutated R κ n B (fun _=>1) (fun _=>1) i := by
  unfold OriginalScalarOne.globalEquiv FrozenAcyclicCover.mutated ScalarFrozenGlobal.mutated
  rw [IsLocalization.algEquivOfAlgEquiv_eq]
  rfl

variable (L : ((Fin n ⊕ κ) → ℤ) →ₗ[ℤ] ((Fin n ⊕ Empty) → ℤ))
variable (hL : L.comp B.mulVecLin=LinearMap.id) (a b : Fin n → Rˣ)

def globalEquiv : ScalarFrozenGlobal.Global R κ n B a b ≃ₐ[R] FrozenAcyclicCover.Global R κ n B :=
  (ActualScalarNormalization.globalEquiv R κ n B L hL a b).trans (OriginalScalarOne.globalEquiv R κ n B).symm

theorem global_initial (r : Fin n ⊕ κ) :
    globalEquiv R κ n B L hL a b (ScalarFrozenGlobal.initial R κ n B a b r)=
      algebraMap R _ (ActualScalarNormalization.constants R κ n L a b r : R)*
        FrozenAcyclicCover.initial R κ n B r := by
  simp only [globalEquiv,AlgEquiv.trans_apply]
  rw [ActualScalarNormalization.global_original,map_mul,AlgEquiv.commutes]
  rw [← one_initial,AlgEquiv.symm_apply_apply]

theorem global_mutated (i : Fin n) :
    globalEquiv R κ n B L hL a b (ScalarFrozenGlobal.mutated R κ n B a b i)=
      algebraMap R _ (ScalarGlobalScaling.partner R (IndependentChartPresentation.oldInitial κ n) B
        (ScalarIndependentChartPresentation.oldScalar R n a) (ActualScalarNormalization.constants R κ n L a b)
          (Sum.inl i) : R)*FrozenAcyclicCover.mutated R κ n B i := by
  simp only [globalEquiv,AlgEquiv.trans_apply]
  rw [ActualScalarNormalization.global_mutated,map_mul,AlgEquiv.commutes]
  rw [← one_mutated,AlgEquiv.symm_apply_apply]

#print axioms one_initial
#print axioms one_mutated
#print axioms globalEquiv
#print axioms global_initial
#print axioms global_mutated
end Verification.OriginalScalarNormalization
