/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarGlobalNormalization
import Verification.ScalarIndependentChartPresentation

/-!
# Actual Scalar Normalization

Simultaneous normalization on the original ScalarFrozenGlobal algebra.
The two scalar families are removed together, keeping every original x and
partner y polynomial and inverting precisely the original frozen variables.
-/
noncomputable section
namespace Verification.ActualScalarNormalization
open MvPolynomial
open Verification.IndependentChartPresentation (oldInitial)
open Verification.ScalarIndependentChartPresentation (oldScalar old_relations)
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : Matrix (Fin n ⊕ κ) (Fin n ⊕ Empty) ℤ)
variable (L : ((Fin n ⊕ κ) → ℤ) →ₗ[ℤ] ((Fin n ⊕ Empty) → ℤ))
variable (hL : L.comp B.mulVecLin=LinearMap.id) (a b : Fin n → Rˣ)

theorem ones_relations : ExchangeRelabel.relations R (oldInitial κ n) B=
    ScalarExchangeRelabel.relations R (oldInitial κ n) B (oldScalar R n (fun _=>1)) (oldScalar R n (fun _=>1)) := by
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  cases i with
  | inl i => simp [ExchangeRelabel.relation,ScalarExchangeRelabel.relation,
      ExchangeRelabel.powerSum,ScalarExchangeRelabel.powerSum,oldScalar]
  | inr z => exact z.elim

def quotientEquiv : ScalarFrozenGlobal.Presentation R κ n B a b ≃ₐ[R]
    ScalarFrozenGlobal.Presentation R κ n B (fun _=>1) (fun _=>1) :=
  (Ideal.quotientEquivAlgOfEq R (old_relations R κ n B a b).symm).trans
    ((ScalarGlobalNormalization.quotientEquiv R (oldInitial κ n) B L hL
      (oldScalar R n a) (oldScalar R n b)).trans
        (Ideal.quotientEquivAlgOfEq R ((ones_relations R κ n B).trans
          (old_relations R κ n B (fun _=>1) (fun _=>1)))))

def constants : (Fin n ⊕ κ) → Rˣ := SplitScalarCharacters.constants L (oldScalar R n a) (oldScalar R n b)

theorem quotient_original (r : Fin n ⊕ κ) :
    quotientEquiv R κ n B L hL a b (ScalarFrozenGlobal.original R κ n B a b r)=
      algebraMap R _ (constants R κ n L a b r : R)*
        ScalarFrozenGlobal.original R κ n B (fun _=>1) (fun _=>1) r := by
  change Ideal.Quotient.mk _ (ScalarGlobalScaling.ambient R (oldInitial κ n) B (oldScalar R n a)
    (constants R κ n L a b) (C (X r)))=_
  rw [ScalarGlobalScaling.ambient_original,map_mul]
  rfl

theorem quotient_mutated (i : Fin n) :
    quotientEquiv R κ n B L hL a b (Ideal.Quotient.mk _ (X (Sum.inl i)))=
      algebraMap R _ (ScalarGlobalScaling.partner R (oldInitial κ n) B (oldScalar R n a)
        (constants R κ n L a b) (Sum.inl i) : R)*
      (Ideal.Quotient.mk _ (X (Sum.inl i)) : ScalarFrozenGlobal.Presentation R κ n B (fun _=>1) (fun _=>1)) := by
  change Ideal.Quotient.mk _ (ScalarGlobalScaling.ambient R (oldInitial κ n) B (oldScalar R n a)
    (constants R κ n L a b) (X (Sum.inl i)))=_
  rw [ScalarGlobalScaling.ambient_X,map_mul]
  rfl

def globalEquiv : ScalarFrozenGlobal.Global R κ n B a b ≃ₐ[R]
    ScalarFrozenGlobal.Global R κ n B (fun _=>1) (fun _=>1) :=
  UnitScaledLocalization.equiv (quotientEquiv R κ n B L hL a b)
    (fun k=>ScalarFrozenGlobal.original R κ n B a b (Sum.inr k))
    (fun k=>ScalarFrozenGlobal.original R κ n B (fun _=>1) (fun _=>1) (Sum.inr k))
    (fun k=>Units.map (algebraMap R (ScalarFrozenGlobal.Presentation R κ n B (fun _=>1) (fun _=>1))).toMonoidHom
      (constants R κ n L a b (Sum.inr k)))
    (fun k=>quotient_original R κ n B L hL a b (Sum.inr k))

theorem global_original (r : Fin n ⊕ κ) :
    globalEquiv R κ n B L hL a b (ScalarFrozenGlobal.initial R κ n B a b r)=
      algebraMap R _ (constants R κ n L a b r : R)*
        ScalarFrozenGlobal.initial R κ n B (fun _=>1) (fun _=>1) r := by
  change UnitScaledLocalization.equiv _ _ _ _ _ (algebraMap _ _ _)=_
  rw [UnitScaledLocalization.equiv_algebraMap,quotient_original,map_mul]
  rfl

theorem global_mutated (i : Fin n) :
    globalEquiv R κ n B L hL a b (ScalarFrozenGlobal.mutated R κ n B a b i)=
      algebraMap R _ (ScalarGlobalScaling.partner R (oldInitial κ n) B (oldScalar R n a)
        (constants R κ n L a b) (Sum.inl i) : R)*
        ScalarFrozenGlobal.mutated R κ n B (fun _=>1) (fun _=>1) i := by
  change UnitScaledLocalization.equiv _ _ _ _ _ (algebraMap _ _ _)=_
  rw [UnitScaledLocalization.equiv_algebraMap,quotient_mutated,map_mul]
  rfl

#print axioms ones_relations
#print axioms quotientEquiv
#print axioms constants
#print axioms quotient_original
#print axioms quotient_mutated
#print axioms globalEquiv
#print axioms global_original
#print axioms global_mutated
end Verification.ActualScalarNormalization
