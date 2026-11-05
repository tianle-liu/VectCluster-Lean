/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarLaurentPresentation
import Verification.LaurentScalarModel

/-!
# Scalar Laurent Normal Form

The ordinary scalar exchange matrix presentation and the normalized
Laurent-character presentation define the same algebra. The rescaling
changes only mutated partners.
-/
noncomputable section
namespace Verification.ScalarLaurentNormalForm
open MvPolynomial Verification.ScalarLaurentPresentation
open Verification.ExchangeCharacters
open scoped BigOperators
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ)

def principal (r i : Fin n) : ℤ := B (Sum.inl r) (Sum.inl i)
def frozenColumn (i : Fin n) : κ →₀ ℤ :=
  column Finset.univ (fun k => B (Sum.inr k) (Sum.inl i)) (fun k => Finsupp.single k 1)
def ratio (i : Fin n) : Rˣ := a i * (b i)⁻¹

def partnerUnit (i : Fin n) : (Target R κ n)ˣ :=
  Units.map (C : OriginalTorus.Torus R κ →+* Target R κ n).toMonoidHom
    (Units.map (algebraMap R (OriginalTorus.Torus R κ)).toMonoidHom (b i) *
      negativeUnit Finset.univ (fun k => B (Sum.inr k) (Sum.inl i)) (fun k => Finsupp.single k 1))

theorem target_image (i : Fin n) : targetExchange R κ n B a b i =
    C (algebraMap R _ (a i : R) * monomial
      (positive Finset.univ (fun k => B (Sum.inr k) (Sum.inl i)) (fun k => Finsupp.single k (1 : ℤ)))) *
      (∏ r : Fin n, X r ^ (principal κ n B r i).toNat) +
    C (algebraMap R _ (b i : R) * monomial
      (negative Finset.univ (fun k => B (Sum.inr k) (Sum.inl i)) (fun k => Finsupp.single k (1 : ℤ)))) *
      (∏ r : Fin n, X r ^ (-principal κ n B r i).toNat) := by
  rw [positive_monomial, negative_monomial]
  simp only [targetExchange, ScalarFrozenGlobal.scalarExchange, map_add, map_mul, map_prod, map_pow,
    PartialOriginalLocalization.polynomialMap, aeval_C, aeval_X, Fintype.prod_sum_type,
    Sum.elim_inl, Sum.elim_inr, Finset.mem_univ, Finset.prod_const, Finset.card_univ]
  change C (algebraMap R _ (a i : R)) *
      ((∏ r : Fin n, X r ^ (principal κ n B r i).toNat) *
        ∏ k : κ, C (OriginalTorus.torusCoordinate R κ k) ^ (B (Sum.inr k) (Sum.inl i)).toNat) +
    C (algebraMap R _ (b i : R)) *
      ((∏ r : Fin n, X r ^ (-principal κ n B r i).toNat) *
        ∏ k : κ, C (OriginalTorus.torusCoordinate R κ k) ^ (-B (Sum.inr k) (Sum.inl i)).toNat) = _
  simp only [OriginalTorus.torusCoordinate, ExchangeCharacters.monomial, map_mul, map_prod, map_pow]
  ring

theorem exchange_factor (i : Fin n) : targetExchange R κ n B a b i =
    (partnerUnit R κ n B b i : Target R κ n) *
      LaurentScalarModel.exchange R (principal κ n B) (frozenColumn κ n B) (ratio R n a b) i := by
  rw [target_image, positive_eq_negative_add_column, monomial_add]
  change _ = C (algebraMap R _ (b i : R) *
    monomial (negative Finset.univ (fun k => B (Sum.inr k) (Sum.inl i)) (fun k => Finsupp.single k 1))) * _
  simp only [LaurentScalarModel.exchange, ratio, frozenColumn, map_mul, Units.val_mul]
  have hu : C (algebraMap R (OriginalTorus.Torus R κ) (b i : R)) *
      C (algebraMap R (OriginalTorus.Torus R κ) ((b i)⁻¹ : Rˣ)) = (1 : Target R κ n) := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  linear_combination -(C (algebraMap R (OriginalTorus.Torus R κ) (a i : R)) *
    C (monomial (negative Finset.univ (fun k => B (Sum.inr k) (Sum.inl i)) (fun k => Finsupp.single k (1 : ℤ)))) *
    C (monomial (column Finset.univ (fun k => B (Sum.inr k) (Sum.inl i)) (fun k => Finsupp.single k (1 : ℤ)))) *
    (∏ r : Fin n, X r ^ (principal κ n B r i).toNat)) * hu

theorem targetIdeal_eq : targetIdeal R κ n B a b =
    PartnerScaling.relations (fun i => X i)
      (fun i => (partnerUnit R κ n B b i : Target R κ n) *
        LaurentScalarModel.exchange R (principal κ n B) (frozenColumn κ n B) (ratio R n a b) i) := by
  unfold targetIdeal PartnerScaling.relations
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  rw [PartnerScaling.relation, exchange_factor]
  rfl

def normalizedEquiv : LaurentPresentation R κ n B a b ≃ₐ[R]
    LaurentScalarModel.Presentation R (principal κ n B) (frozenColumn κ n B) (ratio R n a b) :=
  (Ideal.quotientEquivAlgOfEq R (targetIdeal_eq R κ n B a b)).trans
    (AlgEquiv.ofRingEquiv (f := (PartnerScaling.quotientEquiv (fun i => X i)
      (LaurentScalarModel.exchange R (principal κ n B) (frozenColumn κ n B) (ratio R n a b))
      (partnerUnit R κ n B b)).toRingEquiv) (fun r =>
        PartnerScaling.quotientEquiv_coefficient (fun i => X i)
          (LaurentScalarModel.exchange R (principal κ n B) (frozenColumn κ n B) (ratio R n a b))
          (partnerUnit R κ n B b) (algebraMap R (Target R κ n) r)))

def globalEquiv : ScalarFrozenGlobal.Global R κ n B a b ≃ₐ[R]
    LaurentScalarModel.Presentation R (principal κ n B) (frozenColumn κ n B) (ratio R n a b) :=
  (ScalarLaurentPresentation.globalEquiv R κ n B a b).trans (normalizedEquiv R κ n B a b)

#print axioms principal
#print axioms frozenColumn
#print axioms ratio
#print axioms partnerUnit
#print axioms target_image
#print axioms exchange_factor
#print axioms targetIdeal_eq
#print axioms normalizedEquiv
#print axioms globalEquiv
end Verification.ScalarLaurentNormalForm
