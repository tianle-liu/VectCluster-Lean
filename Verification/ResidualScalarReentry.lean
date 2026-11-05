/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.IteratedASFreezing
import Verification.ScalarMatrixReconstruction
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Data.Finset.Sort

/-!
# Residual Scalar Reentry

The residual algebra is again an actual scalar global exchange
presentation, after choosing a finite frozen basis and increasing mutable
indices. The number of mutable vertices strictly decreases.
-/
noncomputable section
namespace Verification.ResidualScalarReentry
open MvPolynomial Verification.ActualScalarFreezing Verification.IteratedScalarNormalized
open Verification.ActualFreezingDivisor Verification.FreezingIndex
open Verification.ActualResidualColumns Verification.ActualFreezingCoefficient
open Verification.FrozenAcyclicCover
attribute [local instance] Verification.ActualFreezingConstraint.neighborFintype
attribute [local instance] Verification.ActualFreezingConstraint.remainingFintype
attribute [local instance] Verification.IteratedScalarFreezing.scalarPolynomialCommRing
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ) (v : Fin n)
variable (d : Multiplicative (FrozenLattice κ n B v) →* Rˣ)

def principal (r i : Remaining κ n B v) : ℤ := B (Sum.inl r.val) (Sum.inl i.val)
def frozenColumn (i : Remaining κ n B v) : QuotientLattice κ n B v :=
  (LinearMap.range (columnMap κ n B v)).mkQ (neighborColumn κ n B v i.val)
def coefficient (i : Remaining κ n B v) : Rˣ :=
  (a i.val * (b i.val)⁻¹) * d (Multiplicative.ofAdd (neighborColumn κ n B v i.val))

theorem exchange_eq (i : Remaining κ n B v) : normalizedExchange R κ n B a b v d i =
    LaurentScalarModel.exchange R (principal κ n B v) (frozenColumn κ n B v) (coefficient R κ n B a b v d) i := by
  simp only [normalizedExchange, LaurentScalarModel.exchange, principal, frozenColumn, coefficient,
    scalarMonomial, ExchangeCharacters.monomial, Units.val_mul, map_mul, mul_assoc]

def modelEquiv : NormalizedResidual R κ n B a b v d ≃ₐ[R]
    LaurentScalarModel.Presentation R (principal κ n B v) (frozenColumn κ n B v) (coefficient R κ n B a b v d) :=
  Ideal.quotientEquivAlgOfEq R (by
    unfold LaurentScalarModel.relations PartnerScaling.relations
    apply congrArg Ideal.span
    apply congrArg Set.range
    funext i
    rw [PartnerScaling.relation, PartnerScaling.relation, exchange_eq])

def reindexedMatrix {m r : ℕ} (h : Remaining κ n B v ≃ Fin m)
    (e : QuotientLattice κ n B v ≃ₗ[ℤ] (Fin r →₀ ℤ)) :
    (Fin m ⊕ Fin r) → (Fin m ⊕ Empty) → ℤ :=
  ScalarMatrixReconstruction.matrix (Fin r) m
    (fun s i => principal κ n B v (h.symm s) (h.symm i))
    (fun i => e (frozenColumn κ n B v (h.symm i)))

def reindexedCoefficient {m : ℕ} (h : Remaining κ n B v ≃ Fin m) (i : Fin m) : Rˣ :=
  coefficient R κ n B a b v d (h.symm i)

def reentryEquiv {m r : ℕ} (h : Remaining κ n B v ≃ Fin m)
    (e : QuotientLattice κ n B v ≃ₗ[ℤ] (Fin r →₀ ℤ)) :
    NormalizedResidual R κ n B a b v d ≃ₐ[R]
      ScalarFrozenGlobal.Global R (Fin r) m (reindexedMatrix κ n B v h e)
        (reindexedCoefficient R κ n B a b v d h) (fun _ => 1) :=
  (modelEquiv R κ n B a b v d).trans
    ((LaurentScalarModel.presentationEquiv R h e (principal κ n B v) (frozenColumn κ n B v)
      (coefficient R κ n B a b v d)).trans
        (ScalarMatrixReconstruction.modelEquiv R (Fin r) m
          (fun s i => principal κ n B v (h.symm s) (h.symm i))
          (fun i => e (frozenColumn κ n B v (h.symm i)))
          (fun i => coefficient R κ n B a b v d (h.symm i))))

omit [Fintype κ] in
theorem remaining_card_lt : Fintype.card (Remaining κ n B v) < n := by
  have hh := Fintype.card_lt_of_injective_of_not_mem
    (fun i : Remaining κ n B v => i.val) Subtype.coe_injective (b := v)
      (by rintro ⟨i,hi⟩; exact i.property.1 hi)
  simpa only [Fintype.card_fin] using hh

omit d in
theorem actual_scalar_reentry
    (hpos : ∀ r i : Fin n, ¬ r < i → (B (Sum.inl r) (Sum.inl i)).toNat = 0)
    (hneg : ∀ r i : Fin n, ¬ i < r → (-B (Sum.inl r) (Sum.inl i)).toNat = 0)
    (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
    (hAS : AnticliqueSubcolumns.AS (fun r w => B r (Sum.inl w)) ({v} : Finset (Fin n))) :
    ∃ (m r : ℕ) (B' : (Fin m ⊕ Fin r) → (Fin m ⊕ Empty) → ℤ) (c : Fin m → Rˣ),
      m < n ∧ Nonempty (ScalarDivisorPresentation.Divisor R κ n B a b v ≃ₐ[R]
        Polynomial (ScalarFrozenGlobal.Global R (Fin r) m B' c (fun _ => 1))) := by
  letI : Module.Free ℤ (QuotientLattice κ n B v) :=
    NormalizedScalarFreezing.quotientLattice_free κ n B v hpos hneg hsupport hAS
  obtain ⟨d,hd,⟨E⟩⟩ := actual_normalized_freezing R κ n B a b v hpos hneg hsupport hAS
  let h := (Fintype.orderIsoFinOfCardEq (Remaining κ n B v) rfl).symm.toEquiv
  let e := (Module.finBasis ℤ (QuotientLattice κ n B v)).repr
  exact ⟨_,_,reindexedMatrix κ n B v h e,reindexedCoefficient R κ n B a b v d h,
    remaining_card_lt κ n B v,⟨E.trans (Polynomial.mapAlgEquiv (reentryEquiv R κ n B a b v d h e))⟩⟩

#print axioms principal
#print axioms frozenColumn
#print axioms coefficient
#print axioms exchange_eq
#print axioms modelEquiv
#print axioms reindexedMatrix
#print axioms reindexedCoefficient
#print axioms reentryEquiv
#print axioms remaining_card_lt
#print axioms actual_scalar_reentry
end Verification.ResidualScalarReentry
