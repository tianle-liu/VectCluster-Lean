/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarActualOpenChart
import Verification.ScalarLaurentPresentation

/-!
# Scalar Open Elimination

Freezing complementary vertices of a literal scalar exchange chart:
once their original coordinates are invertible, deleting their mutated
partners yields the actual scalar global ring with those columns removed.
No independent-set, acyclicity or rank hypothesis is needed for this
algebraic identification.
-/
noncomputable section
namespace Verification.ScalarOpenElimination
open MvPolynomial Verification.ScalarActualOpenChart Verification.PartialOriginalLocalization
open Verification.EliminationWithResidual
variable (R κ τ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (a b : (Fin n ⊕ τ) → Rˣ) (j : τ → κ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ τ) → ℤ)

def retainedMatrix : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ :=
  fun r => Sum.elim (fun i => B r (Sum.inl i)) Empty.elim

def retainedScalar (c : (Fin n ⊕ τ) → Rˣ) (i : Fin n) : Rˣ := c (Sum.inl i)

abbrev Retained := ScalarFrozenGlobal.Global R κ n (retainedMatrix κ τ n B)
  (retainedScalar R τ n a) (retainedScalar R τ n b)

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem map_residualIdeal :
    (residualIdeal (ActualOpenChart.localizedInitial R (Fin n) κ τ j)
      (localizedExchange R (Fin n) κ τ a b B)).map
      (mapAlgEquiv (Fin n) (openOriginalEquiv R (Fin n) κ)).toRingHom =
    ScalarLaurentPresentation.targetIdeal R κ n (retainedMatrix κ τ n B)
      (retainedScalar R τ n a) (retainedScalar R τ n b) := by
  rw [residualIdeal,ScalarLaurentPresentation.targetIdeal,PartnerScaling.relations,
    Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  change MvPolynomial.map (openOriginalEquiv R (Fin n) κ).toRingHom
    (residualRelation (ActualOpenChart.localizedInitial R (Fin n) κ τ j)
      (localizedExchange R (Fin n) κ τ a b B) i) = _
  simp only [residualRelation,map_sub,map_mul,map_C,map_X]
  change C (openOriginalEquiv R (Fin n) κ (ActualOpenChart.localizedInitial R (Fin n) κ τ j (Sum.inl i))) * X i -
    C (openOriginalEquiv R (Fin n) κ (localizedExchange R (Fin n) κ τ a b B (Sum.inl i))) = _
  rw [ActualOpenChart.localizedInitial_free,localizedExchange,ActualOpenChart.originalEquiv_generator]
  rfl

def residualEquiv :
    (MvPolynomial (Fin n) (LocalBase R (Fin n) κ) ⧸
      residualIdeal (ActualOpenChart.localizedInitial R (Fin n) κ τ j)
        (localizedExchange R (Fin n) κ τ a b B)) ≃ₐ[R]
    ScalarLaurentPresentation.LaurentPresentation R κ n (retainedMatrix κ τ n B)
      (retainedScalar R τ n a) (retainedScalar R τ n b) :=
  Ideal.quotientEquivAlg _ _ (mapAlgEquiv (Fin n) (openOriginalEquiv R (Fin n) κ))
    (map_residualIdeal R κ τ n a b j B).symm

def freezingEquiv : GlobalOpen R (Fin n) κ τ a b j B ≃ₐ[R] Retained R κ τ n a b B :=
  ((globalToLocalized R (Fin n) κ τ a b j B).restrictScalars R).trans
    (((exchangeQuotientEquiv (ActualOpenChart.localizedInitial R (Fin n) κ τ j)
      (localizedExchange R (Fin n) κ τ a b B) (fun t => coordinateUnits R (Fin n) κ (j t))
      (ActualOpenChart.localizedInitial_unit R (Fin n) κ τ j)).restrictScalars R).trans
        ((residualEquiv R κ τ n a b j B).trans
          (ScalarLaurentPresentation.globalEquiv R κ n (retainedMatrix κ τ n B)
            (retainedScalar R τ n a) (retainedScalar R τ n b)).symm))

#print axioms retainedMatrix
#print axioms retainedScalar
#print axioms Retained
#print axioms map_residualIdeal
#print axioms residualEquiv
#print axioms freezingEquiv
end Verification.ScalarOpenElimination
