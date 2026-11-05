/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarActualOpenChart
import Verification.ScalarFrozenGlobal
import Verification.IndependentChartPresentation
import Verification.FrozenGlobalSmooth

/-!
# Scalar Independent Chart Presentation

The fixed global presentation relabeled at an arbitrary independent set.
This transports the literal ideals, then the open complement localization,
to the exact ActualOpenChart presentation.
-/
noncomputable section
namespace Verification.ScalarIndependentChartPresentation
open MvPolynomial Verification.IndependentChartIndex
open Verification.FrozenAcyclicCover (noMutable)
open Verification.IndependentChartPresentation (oldInitial newInitial initial_compatibility matrix_compatibility complementEmbedding originals_complement map_generated)
open Verification.ActualStratum Verification.StratumPresentation
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ)
attribute [local instance] MvPolynomial.algebraMvPolynomial

def oldScalar (c : Fin n → Rˣ) : (Fin n ⊕ Empty) → Rˣ := Sum.elim c Empty.elim

def newScalar (c : Fin n → Rˣ) : (Selected n I ⊕ Other n I) → Rˣ :=
  fun w => oldScalar R n c ((partners n I).symm w)

theorem old_relations : ScalarExchangeRelabel.relations R (oldInitial κ n) B (oldScalar R n a) (oldScalar R n b) =
    exchangeIdeal (initialPolynomial R (Fin n) κ Empty (noMutable κ))
      (ScalarFrozenGlobal.exchangeFamily R κ n B a b) := by
  unfold ScalarExchangeRelabel.relations exchangeIdeal
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext v
  cases v with
  | inl i => rfl
  | inr t => exact t.elim

theorem new_relations : ScalarExchangeRelabel.relations R (newInitial κ n I) (matrix κ n I B) (newScalar R n I a) (newScalar R n I b) =
    exchangeIdeal (initialPolynomial R (Selected n I) (Other n I ⊕ κ) (Other n I) Sum.inl)
      (ScalarActualOpenChart.exchangePolynomial R (Selected n I) (Other n I ⊕ κ) (Other n I)
        (newScalar R n I a) (newScalar R n I b) (matrix κ n I B)) := by
  unfold ScalarExchangeRelabel.relations exchangeIdeal
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext v
  cases v <;> rfl

abbrev NewPresentation := MvPolynomial (Selected n I ⊕ Other n I)
  (OriginalPolynomial R (Selected n I) (Other n I ⊕ κ)) ⧸
    exchangeIdeal (initialPolynomial R (Selected n I) (Other n I ⊕ κ) (Other n I) Sum.inl)
      (ScalarActualOpenChart.exchangePolynomial R (Selected n I) (Other n I ⊕ κ) (Other n I)
        (newScalar R n I a) (newScalar R n I b) (matrix κ n I B))

def quotientEquiv : ScalarFrozenGlobal.Presentation R κ n B a b ≃ₐ[R] NewPresentation R κ n I B a b :=
  (Ideal.quotientEquivAlgOfEq R (old_relations R κ n B a b).symm).trans
    ((ScalarExchangeRelabel.quotientEquiv R (originals κ n I) (partners n I)
      (oldInitial κ n) (newInitial κ n I) B (matrix κ n I B) (oldScalar R n a) (oldScalar R n b)
      (initial_compatibility κ n I) (matrix_compatibility κ n I B)).trans
      (Ideal.quotientEquivAlgOfEq R (new_relations R κ n I B a b)))

theorem quotientEquiv_original (q : Fin n ⊕ κ) :
    quotientEquiv R κ n I B a b (ScalarFrozenGlobal.original R κ n B a b q) =
      (Ideal.Quotient.mk
        (exchangeIdeal (initialPolynomial R (Selected n I) (Other n I ⊕ κ) (Other n I) Sum.inl)
          (ScalarActualOpenChart.exchangePolynomial R (Selected n I) (Other n I ⊕ κ) (Other n I)
            (newScalar R n I a) (newScalar R n I b) (matrix κ n I B)))
        (C (X (originals κ n I q))) : NewPresentation R κ n I B a b) := by
  change Ideal.Quotient.mk _
    (ExchangeRelabel.polynomialEquiv R (originals κ n I) (partners n I) (C (X q))) = _
  rw [ExchangeRelabel.polynomialEquiv_C,rename_X]

def complementMonoid : Submonoid (ScalarFrozenGlobal.Presentation R κ n B a b) :=
  Submonoid.closure (Set.range (fun q => ScalarFrozenGlobal.original R κ n B a b (complementEmbedding κ n I q)))

def newComplementMonoid : Submonoid (NewPresentation R κ n I B a b) :=
  (PolynomialLocalization.coefficientMonoid (α := Selected n I ⊕ Other n I)
    (PartialOriginalLocalization.coordinateMonoid R (Selected n I) (Other n I ⊕ κ))).map (Ideal.Quotient.mk _)

theorem new_complementMonoid : newComplementMonoid R κ n I B a b =
    Submonoid.closure (Set.range (fun q : Other n I ⊕ κ =>
      (Ideal.Quotient.mk _ (C (X (Sum.inr q))) : NewPresentation R κ n I B a b))) := by
  unfold newComplementMonoid PolynomialLocalization.coefficientMonoid
    PartialOriginalLocalization.coordinateMonoid
  rw [map_generated,map_generated]

theorem map_complementMonoid :
    (complementMonoid R κ n I B a b).map (quotientEquiv R κ n I B a b).toMonoidHom =
      newComplementMonoid R κ n I B a b := by
  rw [complementMonoid,map_generated,new_complementMonoid]
  apply congrArg Submonoid.closure
  apply congrArg Set.range
  funext q
  change quotientEquiv R κ n I B a b
    (ScalarFrozenGlobal.original R κ n B a b (complementEmbedding κ n I q)) = _
  rw [quotientEquiv_original,originals_complement]

def openEquiv : Localization (complementMonoid R κ n I B a b) ≃ₐ[R]
    ScalarActualOpenChart.GlobalOpen R (Selected n I) (Other n I ⊕ κ) (Other n I)
      (newScalar R n I a) (newScalar R n I b) Sum.inl (matrix κ n I B) :=
  IsLocalization.algEquivOfAlgEquiv
    (Localization (complementMonoid R κ n I B a b))
    (Localization (newComplementMonoid R κ n I B a b))
    (quotientEquiv R κ n I B a b) (map_complementMonoid R κ n I B a b)

#print axioms oldScalar
#print axioms newScalar
#print axioms old_relations
#print axioms new_relations
#print axioms NewPresentation
#print axioms quotientEquiv
#print axioms quotientEquiv_original
#print axioms complementMonoid
#print axioms newComplementMonoid
#print axioms new_complementMonoid
#print axioms map_complementMonoid
#print axioms openEquiv
end Verification.ScalarIndependentChartPresentation
