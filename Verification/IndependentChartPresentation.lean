/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.IndependentChartIndex
import Verification.FrozenGlobalSmooth

/-!
# Independent Chart Presentation

The fixed global presentation relabeled at an arbitrary independent set.
This transports the literal ideals, then the open complement localization,
to the exact ActualOpenChart presentation.
-/
noncomputable section
namespace Verification.IndependentChartPresentation
open MvPolynomial Verification.IndependentChartIndex Verification.FrozenAcyclicCover
open Verification.ActualStratum Verification.StratumPresentation
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
attribute [local instance] MvPolynomial.algebraMvPolynomial

def oldInitial : (Fin n ⊕ Empty) → (Fin n ⊕ κ) :=
  Sum.elim Sum.inl (fun t => Sum.inr (noMutable κ t))

def newInitial : (Selected n I ⊕ Other n I) → (Selected n I ⊕ (Other n I ⊕ κ)) :=
  Sum.elim Sum.inl (fun t => Sum.inr (Sum.inl t))

omit [Fintype κ] in
theorem initial_compatibility (v : Fin n ⊕ Empty) :
    newInitial κ n I (partners n I v) = originals κ n I (oldInitial κ n v) := by
  obtain ⟨w, rfl⟩ := (partners n I).symm.surjective v
  apply (originals κ n I).symm.injective
  rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  cases w <;> rfl

omit [Fintype κ] in
theorem matrix_compatibility (a : Fin n ⊕ κ) (v : Fin n ⊕ Empty) :
    matrix κ n I B (originals κ n I a) (partners n I v) = B a v := by
  simp only [matrix, Equiv.symm_apply_apply]

theorem old_relations : ExchangeRelabel.relations R (oldInitial κ n) B =
    exchangeIdeal (initialPolynomial R (Fin n) κ Empty (noMutable κ))
      (exchangePolynomial R (Fin n) κ Empty B) := by
  unfold ExchangeRelabel.relations exchangeIdeal
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext v
  cases v with
  | inl i => rfl
  | inr t => exact t.elim

theorem new_relations : ExchangeRelabel.relations R (newInitial κ n I) (matrix κ n I B) =
    exchangeIdeal (initialPolynomial R (Selected n I) (Other n I ⊕ κ) (Other n I) Sum.inl)
      (exchangePolynomial R (Selected n I) (Other n I ⊕ κ) (Other n I) (matrix κ n I B)) := by
  unfold ExchangeRelabel.relations exchangeIdeal
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext v
  cases v <;> rfl

abbrev NewPresentation := FrozenOpenChart.Presentation R (Selected n I) (Other n I ⊕ κ)
  (Other n I) Sum.inl (matrix κ n I B)

def quotientEquiv : PolynomialPresentation R κ n B ≃ₐ[R] NewPresentation R κ n I B :=
  (Ideal.quotientEquivAlgOfEq R (old_relations R κ n B).symm).trans
    ((ExchangeRelabel.quotientEquiv R (originals κ n I) (partners n I)
      (oldInitial κ n) (newInitial κ n I) B (matrix κ n I B)
      (initial_compatibility κ n I) (matrix_compatibility κ n I B)).trans
      (Ideal.quotientEquivAlgOfEq R (new_relations R κ n I B)))

theorem quotientEquiv_original (a : Fin n ⊕ κ) :
    quotientEquiv R κ n I B (FrozenOpenChart.original R (Fin n) κ Empty (noMutable κ) B a) =
      FrozenOpenChart.original R (Selected n I) (Other n I ⊕ κ) (Other n I)
        Sum.inl (matrix κ n I B) (originals κ n I a) := by
  change Ideal.Quotient.mk _
    (ExchangeRelabel.polynomialEquiv R (originals κ n I) (partners n I) (C (X a))) = _
  rw [ExchangeRelabel.polynomialEquiv_C, rename_X]
  rfl

def complementEmbedding : (Other n I ⊕ κ) → (Fin n ⊕ κ) :=
  Sum.elim (fun i => Sum.inl i.1) Sum.inr

omit [Fintype κ] in
theorem originals_complement (a : Other n I ⊕ κ) :
    originals κ n I (complementEmbedding κ n I a) = Sum.inr a := by
  apply (originals κ n I).symm.injective
  rw [Equiv.symm_apply_apply]
  cases a <;> rfl

def complementMonoid : Submonoid (PolynomialPresentation R κ n B) :=
  Submonoid.closure (Set.range (fun a => FrozenOpenChart.original R (Fin n) κ Empty
    (noMutable κ) B (complementEmbedding κ n I a)))

theorem map_generated {A D γ F : Type*} [Monoid A] [Monoid D]
    [FunLike F A D] [MonoidHomClass F A D] (f : F) (v : γ → A) :
    (Submonoid.closure (Set.range v)).map f = Submonoid.closure (Set.range (fun c => f (v c))) := by
  rw [MonoidHom.map_mclosure, ← Set.range_comp]
  rfl

theorem new_complementMonoid :
    FrozenOpenChart.complementMonoid R (Selected n I) (Other n I ⊕ κ) (Other n I)
      Sum.inl (matrix κ n I B) = Submonoid.closure (Set.range (fun a =>
        FrozenOpenChart.original R (Selected n I) (Other n I ⊕ κ) (Other n I)
          Sum.inl (matrix κ n I B) (Sum.inr a))) := by
  unfold FrozenOpenChart.complementMonoid PolynomialLocalization.coefficientMonoid
    PartialOriginalLocalization.coordinateMonoid
  rw [map_generated, map_generated]
  rfl

theorem map_complementMonoid :
    (complementMonoid R κ n I B).map (quotientEquiv R κ n I B).toMonoidHom =
      FrozenOpenChart.complementMonoid R (Selected n I) (Other n I ⊕ κ) (Other n I)
        Sum.inl (matrix κ n I B) := by
  rw [complementMonoid, map_generated, new_complementMonoid]
  apply congrArg Submonoid.closure
  apply congrArg Set.range
  funext a
  change quotientEquiv R κ n I B
    (FrozenOpenChart.original R (Fin n) κ Empty (noMutable κ) B (complementEmbedding κ n I a)) = _
  rw [quotientEquiv_original, originals_complement]

def openEquiv : Localization (complementMonoid R κ n I B) ≃ₐ[R]
    ActualOpenChart.GlobalOpen R (Selected n I) (Other n I ⊕ κ) (Other n I)
      Sum.inl (matrix κ n I B) := by
  exact IsLocalization.algEquivOfAlgEquiv
    (R := PolynomialPresentation R κ n B) (P := NewPresentation R κ n I B)
    (M := complementMonoid R κ n I B)
    (T := FrozenOpenChart.complementMonoid R (Selected n I) (Other n I ⊕ κ) (Other n I)
      Sum.inl (matrix κ n I B))
    (Localization (M := PolynomialPresentation R κ n B) (complementMonoid R κ n I B))
    (Localization (M := NewPresentation R κ n I B)
      (FrozenOpenChart.complementMonoid R (Selected n I) (Other n I ⊕ κ) (Other n I)
        Sum.inl (matrix κ n I B)))
    (quotientEquiv R κ n I B) (map_complementMonoid R κ n I B)

#print axioms oldInitial
#print axioms newInitial
#print axioms initial_compatibility
#print axioms matrix_compatibility
#print axioms old_relations
#print axioms new_relations
#print axioms NewPresentation
#print axioms quotientEquiv
#print axioms quotientEquiv_original
#print axioms complementEmbedding
#print axioms originals_complement
#print axioms complementMonoid
#print axioms map_generated
#print axioms new_complementMonoid
#print axioms map_complementMonoid
#print axioms openEquiv
end Verification.IndependentChartPresentation
