/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarActualOpenChart
import Verification.IndependentChartPresentation

/-!
# Scalar Open Reindex

Reindexing retained mutable vertices of an actual open scalar chart.
Frozen coordinates and all scalar coefficients are transported literally.
-/
noncomputable section
namespace Verification.ScalarOpenReindex
open MvPolynomial Verification.ScalarActualOpenChart
open Verification.IndependentChartPresentation (map_generated)
open Verification.ActualStratum Verification.StratumPresentation
variable (R ι σ κ τ : Type) [CommRing R] [Fintype ι] [Fintype σ] [Fintype κ]
variable (h : ι ≃ σ) (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
variable (a b : (ι ⊕ τ) → Rˣ)
attribute [local instance] MvPolynomial.algebraMvPolynomial

def originals : ι ⊕ κ ≃ σ ⊕ κ := Equiv.sumCongr h (Equiv.refl κ)
def partners : ι ⊕ τ ≃ σ ⊕ τ := Equiv.sumCongr h (Equiv.refl τ)
def matrix : (σ ⊕ κ) → (σ ⊕ τ) → ℤ :=
  fun r v => B ((originals ι σ κ h).symm r) ((partners ι σ τ h).symm v)
def scalar (c : (ι ⊕ τ) → Rˣ) : (σ ⊕ τ) → Rˣ := fun v => c ((partners ι σ τ h).symm v)
def initial (α : Type) : (α ⊕ τ) → (α ⊕ κ) := Sum.elim Sum.inl (fun t => Sum.inr (j t))

omit [Fintype ι] [Fintype σ] [Fintype κ] in
theorem initial_compatibility (v : ι ⊕ τ) :
    initial κ τ j σ (partners ι σ τ h v) = originals ι σ κ h (initial κ τ j ι v) := by
  cases v <;> rfl

omit [Fintype ι] [Fintype σ] [Fintype κ] in
theorem matrix_compatibility (r : ι ⊕ κ) (v : ι ⊕ τ) :
    matrix ι σ κ τ h B (originals ι σ κ h r) (partners ι σ τ h v) = B r v := by
  simp only [matrix,Equiv.symm_apply_apply]

theorem relations_eq : ScalarExchangeRelabel.relations R (initial κ τ j ι) B a b =
    exchangeIdeal (initialPolynomial R ι κ τ j) (exchangePolynomial R ι κ τ a b B) := by
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext v
  cases v <;> rfl

abbrev Presentation := MvPolynomial (ι ⊕ τ) (OriginalPolynomial R ι κ) ⧸
  exchangeIdeal (initialPolynomial R ι κ τ j) (exchangePolynomial R ι κ τ a b B)

def quotientEquiv : Presentation R ι κ τ j B a b ≃ₐ[R]
    Presentation R σ κ τ j (matrix ι σ κ τ h B) (scalar R ι σ τ h a) (scalar R ι σ τ h b) :=
  (Ideal.quotientEquivAlgOfEq R (relations_eq R ι κ τ j B a b).symm).trans
    ((ScalarExchangeRelabel.quotientEquiv R (originals ι σ κ h) (partners ι σ τ h)
      (initial κ τ j ι) (initial κ τ j σ) B (matrix ι σ κ τ h B) a b
      (initial_compatibility ι σ κ τ h j) (matrix_compatibility ι σ κ τ h B)).trans
        (Ideal.quotientEquivAlgOfEq R (relations_eq R σ κ τ j (matrix ι σ κ τ h B)
          (scalar R ι σ τ h a) (scalar R ι σ τ h b))))

def original (k : κ) : Presentation R ι κ τ j B a b := Ideal.Quotient.mk _ (C (X (Sum.inr k)))

theorem quotientEquiv_original (k : κ) : quotientEquiv R ι σ κ τ h j B a b (original R ι κ τ j B a b k) =
    original R σ κ τ j (matrix ι σ κ τ h B) (scalar R ι σ τ h a) (scalar R ι σ τ h b) k := by
  change Ideal.Quotient.mk _
    (ExchangeRelabel.polynomialEquiv R (originals ι σ κ h) (partners ι σ τ h) (C (X (Sum.inr k)))) = _
  rw [ExchangeRelabel.polynomialEquiv_C,rename_X]
  rfl

def monoid : Submonoid (Presentation R ι κ τ j B a b) :=
  (PolynomialLocalization.coefficientMonoid (α := ι ⊕ τ)
    (PartialOriginalLocalization.coordinateMonoid R ι κ)).map (Ideal.Quotient.mk _)

theorem monoid_generators : monoid R ι κ τ j B a b =
    Submonoid.closure (Set.range (original R ι κ τ j B a b)) := by
  unfold monoid PolynomialLocalization.coefficientMonoid PartialOriginalLocalization.coordinateMonoid
  rw [map_generated,map_generated]
  rfl

theorem map_monoid : (monoid R ι κ τ j B a b).map (quotientEquiv R ι σ κ τ h j B a b).toMonoidHom =
    monoid R σ κ τ j (matrix ι σ κ τ h B) (scalar R ι σ τ h a) (scalar R ι σ τ h b) := by
  rw [monoid_generators,map_generated,monoid_generators]
  apply congrArg Submonoid.closure
  apply congrArg Set.range
  exact funext (quotientEquiv_original R ι σ κ τ h j B a b)

def openEquiv : GlobalOpen R ι κ τ a b j B ≃ₐ[R]
    GlobalOpen R σ κ τ (scalar R ι σ τ h a) (scalar R ι σ τ h b) j (matrix ι σ κ τ h B) :=
  IsLocalization.algEquivOfAlgEquiv (Localization (monoid R ι κ τ j B a b))
    (Localization (monoid R σ κ τ j (matrix ι σ κ τ h B) (scalar R ι σ τ h a) (scalar R ι σ τ h b)))
    (quotientEquiv R ι σ κ τ h j B a b) (map_monoid R ι σ κ τ h j B a b)

#print axioms originals
#print axioms partners
#print axioms matrix
#print axioms scalar
#print axioms initial
#print axioms initial_compatibility
#print axioms matrix_compatibility
#print axioms relations_eq
#print axioms Presentation
#print axioms quotientEquiv
#print axioms original
#print axioms quotientEquiv_original
#print axioms monoid
#print axioms monoid_generators
#print axioms map_monoid
#print axioms openEquiv
end Verification.ScalarOpenReindex
