/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ExchangeReindex
import Verification.IndependentChartPresentation

/-!
# Frozen Exchange Reindex

Arbitrary mutable relabeling of the literal global exchange algebra.
The exchange ideal and the frozen localization are transported by actual
universal maps. No sign order, independence, or rank condition is assumed.
-/
noncomputable section
namespace Verification.FrozenExchangeReindex
open MvPolynomial Verification.ActualStratum Verification.StratumPresentation
open Verification.ExchangeReindex (rows)
open Verification.FrozenAcyclicCover (noMutable)
variable (R : Type) [CommRing R]
variable {V W C : Type} [Fintype V] [Fintype W] [Fintype C]
variable (e : V ≃ W) (B : (W ⊕ C) → (W ⊕ Empty) → ℤ)
attribute [local instance] MvPolynomial.algebraMvPolynomial

def partners : (V ⊕ Empty) ≃ (W ⊕ Empty) := Equiv.sumCongr e (Equiv.refl Empty)

def matrix : (V ⊕ C) → (V ⊕ Empty) → ℤ := fun a i => B (rows e a) (partners e i)

omit [Fintype V] [Fintype W] [Fintype C] in
theorem matrix_mutable (a : V ⊕ C) (i : V) :
    matrix e B a (Sum.inl i) = ExchangeReindex.matrix e (fun a i => B a (Sum.inl i)) a i := rfl

def initialIndex (A : Type) : (A ⊕ Empty) → (A ⊕ C) := Sum.elim Sum.inl Empty.elim

theorem relations_eq {A : Type} [Fintype A] (D : (A ⊕ C) → (A ⊕ Empty) → ℤ) :
    ExchangeRelabel.relations R (initialIndex (C := C) A) D =
      exchangeIdeal (initialPolynomial R A C Empty (noMutable C))
        (exchangePolynomial R A C Empty D) := by
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  cases i with
  | inl i => rfl
  | inr t => exact t.elim

abbrev Presentation {A : Type} [Fintype A] (D : (A ⊕ C) → (A ⊕ Empty) → ℤ) :=
  FrozenOpenChart.Presentation R A C Empty (noMutable C) D

def quotientEquiv : Presentation R (matrix e B) ≃ₐ[R] Presentation R B :=
  (Ideal.quotientEquivAlgOfEq R (relations_eq R (matrix e B)).symm).trans
    ((ExchangeRelabel.quotientEquiv R (rows e) (partners e)
      (initialIndex V) (initialIndex W) (matrix e B) B
      (fun i => by cases i with | inl i => rfl | inr t => exact t.elim)
      (fun _ _ => rfl)).trans
        (Ideal.quotientEquivAlgOfEq R (relations_eq R B)))

theorem quotientEquiv_original (a : V ⊕ C) :
    quotientEquiv R e B (FrozenOpenChart.original R V C Empty (noMutable C) (matrix e B) a) =
      FrozenOpenChart.original R W C Empty (noMutable C) B (rows e a) := by
  change Ideal.Quotient.mk _
    (ExchangeRelabel.polynomialEquiv R (rows e) (partners e) (MvPolynomial.C (X a))) = _
  rw [ExchangeRelabel.polynomialEquiv_C, rename_X]
  rfl

theorem quotientEquiv_partner (i : V ⊕ Empty) :
    quotientEquiv R e B (Ideal.Quotient.mk _ (X i)) =
      Ideal.Quotient.mk _ (X (partners e i)) := by
  change Ideal.Quotient.mk _
    (ExchangeRelabel.polynomialEquiv R (rows e) (partners e) (X i)) = _
  rw [ExchangeRelabel.polynomialEquiv_X]

theorem map_frozenMonoid :
    (FrozenOpenChart.frozenMonoid R V C Empty (noMutable C) (matrix e B)).map
      (quotientEquiv R e B).toMonoidHom =
        FrozenOpenChart.frozenMonoid R W C Empty (noMutable C) B := by
  unfold FrozenOpenChart.frozenMonoid
  rw [IndependentChartPresentation.map_generated]
  apply congrArg Submonoid.closure
  apply congrArg Set.range
  funext k
  exact quotientEquiv_original R e B (Sum.inr k.val)

abbrev Global {A : Type} [Fintype A] (D : (A ⊕ C) → (A ⊕ Empty) → ℤ) :=
  FrozenOpenChart.FrozenPresentation R A C Empty (noMutable C) D

def globalEquiv : Global R (matrix e B) ≃ₐ[R] Global R B :=
  IsLocalization.algEquivOfAlgEquiv (Global R (matrix e B)) (Global R B)
    (quotientEquiv R e B) (map_frozenMonoid R e B)

def initial {A : Type} [Fintype A] (D : (A ⊕ C) → (A ⊕ Empty) → ℤ) (a : A ⊕ C) : Global R D :=
  algebraMap (Presentation R D) (Global R D)
    (FrozenOpenChart.original R A C Empty (noMutable C) D a)

def mutated {A : Type} [Fintype A] (D : (A ⊕ C) → (A ⊕ Empty) → ℤ) (i : A) : Global R D :=
  algebraMap (Presentation R D) (Global R D) (Ideal.Quotient.mk _ (X (Sum.inl i)))

theorem globalEquiv_algebraMap (p : Presentation R (matrix e B)) :
    globalEquiv R e B (algebraMap (Presentation R (matrix e B)) _ p) =
      algebraMap (Presentation R B) _ (quotientEquiv R e B p) :=
  IsLocalization.map_eq
    (M := FrozenOpenChart.frozenMonoid R V C Empty (noMutable C) (matrix e B))
    (T := FrozenOpenChart.frozenMonoid R W C Empty (noMutable C) B)
    (S := Global R (matrix e B)) (Q := Global R B)
    (g := (quotientEquiv R e B).toRingHom)
    (Submonoid.le_comap_of_map_le _ (le_of_eq (map_frozenMonoid R e B))) p

theorem globalEquiv_initial (a : V ⊕ C) :
    globalEquiv R e B (initial R (matrix e B) a) = initial R B (rows e a) := by
  rw [initial, globalEquiv_algebraMap, quotientEquiv_original]
  rfl

theorem globalEquiv_mutated (i : V) :
    globalEquiv R e B (mutated R (matrix e B) i) = mutated R B (e i) := by
  rw [mutated, globalEquiv_algebraMap, quotientEquiv_partner]
  rfl

def frozenUnit {A : Type} [Fintype A] (D : (A ⊕ C) → (A ⊕ Empty) → ℤ) (c : C) :
    (Global R D)ˣ :=
  (IsLocalization.map_units (Global R D)
    (⟨FrozenOpenChart.original R A C Empty (noMutable C) D (Sum.inr c), by
      apply Submonoid.subset_closure
      exact ⟨⟨c, by simp [noMutable]⟩, rfl⟩⟩ :
        FrozenOpenChart.frozenMonoid R A C Empty (noMutable C) D)).unit

theorem frozenUnit_val {A : Type} [Fintype A] (D : (A ⊕ C) → (A ⊕ Empty) → ℤ) (c : C) :
    (frozenUnit R D c : Global R D) = initial R D (Sum.inr c) :=
  IsUnit.unit_spec _

theorem globalEquiv_frozenUnit (c : C) :
    Units.map (globalEquiv R e B).toMonoidHom (frozenUnit R (matrix e B) c) = frozenUnit R B c := by
  apply Units.ext
  simp only [Units.coe_map, frozenUnit_val]
  exact globalEquiv_initial R e B (Sum.inr c)

theorem globalEquiv_frozenInverse (c : C) :
    globalEquiv R e B ((frozenUnit R (matrix e B) c)⁻¹ : (Global R (matrix e B))ˣ) =
      ((frozenUnit R B c)⁻¹ : (Global R B)ˣ) := by
  change (Units.map (globalEquiv R e B).toMonoidHom
    ((frozenUnit R (matrix e B) c)⁻¹) : Global R B) = _
  rw [map_inv, globalEquiv_frozenUnit]

def finiteEquiv {n m : ℕ} (d : Fin n ≃ Fin m)
    (D : (Fin m ⊕ C) → (Fin m ⊕ Empty) → ℤ) :
    FrozenAcyclicCover.Global R C n (matrix d D) ≃ₐ[R] FrozenAcyclicCover.Global R C m D :=
  AlgEquiv.ofRingEquiv (f := (globalEquiv R d D).toRingEquiv) (fun r => by
    change globalEquiv R d D
      (algebraMap (Presentation R (matrix d D)) _
        (algebraMap R (Presentation R (matrix d D)) r)) =
      algebraMap (Presentation R D) _ (algebraMap R (Presentation R D) r)
    rw [globalEquiv_algebraMap, AlgEquiv.commutes])

theorem finiteEquiv_initial {n m : ℕ} (d : Fin n ≃ Fin m)
    (D : (Fin m ⊕ C) → (Fin m ⊕ Empty) → ℤ) (a : Fin n ⊕ C) :
    finiteEquiv R d D (FrozenAcyclicCover.initial R C n (matrix d D) a) =
      FrozenAcyclicCover.initial R C m D (rows d a) := globalEquiv_initial R d D a

theorem finiteEquiv_mutated {n m : ℕ} (d : Fin n ≃ Fin m)
    (D : (Fin m ⊕ C) → (Fin m ⊕ Empty) → ℤ) (i : Fin n) :
    finiteEquiv R d D (FrozenAcyclicCover.mutated R C n (matrix d D) i) =
      FrozenAcyclicCover.mutated R C m D (d i) := globalEquiv_mutated R d D i

#print axioms partners
#print axioms matrix
#print axioms matrix_mutable
#print axioms initialIndex
#print axioms relations_eq
#print axioms Presentation
#print axioms quotientEquiv
#print axioms quotientEquiv_original
#print axioms quotientEquiv_partner
#print axioms map_frozenMonoid
#print axioms Global
#print axioms globalEquiv
#print axioms initial
#print axioms mutated
#print axioms globalEquiv_algebraMap
#print axioms globalEquiv_initial
#print axioms globalEquiv_mutated
#print axioms frozenUnit
#print axioms frozenUnit_val
#print axioms globalEquiv_frozenUnit
#print axioms globalEquiv_frozenInverse
#print axioms finiteEquiv
#print axioms finiteEquiv_initial
#print axioms finiteEquiv_mutated
end Verification.FrozenExchangeReindex
