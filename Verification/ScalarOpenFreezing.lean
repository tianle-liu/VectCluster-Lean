/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarOpenElimination
import Verification.ScalarOpenReindex
import Verification.ScalarIndependentBasicOpen

/-!
# Scalar Open Freezing

The actual principal open D(x_v) of a scalar frozen exchange ring is
another scalar frozen exchange ring with v removed from the mutable set.
The new matrix and coefficients are explicit restrictions, and the number
of mutable vertices decreases. AS transport is proved separately.
-/
noncomputable section
namespace Verification.ScalarOpenFreezing
open Verification.IndependentChartIndex Verification.ScalarFrozenGlobal
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ)
variable (m : ℕ) (h : Selected n I ≃ Fin m)

def frozenMatrix : (Fin m ⊕ (Other n I ⊕ κ)) → (Fin m ⊕ Empty) → ℤ :=
  ScalarOpenElimination.retainedMatrix (Other n I ⊕ κ) (Other n I) m
    (ScalarOpenReindex.matrix (Selected n I) (Fin m) (Other n I ⊕ κ) (Other n I)
      h (matrix κ n I B))

def frozenScalar (c : Fin n → Rˣ) (i : Fin m) : Rˣ := c (h.symm i).1

def chartFreezingEquiv : ScalarIndependentBasicOpen.BasicOpen R κ n I B a b ≃ₐ[R]
    Global R (Other n I ⊕ κ) m (frozenMatrix κ n I B m h)
      (frozenScalar R n I m h a) (frozenScalar R n I m h b) :=
  (ScalarIndependentBasicOpen.chartEquiv R κ n I B a b).trans
    ((ScalarOpenReindex.openEquiv R (Selected n I) (Fin m) (Other n I ⊕ κ) (Other n I)
      h Sum.inl (matrix κ n I B) (ScalarIndependentChartPresentation.newScalar R n I a)
      (ScalarIndependentChartPresentation.newScalar R n I b)).trans
        (ScalarOpenElimination.freezingEquiv R (Other n I ⊕ κ) (Other n I) m
          (ScalarOpenReindex.scalar R (Selected n I) (Fin m) (Other n I) h
            (ScalarIndependentChartPresentation.newScalar R n I a))
          (ScalarOpenReindex.scalar R (Selected n I) (Fin m) (Other n I) h
            (ScalarIndependentChartPresentation.newScalar R n I b)) Sum.inl
          (ScalarOpenReindex.matrix (Selected n I) (Fin m) (Other n I ⊕ κ) (Other n I)
            h (matrix κ n I B))))

omit [Fintype κ] in
theorem frozenMatrix_principal (r i : Fin m) :
    frozenMatrix κ n I B m h (Sum.inl r) (Sum.inl i) =
      B (Sum.inl (h.symm r).1) (Sum.inl (h.symm i).1) := rfl

variable (v : Fin n)

def retainedSet : Finset (Fin n) := {v}ᶜ
abbrev VertexOpen := Localization.Away (initial R κ n B a b (Sum.inl v))

theorem chartValue_vertex :
    ScalarIndependentBasicOpen.chartValue R κ n (retainedSet n v) B a b = initial R κ n B a b (Sum.inl v) := by
  classical
  simp [ScalarIndependentBasicOpen.chartValue,ExchangeOpenCover.chartElement,retainedSet]

def vertexToChart : VertexOpen R κ n B a b v ≃ₐ[R]
    ScalarIndependentBasicOpen.BasicOpen R κ n (retainedSet n v) B a b := by
  letI : IsLocalization (Submonoid.powers (initial R κ n B a b (Sum.inl v)))
      (ScalarIndependentBasicOpen.BasicOpen R κ n (retainedSet n v) B a b) := by
    rw [← chartValue_vertex R κ n B a b v]
    infer_instance
  exact (IsLocalization.algEquiv (Submonoid.powers (initial R κ n B a b (Sum.inl v)))
    (VertexOpen R κ n B a b v)
    (ScalarIndependentBasicOpen.BasicOpen R κ n (retainedSet n v) B a b)).restrictScalars R

def retainedOrder : Selected n (retainedSet n v) ≃o Fin (Fintype.card (Selected n (retainedSet n v))) :=
  (Fintype.orderIsoFinOfCardEq (Selected n (retainedSet n v)) rfl).symm

theorem retained_card_lt : Fintype.card (Selected n (retainedSet n v)) < n := by
  have hh := Fintype.card_lt_of_injective_of_not_mem
    (f := (Subtype.val : Selected n (retainedSet n v) → Fin n)) Subtype.val_injective (b := v) (by
      rintro ⟨i,hi⟩
      have hm := i.2
      rw [hi] at hm
      simp [retainedSet] at hm)
  simpa only [Fintype.card_fin] using hh

def vertexFreezingEquiv : VertexOpen R κ n B a b v ≃ₐ[R]
    Global R (Other n (retainedSet n v) ⊕ κ) (Fintype.card (Selected n (retainedSet n v)))
      (frozenMatrix κ n (retainedSet n v) B _ (retainedOrder n v).toEquiv)
      (frozenScalar R n (retainedSet n v) _ (retainedOrder n v).toEquiv a)
      (frozenScalar R n (retainedSet n v) _ (retainedOrder n v).toEquiv b) :=
  (vertexToChart R κ n B a b v).trans
    (chartFreezingEquiv R κ n (retainedSet n v) B a b _ (retainedOrder n v).toEquiv)

#print axioms frozenMatrix
#print axioms frozenScalar
#print axioms chartFreezingEquiv
#print axioms frozenMatrix_principal
#print axioms retainedSet
#print axioms VertexOpen
#print axioms chartValue_vertex
#print axioms vertexToChart
#print axioms retainedOrder
#print axioms retained_card_lt
#print axioms vertexFreezingEquiv
end Verification.ScalarOpenFreezing
