/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarGlobalNonzerodivisors
import Verification.ScalarDivisorPresentation

/-!
# Scalar Boundary Points

A genuine scalar global point lies on each singleton boundary and
on no other mutable boundary. This verifies that the resulting prime
boundary ideals are pairwise distinct.
-/
noncomputable section
namespace Verification.ScalarBoundaryPoints
open Verification.ScalarFrozenGlobal Verification.ScalarIndependentBasicOpen
open Verification.ScalarIndependentOpenCoordinates Verification.IndependentChartIndex
open Verification.ExchangeOpenCover
open Verification.FrozenAcyclicCover (earlierWeights laterWeights)
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ)
variable (hpos : ∀ r i : Fin n, ¬ r < i → (B (Sum.inl r) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ r i : Fin n, ¬ i < r → (-B (Sum.inl r) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hall : ∀ I : Finset (Fin n), Independent (laterWeights κ n B) I →
  AnticliqueSubcolumns.AS (fun q j => B q (Sum.inl j)) I)
include hpos hneg hsupport hall

theorem singleton_point (v : Fin n) : ∃ p : Global R κ n B a b →ₐ[R] R,
    p (initial R κ n B a b (Sum.inl v)) = 0 ∧
    ∀ w, w ≠ v → IsUnit (p (initial R κ n B a b (Sum.inl w))) := by
  have hI : Independent (laterWeights κ n B) ({v} : Finset (Fin n)) := by
    intro i hi k hk
    have hi' := Finset.mem_singleton.mp hi
    have hk' := Finset.mem_singleton.mp hk
    subst i
    subst k
    simp [ExchangeRing.Adjacent]
  obtain ⟨hf,hs⟩ := (GlobalSelectedColumns.AS_iff κ n B {v}).mpr (hall {v} hI)
  obtain ⟨p,hp⟩ := ScalarActualOpenRegular.zero_point R (Selected n {v}) (Other n {v} ⊕ κ)
    (Other n {v}) (ScalarIndependentChartPresentation.newScalar R n {v} a)
    (ScalarIndependentChartPresentation.newScalar R n {v} b) Sum.inl (matrix κ n {v} B)
    (matrix_zero_block κ n {v} B hpos hneg hsupport hI) hf hs
  let q := p.comp (chartEquiv R κ n {v} B a b).toAlgHom
  refine ⟨q.comp (IsScalarTower.toAlgHom R (Global R κ n B a b) (BasicOpen R κ n {v} B a b)),?_,?_⟩
  · change p (chartEquiv R κ n {v} B a b
      (selectedCoordinate R κ n {v} B a b ⟨v,Finset.mem_singleton_self v⟩)) = 0
    rw [chartEquiv_selectedCoordinate]
    exact hp _
  · intro w hw
    have hw' : w ∉ ({v} : Finset (Fin n)) := by simpa only [Finset.mem_singleton] using hw
    exact (complement_units R κ n {v} B a b (Sum.inl ⟨w,hw'⟩)).map q.toRingHom

include hpos hneg hsupport hall in
theorem other_not_mem [Nontrivial R] (v w : Fin n) (hw : w ≠ v) :
    initial R κ n B a b (Sum.inl w) ∉ ScalarDivisorPresentation.divisorIdeal R κ n B a b v := by
  obtain ⟨p,hp,hu⟩ := singleton_point R κ n B a b hpos hneg hsupport hall v
  have hker : ScalarDivisorPresentation.divisorIdeal R κ n B a b v ≤ RingHom.ker p.toRingHom := by
    apply Ideal.span_le.mpr
    intro z hz
    have hz' : z = initial R κ n B a b (Sum.inl v) := Set.mem_singleton_iff.mp hz
    change p z = 0
    rw [hz',hp]
  intro hm
  exact (hu w hw).ne_zero (hker hm)

theorem boundary_distinct [Nontrivial R] (v w : Fin n) (hw : w ≠ v) :
    ScalarDivisorPresentation.divisorIdeal R κ n B a b v ≠
      ScalarDivisorPresentation.divisorIdeal R κ n B a b w := by
  intro h
  apply other_not_mem R κ n B a b hpos hneg hsupport hall v w hw
  rw [h]
  exact Ideal.subset_span (Set.mem_singleton _)

#print axioms singleton_point
#print axioms other_not_mem
#print axioms boundary_distinct
end Verification.ScalarBoundaryPoints
