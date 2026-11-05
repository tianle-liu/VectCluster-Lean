/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FreezingOrder
import Verification.StrictPolynomialBound
import Verification.StrictEdgelessOriginal
import Verification.ScalarFramedNisnevich
import Verification.ScalarFreezingIteration
import Verification.ScalarOpenConditions

/-!
# Scalar Ordered Freezing

Strong induction for ordered freezing on actual scalar exchange
rings. The matrix class is a parameter, and its degree-zero cohomology
hypothesis is consumed only on the actual closed residual seed. It is
instantiated by the separately proved edgeless and path-forest results.
-/
noncomputable section
namespace Verification.ScalarOrderedFreezing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
open Verification.ScalarOpenFreezing Verification.ScalarOpenConditions
open Verification.IndependentChartIndex Verification.StrictCohomologicalDimension
universe u
variable {M : Type u} (T : StrictNisnevichInput.Theory M)
variable (R : Type) [Field R] (N : StrictNisnevichInput.Standard T R)
variable (L : StrictPrincipalLongExact.Standard T R)
variable (C : ∀ n : ℕ, (Fin n → Fin n → ℤ) → Prop)
variable (hC : ∀ (κ : Type) [Fintype κ] (n : ℕ)
  (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ),
  (∀ s i : Fin n, ¬ s < i → (B (Sum.inl s) (Sum.inl i)).toNat=0) →
  (∀ s i : Fin n, ¬ i < s → (-B (Sum.inl s) (Sum.inl i)).toNat=0) →
  (∀ i j, earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0) →
  (∀ I : Finset (Fin n), Independent (laterWeights κ n B) I →
    AnticliqueSubcolumns.AS (fun r i => B r (Sum.inl i)) I) →
  C n (fun i j => B (Sum.inl i) (Sum.inl j)) →
  Bound T (ScalarFrozenGlobal.Global R κ n B a b) 0)

include N L hC in
theorem bound (n : ℕ) (κ : Type) [Fintype κ]
    (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ)
    (hpos : ∀ s i : Fin n, ¬ s < i → (B (Sum.inl s) (Sum.inl i)).toNat=0)
    (hneg : ∀ s i : Fin n, ¬ i < s → (-B (Sum.inl s) (Sum.inl i)).toNat=0)
    (hsupport : ∀ i j, earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)
    (hall : ∀ I : Finset (Fin n), Independent (laterWeights κ n B) I →
      AnticliqueSubcolumns.AS (fun r i => B r (Sum.inl i)) I)
    (rank : Fin n → ℕ) (hinj : Function.Injective rank)
    (horder : FreezingOrder.Good C (fun i j => B (Sum.inl i) (Sum.inl j))
      (ExchangeRing.Adjacent (laterWeights κ n B)) rank) :
    Bound T (ScalarFrozenGlobal.Global R κ n B a b) 1 := by
  induction n using Nat.strong_induction_on generalizing κ with
  | h n ih =>
    cases n with
    | zero =>
      have hz : ∀ s i : Fin 0, B (Sum.inl s) (Sum.inl i)=0 := fun s => Fin.elim0 s
      have hi : Independent (laterWeights κ 0 B) Finset.univ := by
        intro s; exact Fin.elim0 s
      intro F q hq
      exact StrictEdgelessOriginal.scalar_cohomology_zero T R N κ 0 B (hall _ hi) hz a b F q (by omega)
    | succ n =>
      obtain ⟨v,hmin⟩ := FreezingOrder.exists_minimum rank
      obtain ⟨m,r,B',c,_,⟨e⟩,⟨g,hg,hB⟩,hp,hn,hs,hA⟩ :=
        ScalarFreezingIteration.closed_scalar_seed R κ (n+1) B a b v hpos hneg hsupport hall
      have hclass : C m (fun i j => B' (Sum.inl i) (Sum.inl j)) := by
        simpa only [hB] using FreezingOrder.at_minimum C _ _ rank horder hinj v hmin m g hg
      have hclosed : Bound T (ScalarDivisorPresentation.Divisor R κ (n+1) B a b v) 0 := by
        letI := ScalarFramedNisnevich.smooth R (Fin r) m B' c (fun _=>1) hp hn hs hA
        exact of_equiv T e.toRingEquiv 0
          (StrictPolynomialBound.bound T R N _ 0 (hC (Fin r) m B' c (fun _=>1) hp hn hs hA hclass))
      let I := retainedSet (n+1) v
      let k := Fintype.card (Selected (n+1) I)
      let h := retainedOrder (n+1) v
      let f : Fin k ↪ Fin (n+1) := ⟨retainedVertex (n+1) I h,retainedVertex_injective (n+1) I h⟩
      have hf : ∀ w, w ∈ Set.range f ↔ w ≠ v := by
        intro w
        constructor
        · rintro ⟨i,rfl⟩
          have hi := (h.symm i).property
          simpa only [I,retainedSet,Finset.mem_compl,Finset.mem_singleton] using hi
        · intro hw
          have hw' : w ∈ I := by simpa [I,retainedSet] using hw
          exact ⟨h ⟨w,hw'⟩,congrArg Subtype.val (h.symm_apply_apply ⟨w,hw'⟩)⟩
      let B₁ := frozenMatrix κ (n+1) I B k h.toEquiv
      have horder₁ : FreezingOrder.Good C (fun i j => B₁ (Sum.inl i) (Sum.inl j))
          (ExchangeRing.Adjacent (laterWeights (Other (n+1) I⊕κ) k B₁)) (rank ∘ f) :=
        FreezingOrder.restrict C _ _ rank horder v hmin f hf _ _
          (fun _ _ => rfl) (adjacent_iff κ (n+1) I B h)
      have hopen : Bound T (ScalarOpenFreezing.VertexOpen R κ (n+1) B a b v) 1 := by
        apply of_equiv T (vertexFreezingEquiv R κ (n+1) B a b v).toRingEquiv 1
        exact ih k (retained_card_lt (n+1) v) (Other (n+1) I⊕κ) B₁
          (frozenScalar R (n+1) I k h.toEquiv a) (frozenScalar R (n+1) I k h.toEquiv b)
          (positive_order κ (n+1) I B h hpos) (negative_order κ (n+1) I B h hneg)
          (support κ (n+1) I B h hsupport) (allAS κ (n+1) I B h hall)
          (rank ∘ f) (hinj.comp f.injective) horder₁
      exact ScalarFramedNisnevich.freezing_bound_one T R κ (n+1) L B a b
        hpos hneg hsupport hall v hopen hclosed

#print axioms bound
end Verification.ScalarOrderedFreezing
