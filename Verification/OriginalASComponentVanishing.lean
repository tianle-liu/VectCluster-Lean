/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ExplicitStratumTorus
import Verification.GlobalSelectedColumns
import Verification.OriginalChowExponentFamily

/-!
# Original AS Component Vanishing

AS gives integral actual zero strata, hence one actual connected
component. A positive target stratum then has a surjective joint pullback
and zero component cokernel. No connectedness or surjectivity premise is
added to the exchange hypotheses.
-/
noncomputable section
namespace Verification.OriginalASComponentVanishing
attribute [local instance] Classical.propDecidable
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
open scoped BigOperators

section Generic
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (Allowed : Finset α → Prop)
variable (hereditary : ∀ J, Allowed J → ∀ v : J, Allowed (J.erase v.val))
variable (p : ℕ) (P : AllowedComponentRow.Source Allowed p → Type*)
variable (Q : AllowedComponentRow.Target Allowed p → Type*)
variable (res : ∀ J : AllowedComponentRow.Target Allowed p, ∀ v : J.val,
  Q J → P (AllowedComponentRow.predecessor Allowed hereditary p J v))
variable (J : AllowedComponentRow.Target Allowed p)

omit [Fintype α] in
theorem jointPullback_surjective [Subsingleton (Q J)] :
    Function.Surjective (AllowedComponentRow.jointPullback Allowed hereditary p P Q res J) := by
  classical
  by_cases hq : Nonempty (Q J)
  · let q0 : Q J := Classical.choice hq
    obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0 < J.val.card by rw [J.property.1]; omega)
    let v0 : J.val := ⟨v,hv⟩
    intro y
    refine ⟨fun w _ => if w = v0 then y q0 else 0, ?_⟩
    funext q
    change (∑ w : J.val, if w = v0 then y q0 else 0) = y q
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_pos, Subsingleton.elim q0 q]
  · letI : IsEmpty (Q J) := not_nonempty_iff.mp hq
    intro y
    refine ⟨0, ?_⟩
    funext q
    exact isEmptyElim q

omit [Fintype α] in
theorem jointPullback_cokernel [Subsingleton (Q J)] :
    Subsingleton ((Q J → ℤ) ⧸ LinearMap.range
      (AllowedComponentRow.jointPullback Allowed hereditary p P Q res J)) := by
  rw [LinearMap.range_eq_top.mpr (jointPullback_surjective Allowed hereditary p P Q res J)]
  infer_instance
end Generic

section Actual
open Verification.IndependentChartIndex Verification.FrozenAcyclicCover
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (I : Finset (Fin n)) (hI : ExchangeOpenCover.Independent (laterWeights κ n B) I)
variable (hAS : AnticliqueSubcolumns.AS (fun a i => B a (Sum.inl i)) I)

include hpos hneg hsupport hI hAS in
theorem stratum_domain : IsDomain (GlobalNormalFrame.ZeroLayer R κ n I B) := by
  obtain ⟨hf,hs⟩ := (GlobalSelectedColumns.AS_iff κ n B I).mpr hAS
  let e := ExplicitStratumTorus.affineTorusEquiv R κ n I B hf hs hpos hneg hsupport hI
  exact Function.Injective.isDomain e.toRingHom e.injective

include hpos hneg hsupport hI hAS in
def components_unique :
    Unique (ConnectedComponents (PrimeSpectrum (GlobalNormalFrame.ZeroLayer R κ n I B))) := by
  letI := stratum_domain R κ n B hpos hneg hsupport I hI hAS
  refine { default := ConnectedComponents.mk (⟨⊥,Ideal.bot_prime⟩ : PrimeSpectrum (GlobalNormalFrame.ZeroLayer R κ n I B)), uniq := ?_ }
  intro c
  obtain ⟨q,rfl⟩ := ConnectedComponents.surjective_coe c
  apply ConnectedComponents.coe_eq_coe'.mpr
  rw [PreconnectedSpace.connectedComponent_eq_univ]
  exact Set.mem_univ _

variable (p : ℕ)
local notation "Allowed" => ExchangeOpenCover.Independent (laterWeights κ n B)
local notation "hered" => OriginalChowExponentFamily.hereditary κ n B
local notation "P" => OriginalChowExponentFamily.componentFamily R κ n B p
local notation "Q" => fun J : AllowedComponentRow.Target Allowed p =>
  OriginalChowExponentFamily.Components R κ n B (Subtype.val J)
variable (res : ∀ J : AllowedComponentRow.Target (ExchangeOpenCover.Independent (laterWeights κ n B)) p,
  ∀ v : J.val, OriginalChowExponentFamily.Components R κ n B J.val →
    OriginalChowExponentFamily.Components R κ n B
      (AllowedComponentRow.predecessor (ExchangeOpenCover.Independent (laterWeights κ n B))
        (OriginalChowExponentFamily.hereditary κ n B) p J v).val)
variable (J : AllowedComponentRow.Target (ExchangeOpenCover.Independent (laterWeights κ n B)) p)
variable (hASJ : AnticliqueSubcolumns.AS (fun a i => B a (Sum.inl i)) J.val)

include hpos hneg hsupport hASJ in
theorem actual_jointPullback_surjective :
    Function.Surjective (AllowedComponentRow.jointPullback Allowed hered p P Q res J) := by
  letI := components_unique (R := R) (κ := κ) (n := n) (B := B) (I := J.val)
    (hpos := hpos) (hneg := hneg) (hsupport := hsupport) (hI := J.property.2) (hAS := hASJ)
  exact jointPullback_surjective Allowed hered p P Q res J

include hpos hneg hsupport hASJ in
theorem actual_jointPullback_cokernel :
    Subsingleton ((OriginalChowExponentFamily.Components R κ n B J.val → ℤ) ⧸
      LinearMap.range (AllowedComponentRow.jointPullback Allowed hered p P Q res J)) := by
  letI := components_unique (R := R) (κ := κ) (n := n) (B := B) (I := J.val)
    (hpos := hpos) (hneg := hneg) (hsupport := hsupport) (hI := J.property.2) (hAS := hASJ)
  exact jointPullback_cokernel Allowed hered p P Q res J
end Actual

#print axioms jointPullback_surjective
#print axioms jointPullback_cokernel
#print axioms stratum_domain
#print axioms components_unique
#print axioms actual_jointPullback_surjective
#print axioms actual_jointPullback_cokernel
end Verification.OriginalASComponentVanishing
