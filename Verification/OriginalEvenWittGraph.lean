/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.EvenWittOriginalParity
import Verification.EvenWittGraphComplex
import Verification.OriginalWittFamilyChange
import Verification.OriginalMutableGraph

/-!
# Original Even Witt Graph

The graph in the even Witt decomposition is the original mutable
support graph. Both its allowed strata and all original residue maps are
identified internally.
-/
noncomputable section
open scoped Classical
namespace Verification.OriginalEvenWittGraph
open CategoryTheory Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
variable (κ : Type) [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (c : Fin n → κ)
variable (hm : ∀ a i : Fin n, Even (B (Sum.inl a) (Sum.inl i)))
variable (hc : ∀ a i, B (Sum.inr a) (Sum.inl i) = if c i = a then 1 else 0)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)

abbrev graph := OriginalMutableGraph.graph (fun a i => B a (Sum.inl i))

include hpos hneg hsupport in
omit [Fintype κ] in
theorem independent_iff (I : Finset (Fin n)) :
    Independent (laterWeights κ n B) I ↔ (graph κ n B).IsIndepSet (I : Set (Fin n)) := by
  rw [OriginalMutableGraph.independent_iff]
  constructor
  · intro hI a ha i hi _
    exact IndependentChartIndex.independent_principal_zero κ n I B hpos hneg hsupport hI a i ha hi
  · intro hI a ha i hi hadj
    rcases hadj with ⟨hai,hv⟩ | ⟨hia,hv⟩
    · apply hv
      change (-B (Sum.inl i) (Sum.inl a)).toNat = 0
      have hz : B (Sum.inl i) (Sum.inl a) = 0 := hI i hi a ha (ne_of_gt hai)
      rw [hz]
      rfl
    · apply hv
      change (-B (Sum.inl a) (Sum.inl i)).toNat = 0
      have hz : B (Sum.inl a) (Sum.inl i) = 0 := hI a ha i hi (ne_of_gt hia)
      rw [hz]
      rfl

variable (hclique : ∀ a i : Fin n, a ≠ i → c a = c i → B (Sum.inl a) (Sum.inl i) ≠ 0)

include hclique in
omit [Fintype κ] in
theorem colors_injective (I : Finset (Fin n)) (hI : (graph κ n B).IsIndepSet (I : Set (Fin n))) :
    Function.Injective (fun i : I => c i.val) := by
  intro a i hai
  apply Subtype.ext
  by_contra hne
  have hp := (OriginalMutableGraph.independent_iff (fun a i => B a (Sum.inl i)) I).mp hI
  exact hclique a.val i.val hne hai (hp a.val a.property i.val i.property hne)

def iso : OriginalWittIntegerModel.complex κ n B hpos hneg hsupport ≅
    GraphBlockComplex.monomialComplex ℤ (graph κ n B) c :=
  EvenWittOriginalParity.iso κ n B c hm hc hpos hneg hsupport ≪≫
  OriginalWittFamilyChange.iso (EvenWittColumns.frozenMatrix c)
    (Independent (laterWeights κ n B)) (EvenWittGraphRealization.Allowed (graph κ n B))
    (OriginalWittIntegerModel.hereditary κ n B) (EvenWittGraphRealization.hereditary (graph κ n B))
    (EvenWittOriginalParity.frozenIndependent κ n B c)
    (EvenWittGraphRealization.independentEntries (graph κ n B) c)
    (independent_iff κ n B hpos hneg hsupport) ≪≫
  EvenWittGraphComplex.iso (graph κ n B) c (colors_injective κ n B c hclique)

#print axioms graph
#print axioms independent_iff
#print axioms colors_injective
#print axioms iso
end Verification.OriginalEvenWittGraph
