/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalWittParityComplex
import Verification.EvenWittColumns
import Verification.OriginalWittIntegerModel

/-!
# Even Witt Original Parity

The original exchange matrix is reduced modulo two inside its literal
Witt complex. The independent-set family stays that of the original
mutable support graph; only its quotient columns are simplified.
-/
noncomputable section
open scoped Classical
namespace Verification.EvenWittOriginalParity
open CategoryTheory Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
variable (κ : Type) [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (c : Fin n → κ)
variable (hm : ∀ a i : Fin n, Even (B (Sum.inl a) (Sum.inl i)))
variable (hc : ∀ a i, B (Sum.inr a) (Sum.inl i) = if c i = a then 1 else 0)

include hm hc in
omit [Fintype κ] in
theorem parity (a : Fin n ⊕ κ) (i : Fin n) :
    (B a (Sum.inl i) : ZMod 2) = (EvenWittColumns.frozenMatrix c a i : ZMod 2) := by
  cases a with
  | inl a =>
    obtain ⟨b,hb⟩ := hm a i
    rw [hb]
    simp [EvenWittColumns.frozenMatrix,← two_mul,show (2 : ZMod 2) = 0 from by decide]
  | inr a => rw [hc]; rfl

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)

def frozenIndependent : ∀ I, Independent (laterWeights κ n B) I →
    ∀ i∈I, ∀ j∈I, i≠j → EvenWittColumns.frozenMatrix c (Sum.inl j) i=0 := by
  intros
  rfl

def complex : CochainComplex (ModuleCat ℤ) ℕ :=
  OriginalWittIntegerComplex.complex (EvenWittColumns.frozenMatrix c)
    (Independent (laterWeights κ n B)) (OriginalWittIntegerModel.hereditary κ n B)
    (frozenIndependent κ n B c)

def iso : OriginalWittIntegerModel.complex κ n B hpos hneg hsupport ≅ complex κ n B c :=
  OriginalWittParityComplex.iso (fun a i => B a (Sum.inl i)) (EvenWittColumns.frozenMatrix c)
    (parity κ n B c hm hc) (Independent (laterWeights κ n B))
    (OriginalWittIntegerModel.hereditary κ n B)
    (OriginalWittIntegerModel.independent_entries κ n B hpos hneg hsupport)
    (frozenIndependent κ n B c)

#print axioms parity
#print axioms frozenIndependent
#print axioms complex
#print axioms iso
end Verification.EvenWittOriginalParity
