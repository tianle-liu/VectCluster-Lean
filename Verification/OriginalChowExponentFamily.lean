/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalComponentExponentCoordinates
import Verification.AllowedComponentRow

/-!
# Original Chow Exponent Family

Simultaneous realization of every allowed flag exponent by actual
units of the predecessor strata. The combinatorial extension and the
algebraic units are both constructed internally.
-/
noncomputable section
namespace Verification.OriginalChowExponentFamily
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
open Verification.IndependentChartIndex Verification.FrozenAcyclicCover
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
local notation "Allowed" => ExchangeOpenCover.Independent (laterWeights κ n B)

def hereditary (J : Finset (Fin n)) (hJ : ExchangeOpenCover.Independent (laterWeights κ n B) J)
    (v : J) : ExchangeOpenCover.Independent (laterWeights κ n B) (J.erase v.val) :=
  fun a ha b hb => hJ a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)

abbrev Components (I : Finset (Fin n)) :=
  ConnectedComponents (PrimeSpectrum (GlobalNormalFrame.ZeroLayer R κ n I B))

variable (p : ℕ)
local notation "Source" => AllowedComponentRow.Source Allowed p
local notation "Target" => AllowedComponentRow.Target Allowed p
local notation "pred" => AllowedComponentRow.predecessor Allowed (hereditary κ n B) p
abbrev componentFamily (I : Source) := Components R κ n B I.val
local notation "P" => componentFamily R κ n B p
local notation "SI" => AllowedComponentRow.SourceIndex Allowed p P
abbrev FlagValues := ∀ J : Target, ∀ v : J.val, Components R κ n B ((pred J v).val) → ℤ
local notation "Flags" => FlagValues R κ n B p
variable (D : ∀ I : AllowedComponentRow.Source (ExchangeOpenCover.Independent (laterWeights κ n B)) p,
  OriginalRetainedProductCoordinates.ProductData R κ n I.val B)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)

def realize (x : SI → ℤ) : ∀ I : Source, Additive (GlobalNormalFrame.ZeroLayer R κ n I.val B)ˣ :=
  fun I => Additive.ofMul (OriginalComponentExponentCoordinates.realize R κ n I.val B (D I)
    hpos hneg hsupport I.property.2 (fun i c => x ⟨I,(i,c)⟩))

def flags (u : ∀ I : Source, Additive (GlobalNormalFrame.ZeroLayer R κ n I.val B)ˣ) : Flags :=
  fun J v c => OriginalComponentExponentCoordinates.exponents R κ n (pred J v).val B (D (pred J v))
    hpos hneg hsupport (pred J v).property.2 (Additive.toMul (u (pred J v))) v.val c

theorem realize_flags (x : SI → ℤ) :
    flags R κ n B p D hpos hneg hsupport (realize R κ n B p D hpos hneg hsupport x) =
      AllowedComponentRow.restriction Allowed (hereditary κ n B) p P x := by
  funext J v c
  let k := OriginalFreeBoundaryIndex.boundary κ n J.val B v hpos hneg hsupport J.property.2
  have h := OriginalComponentExponentCoordinates.realize_at R κ n (pred J v).val B (D (pred J v))
    hpos hneg hsupport (pred J v).property.2
    (fun i c => x ⟨pred J v,(i,c)⟩) k c
  exact h

theorem flags_surjective : Function.Surjective (flags R κ n B p D hpos hneg hsupport) := by
  intro y
  obtain ⟨x,hx⟩ := AllowedComponentRow.restriction_surjective Allowed (hereditary κ n B) p P y
  exact ⟨realize R κ n B p D hpos hneg hsupport x,
    (realize_flags R κ n B p D hpos hneg hsupport x).trans hx⟩

#print axioms hereditary
#print axioms Components
#print axioms componentFamily
#print axioms FlagValues
#print axioms realize
#print axioms flags
#print axioms realize_flags
#print axioms flags_surjective
end Verification.OriginalChowExponentFamily
