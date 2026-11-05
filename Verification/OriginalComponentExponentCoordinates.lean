/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalStratumExponentRealization
import Verification.OriginalFreeCoordinateVertex
import Verification.DomainProductComponents

/-!
# Original Component Exponent Coordinates

Exponents indexed by original mutable vertices and actual connected
components. Every function on these labels is realized at every available
free vertex by an actual unit; unused vertices are irrelevant to residues.
-/
noncomputable section
namespace Verification.OriginalComponentExponentCoordinates
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
open Verification.IndependentChartIndex Verification.OriginalFreeTorusCoordinates
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (D : OriginalRetainedProductCoordinates.ProductData R κ n I B)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, FrozenAcyclicCover.earlierWeights κ n B i j = 0 ↔
  FrozenAcyclicCover.laterWeights κ n B i j = 0)
variable (hI : ExchangeOpenCover.Independent (FrozenAcyclicCover.laterWeights κ n B) I)
local notation "A" => GlobalNormalFrame.ZeroLayer R κ n I B
local notation "K" => FreeIndex κ n I B
local notation "V" => Selected n I
local notation "Comp" => ConnectedComponents (PrimeSpectrum A)

def labels : Comp ≃ D.Index :=
  DomainProductComponents.transport
    (fun j => MvPolynomial V (OriginalTorus.Torus (D.Factor j) K))
    (OriginalRetainedProductCoordinates.stratumEquiv R κ n I B D hpos hneg hsupport hI).toRingEquiv

def exponents (u : Aˣ) (i : Fin n) (c : Comp) : ℤ :=
  Function.extend (OriginalFreeCoordinateVertex.vertex κ n I B)
    (fun k => OriginalStratumUnitGeneration.exponentPart R κ n I B D hpos hneg hsupport hI
      u (labels R κ n I B D hpos hneg hsupport hI c) k) (fun _ => 0) i

theorem exponents_at (u : Aˣ) (k : K) (c : Comp) :
    exponents R κ n I B D hpos hneg hsupport hI u (OriginalFreeCoordinateVertex.vertex κ n I B k) c =
      OriginalStratumUnitGeneration.exponentPart R κ n I B D hpos hneg hsupport hI
        u (labels R κ n I B D hpos hneg hsupport hI c) k :=
  (OriginalFreeCoordinateVertex.vertex_injective κ n I B).extend_apply _ _ k

def realize (a : Fin n → Comp → ℤ) : Aˣ :=
  OriginalStratumExponentRealization.realize R κ n I B D hpos hneg hsupport hI
    (fun j => Finsupp.equivFunOnFinite.symm
      (fun k => a (OriginalFreeCoordinateVertex.vertex κ n I B k)
        ((labels R κ n I B D hpos hneg hsupport hI).symm j)))

theorem realize_at (a : Fin n → Comp → ℤ) (k : K) (c : Comp) :
    exponents R κ n I B D hpos hneg hsupport hI
      (realize R κ n I B D hpos hneg hsupport hI a)
      (OriginalFreeCoordinateVertex.vertex κ n I B k) c =
    a (OriginalFreeCoordinateVertex.vertex κ n I B k) c := by
  rw [exponents_at]
  unfold realize
  rw [OriginalStratumExponentRealization.exponent_realize]
  change Finsupp.equivFunOnFinite
    (Finsupp.equivFunOnFinite.symm (fun k => a (OriginalFreeCoordinateVertex.vertex κ n I B k)
      ((labels R κ n I B D hpos hneg hsupport hI).symm
        (labels R κ n I B D hpos hneg hsupport hI c)))) k = _
  rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]

#print axioms labels
#print axioms exponents
#print axioms exponents_at
#print axioms realize
#print axioms realize_at
end Verification.OriginalComponentExponentCoordinates
