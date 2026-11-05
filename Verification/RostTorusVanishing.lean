/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RostAffineInput
import Verification.TorusZero
import Verification.ExplicitStratumTorus

/-!
# Rost Torus Vanishing

The manuscript's affine-times-torus cycle-module acyclicity argument.
It is proved by induction using only ordinary field vanishing, affine
invariance and the separate localization exact sequence. The final theorem
uses the original coordinate-stratum scheme isomorphism.
-/
noncomputable section
namespace Verification.RostTorusVanishing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable (T : RostAffineInput.Theory)

theorem torus_positive (k : Type) [Field k] (n : ℕ) (s : ℤ) (q : ℕ) (hq : 0<q) :
    IsZero ((T.cycles (RostAffineInput.Torus k n) s).homology q) := by
  induction n generalizing s with
  | zero =>
    exact IsZero.of_iso (T.field_positive k s q hq) (T.iso (TorusZero.schemeIso k) s q)
  | succ n ih =>
    have hleft := IsZero.of_iso (ih s) (T.torus_source k n s q)
    have hright := IsZero.of_iso (ih (s-1)) (T.torus_target k n s q)
    have hmiddle := (T.torus_exact k n s q).isZero_X₂ (hleft.eq_of_src _ _) (hright.eq_of_tgt _ _)
    exact IsZero.of_iso hmiddle (T.torus_middle k n s q).symm

theorem affine_torus_positive (k : Type) [Field k] (ι : Type) [Fintype ι]
    (n : ℕ) (s : ℤ) (q : ℕ) (hq : 0<q) :
    IsZero ((T.cycles (Spec (CommRingCat.of (MvPolynomial ι
      (MonoidAlgebra k (Multiplicative (Fin n →₀ ℤ)))))) s).homology q) :=
  IsZero.of_iso (torus_positive T k n s q hq) (T.affine k ι n s q)

open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)
variable (I : Finset (Fin n)) (hI : Independent (laterWeights κ n B) I)
variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))

include hpos hneg hsupport hI hf hs in
theorem original_stratum_positive (s : ℤ) (q : ℕ) (hq : 0<q) :
    IsZero ((T.cycles (Spec (CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n I B))) s).homology q) :=
  IsZero.of_iso (affine_torus_positive T R (IndependentChartIndex.Selected n I)
    (ExplicitStratumTorus.torusRank κ n I B) s q hq)
    (T.iso (ExplicitStratumTorus.schemeIso R κ n I B hf hs hpos hneg hsupport hI) s q)

#print axioms torus_positive
#print axioms affine_torus_positive
#print axioms original_stratum_positive
end Verification.RostTorusVanishing
