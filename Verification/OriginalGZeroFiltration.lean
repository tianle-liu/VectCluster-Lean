/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalGZeroGeometry
import Verification.CoordinateLayerRestriction
import Verification.CoordinateEmptyLayer
import Verification.PrimeIndependentHeight

/-!
# Original G Zero Filtration

The original anticlique filtration computes actual coherent G_0.
All closed-stratum pushforwards vanish by the constructed global Koszul
application, so every restriction is bijective. The initial torus and
the exhaustion then identify the structure-sheaf generator globally.
-/
noncomputable section
namespace Verification.OriginalGZeroFiltration
open CategoryTheory AlgebraicGeometry
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
open Verification.SchemeGZeroConsequences
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)
variable (hf : ∀ I,Independent (laterWeights κ n B) I → Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : ∀ I,Independent (laterWeights κ n B) I → FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))
variable {G : Scheme → Type*} [∀ X,AddCommGroup (G X)]
variable (T : SchemeGZeroInput.Theory G) (K : SchemeGZeroInput.Koszul T)
variable (ST : SchemeGZeroInput.SplitAffineTorus T) (L : SchemeGZeroInput.Localization T)

abbrev stage (r : ℕ) := (PrimeSchemeFiltration.stageOpen (Global R κ n B)
  (fun i => initial R κ n B (Sum.inl i)) (r+1)).toScheme

def step (r : ℕ) : stage R κ n B r ⟶ stage R κ n B (r+1) :=
  CoordinateLayerRestriction.inclusion (Global R κ n B) (Fin n)
    (fun i => initial R κ n B (Sum.inl i)) (r+1)

instance step_open (r : ℕ) : IsOpenImmersion (step R κ n B r) :=
  inferInstanceAs (IsOpenImmersion (CoordinateLayerRestriction.inclusion (Global R κ n B)
    (Fin n) (fun i => initial R κ n B (Sum.inl i)) (r+1)))

abbrev Index (r : ℕ) := PrimeLayerCover.Index (Independent (laterWeights κ n B)) (r+1)

include hpos hneg hsupport hf K in
theorem layer_class_zero (r : ℕ) (i : Index κ n B r) :
    T.push (CoordinateClosedLayer.inclusion (Global R κ n B) (Fin n)
      (fun i => initial R κ n B (Sum.inl i)) (Independent (laterWeights κ n B)) (r+1) i)
      inferInstance (T.unit (CoordinateClosedImmersion.source (Global R κ n B) (Fin n)
        (fun i => initial R κ n B (Sum.inl i)) i.val))=0 := by
  let x := fun j => initial R κ n B (Sum.inl j)
  have hr := OriginalGZeroGeometry.local_regular R κ n B hpos hneg hsupport i.val i.property.2 (hf i.val i.property.2)
  have hc : PrimeSchemeFiltration.stageOpen (Global R κ n B) x (r+1+1) ≤
      PrimeSpectrum.basicOpen (∏ j∈i.valᶜ,x j) ⊔
        ⨆ b : {b : Global R κ n B // b∈CoordinateKoszulClass.equations (Global R κ n B) (Fin n) x i.val},
          PrimeSpectrum.basicOpen b.val := by
    simpa only [CoordinateClosedImmersion.ambient,i.property.1] using
      CoordinateKoszulClass.cover (Global R κ n B) (Fin n) x i.val
  have h := K.resolution_class (Global R κ n B)
    (PrimeSchemeFiltration.stageOpen (Global R κ n B) x (r+1+1))
    (∏ j∈i.valᶜ,x j) (CoordinateKoszulClass.equations (Global R κ n B) (Fin n) x i.val)
    hr hc (CoordinateClosedImmersion.source (Global R κ n B) (Fin n) x i.val)
    (CoordinateClosedLayer.inclusion (Global R κ n B) (Fin n) x
      (Independent (laterWeights κ n B)) (r+1) i) inferInstance
    (CoordinateKoszulClass.quotientIso (Global R κ n B) (Fin n) x i.val)
    ((CoordinateClosedLayer.inclusion_fac (Global R κ n B) (Fin n) x
      (Independent (laterWeights κ n B)) (r+1) i).trans
      (CoordinateKoszulClass.quotientIso_fac (Global R κ n B) (Fin n) x i.val).symm)
  rw [CoordinateKoszulClass.length_equations,i.property.1] at h
  exact h.trans (StableFree.koszul_class_zero (r+1) (Nat.succ_ne_zero r) _)

include hpos hneg hsupport hf hs K ST L in
theorem restriction_bijective (r : ℕ) : Function.Bijective (T.restrict (step R κ n B r) inferInstance) := by
  classical
  letI : Fintype (Index κ n B r) := Fintype.ofFinite _
  let x := fun j => initial R κ n B (Sum.inl j)
  exact SchemeGZeroConsequences.restriction_bijective T L (step R κ n B r) inferInstance
    (Index κ n B r) (fun i => CoordinateClosedImmersion.source (Global R κ n B) (Fin n) x i.val)
    (CoordinateClosedLayer.inclusion (Global R κ n B) (Fin n) x (Independent (laterWeights κ n B)) (r+1))
    (fun _ => inferInstance)
    (CoordinateClosedLayer.disjoint (Global R κ n B) (Fin n) x (Independent (laterWeights κ n B)) (r+1))
    (CoordinateLayerRestriction.complement (Global R κ n B) (Fin n) x (r+1)
      (Independent (laterWeights κ n B))
      (PrimeCoordinateFiltration.actual_zeroSet_independent R κ n B hpos hneg hsupport))
    (fun i => OriginalGZeroGeometry.stratum_generated R κ n B hpos hneg hsupport i.val i.property.2
      (hf i.val i.property.2) (hs i.val i.property.2) T ST)
    (layer_class_zero R κ n B hpos hneg hsupport hf T K r)

include hpos hneg hsupport hf hs ST in
theorem base_unit_bijective : Function.Bijective (unitMap T (stage R κ n B 0)) := by
  have he : Independent (laterWeights κ n B) ∅ := by simp [Independent]
  let e := (CoordinateEmptyLayer.stratumIso (Global R κ n B) (Fin n)
    (fun i => initial R κ n B (Sum.inl i))).symm
  exact ⟨unit_injective_of_iso T e
      (OriginalGZeroGeometry.stratum_infinite_order R κ n B hpos hneg hsupport ∅ he (hf ∅ he) (hs ∅ he) T ST),
    unit_generated_of_iso T e
      (OriginalGZeroGeometry.stratum_generated R κ n B hpos hneg hsupport ∅ he (hf ∅ he) (hs ∅ he) T ST)⟩

include hpos hneg hsupport hf hs K ST L in
theorem unit_bijective : ∀ r,Function.Bijective (unitMap T (stage R κ n B r)) := by
  intro r
  induction r with
  | zero => exact base_unit_bijective R κ n B hpos hneg hsupport hf hs T ST
  | succ r ih =>
    exact unit_bijective_of_restriction T (step R κ n B r) inferInstance
      (restriction_bijective R κ n B hpos hneg hsupport hf hs T K ST L r) ih

include hpos hneg hsupport hf hs K ST L in
theorem global_unit_bijective : Function.Bijective (unitMap T (Spec (CommRingCat.of (Global R κ n B)))) := by
  let e := PrimeIndependentHeight.exhaustiveIso (Fin n) (Independent (laterWeights κ n B))
    (Global R κ n B) (fun i => initial R κ n B (Sum.inl i))
      (PrimeCoordinateFiltration.actual_zeroSet_independent R κ n B hpos hneg hsupport)
  have h := unit_bijective R κ n B hpos hneg hsupport hf hs T K ST L
    (PrimeIndependentHeight.height (Fin n) (Independent (laterWeights κ n B)))
  exact ⟨unit_injective_of_iso T e.symm h.1,unit_generated_of_iso T e.symm h.2⟩

#print axioms stage
#print axioms step
#print axioms step_open
#print axioms Index
#print axioms layer_class_zero
#print axioms restriction_bijective
#print axioms base_unit_bijective
#print axioms unit_bijective
#print axioms global_unit_bijective
end Verification.OriginalGZeroFiltration
