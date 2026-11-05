/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinateKoszulClass
import Verification.SchemeGZeroConsequences
import Verification.ExplicitStratumTorus

/-!
# Original G Zero Geometry

All cluster-specific geometric inputs to coherent G-theory: the
actual global ring is noetherian, its selected Koszul parameters are
regular, and its literal coordinate strata have structure-sheaf-generated
G_0. The nonempty closed-stratum class is then proved to vanish globally
on the relevant filtration open, not merely on its principal chart.
-/
noncomputable section
namespace Verification.OriginalGZeroGeometry
open CategoryTheory AlgebraicGeometry
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)

instance global_noetherian : IsNoetherianRing (Global R κ n B) := by
  letI := FrozenGlobalSmooth.global_finitePresentation R κ n B
  exact Algebra.FiniteType.isNoetherianRing R (Global R κ n B)

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)
variable (I : Finset (Fin n)) (hI : Independent (laterWeights κ n B) I)
variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))

include hpos hneg hsupport hI hf in
theorem local_regular : RingTheory.Sequence.IsWeaklyRegular
    (PrimeStratumPresentation.OpenRing (fun i => initial R κ n B (Sum.inl i)) I)
    ((CoordinateKoszulClass.equations (Global R κ n B) (Fin n)
      (fun i => initial R κ n B (Sum.inl i)) I).map (algebraMap (Global R κ n B)
        (PrimeStratumPresentation.OpenRing (fun i => initial R κ n B (Sum.inl i)) I))) := by
  have h := (GlobalRegularParameters.selected_coordinates_regular R κ n B hpos hneg hsupport
    I hI hf (CoordinateKoszulClass.ordered (Fin n) I)
      (CoordinateKoszulClass.ordered_nodup (Fin n) I)).toIsWeaklyRegular
  simpa only [CoordinateKoszulClass.equations,List.map_map,
    IndependentOpenCoordinates.selectedCoordinate,Function.comp_def] using h

variable {G : Scheme → Type*} [∀ X,AddCommGroup (G X)]
variable (T : SchemeGZeroInput.Theory G) (K : SchemeGZeroInput.Koszul T)
variable (ST : SchemeGZeroInput.SplitAffineTorus T)

include hpos hneg hsupport hI hf K in
theorem closed_class_zero (hne : I.Nonempty) :
    T.push (CoordinateClosedImmersion.inclusion (Global R κ n B) (Fin n)
      (fun i => initial R κ n B (Sum.inl i)) I) inferInstance
      (T.unit (CoordinateClosedImmersion.source (Global R κ n B) (Fin n)
        (fun i => initial R κ n B (Sum.inl i)) I))=0 :=
  CoordinateKoszulClass.class_zero (Global R κ n B) (Fin n)
    (fun i => initial R κ n B (Sum.inl i)) I T K
      (local_regular R κ n B hpos hneg hsupport I hI hf) hne

include hpos hneg hsupport hI hf hs ST in
theorem stratum_generated : Function.Surjective (SchemeGZeroConsequences.unitMap T
    (CoordinateClosedImmersion.source (Global R κ n B) (Fin n)
      (fun i => initial R κ n B (Sum.inl i)) I)) := by
  exact SchemeGZeroConsequences.unit_generated_of_iso T
    (ExplicitStratumTorus.schemeIso R κ n I B hf hs hpos hneg hsupport hI)
    (ST.generated R (IndependentChartIndex.Selected n I) (ExplicitStratumTorus.torusRank κ n I B))

include hpos hneg hsupport hI hf hs ST in
theorem stratum_infinite_order : Function.Injective (SchemeGZeroConsequences.unitMap T
    (CoordinateClosedImmersion.source (Global R κ n B) (Fin n)
      (fun i => initial R κ n B (Sum.inl i)) I)) := by
  exact SchemeGZeroConsequences.unit_injective_of_iso T
    (ExplicitStratumTorus.schemeIso R κ n I B hf hs hpos hneg hsupport hI)
    (ST.infinite_order R (IndependentChartIndex.Selected n I) (ExplicitStratumTorus.torusRank κ n I B))

#print axioms global_noetherian
#print axioms local_regular
#print axioms closed_class_zero
#print axioms stratum_generated
#print axioms stratum_infinite_order
end Verification.OriginalGZeroGeometry
