/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.IndependentBasicOpen

/-!
# Adjacent Chart Localization

Inside a J-chart, inverting the remaining original coordinate v is
exactly the original (J minus v)-chart. The ring equivalence is the unique
localization equivalence and preserves every original global element.
-/
noncomputable section
namespace Verification.AdjacentChartLocalization
open Verification.ExchangeOpenCover
variable {A : Type} [CommRing A] {n : ℕ}
variable (x : Fin n → A) (J : Finset (Fin n)) (v : J)

abbrev Chart := Localization.Away (chartElement x J)
abbrev OpenChart := Localization.Away (algebraMap A (Chart x J) (x v.val))

theorem chartElement_erase : chartElement x (J.erase v.val) = x v.val * chartElement x J := by
  classical
  unfold chartElement
  rw [Finset.compl_erase,Finset.prod_insert]
  exact fun h => (Finset.mem_compl.mp h) v.property

instance localization_erase : IsLocalization.Away (chartElement x (J.erase v.val)) (OpenChart x J v) := by
  rw [chartElement_erase]
  exact IsLocalization.Away.mul (Chart x J) (OpenChart x J v) (chartElement x J) (x v.val)

def equiv : OpenChart x J v ≃ₐ[A] Chart x (J.erase v.val) :=
  IsLocalization.algEquiv (Submonoid.powers (chartElement x (J.erase v.val))) _ _

theorem equiv_coordinate (a : A) : equiv x J v (algebraMap A (OpenChart x J v) a) =
    algebraMap A (Chart x (J.erase v.val)) a := (equiv x J v).commutes a

#print axioms Chart
#print axioms OpenChart
#print axioms chartElement_erase
#print axioms localization_erase
#print axioms equiv
#print axioms equiv_coordinate
end Verification.AdjacentChartLocalization
