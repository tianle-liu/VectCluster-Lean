/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictCohomologicalDimension
import Verification.OriginalDivisorGeometry
import Verification.GlobalExchangeSmooth

/-!
# Original Framed Nisnevich

The four framed localization terms and their dimension consequences
on the actual original seed. Smoothness of the whole ring and divisor,
regularity of x_v, and its conormal frame are constructed from AS.
-/
noncomputable section
namespace Verification.OriginalFramedNisnevich
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.FrozenAcyclicCover Verification.ActualFreezingDivisor
open Verification.StrictCohomologicalDimension
universe u
variable {M : Type u} (T : StrictNisnevichInput.Theory M)
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ)
variable (P : StrictPrincipalLongExact.Standard T R)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)
variable (hall : ∀ I : Finset (Fin n), ExchangeOpenCover.Independent (laterWeights κ n B) I →
  AnticliqueSubcolumns.AS (fun a i => B a (Sum.inl i)) I)

include hpos hneg hsupport hall in
theorem smooth : Algebra.Smooth R (Global R κ n B) :=
  GlobalExchangeSmooth.global_smooth_saturated R κ n B hpos hneg hsupport
    (fun I hI => ((GlobalSelectedColumns.AS_iff κ n B I).mpr (hall I hI)).1)
    (fun I hI => ((GlobalSelectedColumns.AS_iff κ n B I).mpr (hall I hI)).2)

def sequence (v : Fin n) (F : M) (q : ℕ) :
    StrictPrincipalLongExact.FourTerm T (Global R κ n B) (initial R κ n B (Sum.inl v)) F q := by
  letI := smooth R κ n B hpos hneg hsupport hall
  exact P.sequence (Global R κ n B) (initial R κ n B (Sum.inl v))
    (OriginalDivisorGeometry.coordinate_regular R κ n B hpos hneg hsupport hall v)
    (OriginalDivisorGeometry.divisor_smooth R κ n B hpos hneg hsupport hall v) F q

include P hpos hneg hsupport hall in
theorem dimension_bound (v : Fin n) (du dc : ℕ)
    (hu : Bound T (Localization.Away (initial R κ n B (Sum.inl v))) du)
    (hc : Bound T (Divisor R κ n B v) dc) :
    Bound T (Global R κ n B) (max du (dc+1)) := by
  letI := smooth R κ n B hpos hneg hsupport hall
  exact principal_bound T R P (Global R κ n B) (initial R κ n B (Sum.inl v))
    (OriginalDivisorGeometry.coordinate_regular R κ n B hpos hneg hsupport hall v)
    (OriginalDivisorGeometry.divisor_smooth R κ n B hpos hneg hsupport hall v) du dc hu hc

include P hpos hneg hsupport hall in
theorem freezing_bound_one (v : Fin n)
    (hu : Bound T (Localization.Away (initial R κ n B (Sum.inl v))) 1)
    (hc : Bound T (Divisor R κ n B v) 0) : Bound T (Global R κ n B) 1 :=
  dimension_bound T R κ n P B hpos hneg hsupport hall v 1 0 hu hc

include P hpos hneg hsupport hall in
theorem restriction_isIso (v : Fin n) (hc : Bound T (Divisor R κ n B v) 0)
    (F : M) (q : ℕ) (hq : 0 < q) :
    IsIso (sequence T R κ n P B hpos hneg hsupport hall v F q).restriction := by
  letI := smooth R κ n B hpos hneg hsupport hall
  exact StrictCohomologicalDimension.restriction_isIso T R P
    (Global R κ n B) (initial R κ n B (Sum.inl v))
    (OriginalDivisorGeometry.coordinate_regular R κ n B hpos hneg hsupport hall v)
    (OriginalDivisorGeometry.divisor_smooth R κ n B hpos hneg hsupport hall v) hc F q hq

#print axioms smooth
#print axioms sequence
#print axioms dimension_bound
#print axioms freezing_bound_one
#print axioms restriction_isIso
end Verification.OriginalFramedNisnevich
