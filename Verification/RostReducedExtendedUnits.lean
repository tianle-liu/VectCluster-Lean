/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RostReducedDivisorResidues

/-!
# Rost Reduced Extended Units

Zero residue for every genuinely extended unit on a reduced principal
boundary, derived using the actual branch DVR normalization.
-/
noncomputable section
namespace Verification.RostReducedExtendedUnits
open Verification.RostCanonicalCoefficients
open Verification.RostPrincipalLocalizationInput (OpenRing ClosedRing)
open Verification.RostPrincipalResidueInput
open Verification.ReducedBoundaryBranchOrder
variable (T : RostAffineInput.Theory) (P : RostPrincipalLocalizationInput.Theory T)
variable (F : RostFiniteProducts.Standard T) (Z : RostWeightZero.IntegralConvention T)
variable (E : GenericZeroEvaluation T F Z) (U : OriginalRostUnitTerms.UnitsConvention T)
variable (N : Normalization T P F Z E U)
variable (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.Smooth k A]
variable (t : A) (ht : IsRegular t) [Algebra.Smooth k (OpenRing A t)]
variable [IsNoetherianRing A]
variable {J : Type} (D : J → Type) [∀ j, CommRing (D j)] [∀ j, IsDomain (D j)]
variable (e : ClosedRing A t ≃+* ∀ j, D j) (j : J)

include N in
theorem extended (u : (OpenRing A t)ˣ) (w : Aˣ)
    (h : (u : OpenRing A t) = algebraMap A (OpenRing A t) w) :
    RostReducedDivisorResidues.residue T P F Z E U k A t ht D e j (Additive.ofMul u) = 0 := by
  apply RostReducedDivisorResidues.not_mem T P F Z E U N k A t ht D e j u w h
  change projection A t D e j (w : A) ≠ 0
  exact (w.isUnit.map (projection A t D e j)).ne_zero

include N in
theorem extended_map (w : Aˣ) :
    RostReducedDivisorResidues.residue T P F Z E U k A t ht D e j
      (Additive.ofMul (Units.map (algebraMap A (OpenRing A t)).toMonoidHom w)) = 0 :=
  extended T P F Z E U N k A t ht D e j _ w rfl

include N in
theorem extended_selector (a : A) (ha : a * a = a) (w : Aˣ) :
    RostReducedDivisorResidues.residue T P F Z E U k A t ht D e j
      (Additive.ofMul (Units.map (algebraMap A (OpenRing A t)).toMonoidHom
        (BoundaryComponentSelector.unit a ha w))) = 0 :=
  extended_map T P F Z E U N k A t ht D e j _

#print axioms extended
#print axioms extended_map
#print axioms extended_selector
end Verification.RostReducedExtendedUnits
