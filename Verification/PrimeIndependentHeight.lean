/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimeSchemeFiltration

/-!
# Prime Independent Height

The actual zero-coordinate filtration is exhaustive at independence
height plus one. Its length is the largest allowed zero-set cardinality,
not the total number of mutable vertices.
-/
noncomputable section
namespace Verification.PrimeIndependentHeight
open CategoryTheory AlgebraicGeometry
open Verification.PrimeCoordinateFiltration
variable (V : Type) [Fintype V] [DecidableEq V] (Allowed : Finset V → Prop)

def height : ℕ := by
  classical
  exact (Finset.univ.filter Allowed).sup Finset.card

omit [DecidableEq V] in
theorem card_le_height (I : Finset V) (hI : Allowed I) : I.card ≤ height V Allowed := by
  classical
  exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_univ I,hI⟩)

omit [DecidableEq V] in
theorem height_le_card : height V Allowed ≤ Fintype.card V := by
  classical
  exact Finset.sup_le (fun I _ => Finset.card_le_univ I)

variable (R : Type) [CommRing R] (x : V → R)
variable (hall : ∀ p : PrimeSpectrum R, Allowed (zeroSet x p))

include hall in
theorem stage_exhaustive : stage x (height V Allowed + 1) = ⊤ := by
  ext p
  change p ∈ stage x (height V Allowed + 1) ↔ True
  rw [mem_stage,iff_true]
  exact Nat.lt_succ_of_le (card_le_height V Allowed (zeroSet x p) (hall p))

def exhaustiveIso : (PrimeSchemeFiltration.stages R x).obj (height V Allowed+1) ≅ Spec (CommRingCat.of R) :=
  eqToIso (congrArg Scheme.Opens.toScheme (show PrimeSchemeFiltration.stageOpen R x (height V Allowed+1) = ⊤ from
    stage_exhaustive V Allowed R x hall)) ≪≫ (Spec (CommRingCat.of R)).topIso

#print axioms height
#print axioms card_le_height
#print axioms height_le_card
#print axioms stage_exhaustive
#print axioms exhaustiveIso
end Verification.PrimeIndependentHeight
