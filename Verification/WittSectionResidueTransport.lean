/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.WittSheafLaurentResidue

/-!
# Witt Section Residue Transport

Transport the genuine graded contraction through the ordinary
eta-periodic Witt section comparison, preserving the actual sheaf map.
-/
noncomputable section
namespace Verification.WittSectionResidueTransport
open CategoryTheory AlgebraicGeometry Opposite
open Verification.WittSheafSectionsInput
variable (R : Type) [CommRing R] (W : Scheme.{0}ᵒᵖ ⥤ CommRingCat.{0})
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (E : Comparison R W site N) (K : StandardThomContractionNormalization.Grading R site N)
variable (S : Type) [CommRing S] [Algebra R S] (hs : Algebra.Smooth R S)

theorem degreeCast (q q' : ℤ) (h : q=q') (a : RingSection W S) :
    StandardThomContractionNormalization.degreeCast site N S q q' h (E.sections S hs q a) =
      E.sections S hs q' a := by
  subst q'
  rfl

theorem residue (q : ℤ) (a : RingSection W (LaurentBasepoint.Laurent S)) :
    SheafGradedLaurentResidue.degreeResidue R S site N K hs q
      (E.sections (LaurentBasepoint.Laurent S) (WittSheafLaurentResidue.laurentSmooth R S hs) q a) =
      E.sections S hs (q-1) (WittSheafLaurentResidue.residue R W site N E K S hs q a) := by
  exact ((E.sections S hs (q-1)).apply_symm_apply _).symm

variable {U : Type} [CommRing U] [Algebra R U] (hu : Algebra.Smooth R U)
variable (f : U →ₐ[R] LaurentBasepoint.Laurent S)

theorem pullback_residue (q : ℤ) (a : RingSection W U) :
    SheafGradedLaurentResidue.degreeResidue R S site N K hs q
      (ActualSheafContractionRestriction.pullback site (N q) f.toRingHom (E.sections U hu q a)) =
      E.sections S hs (q-1)
        (WittSheafLaurentResidue.residue R W site N E K S hs q (pullback W f.toRingHom a)) := by
  exact (congrArg (SheafGradedLaurentResidue.degreeResidue R S site N K hs q)
    (E.natural U (LaurentBasepoint.Laurent S) hu (WittSheafLaurentResidue.laurentSmooth R S hs) f q a).symm).trans
      (residue R W site N E K S hs q _)

#print axioms degreeCast
#print axioms residue
#print axioms pullback_residue
end Verification.WittSectionResidueTransport
