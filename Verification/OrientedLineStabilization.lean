/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StableOrientations

/-!
# Oriented Line Stabilization

Stabilization of genuine determinant-oriented modules. The sole
naturality input is the ordinary determinant direct-sum isomorphism's
naturality under module isomorphisms. Its consequences for quotient
classes and unit changes are proved here.
-/
noncomputable section
namespace Verification.OrientedLineStabilization
open CategoryTheory Verification.ActualProjectiveSplitting
open Verification.ProjectiveFreeCoordinates Verification.ActualOrientations
open scoped MonoidalCategory
variable {R : Type} [CommRing R] [IsDomain R]
variable (D : DeterminantStandardInput.Standard R)

def sumIso {P Q : Bundle R} (e : P.object ≅ Q.object) :
    (sum P line).object ≅ (sum Q line).object :=
  (e.toLinearEquiv.prodCongr (LinearEquiv.refl R R)).toModuleIso

def lineDet (P : Bundle R) {r : ℕ} (hr : HasRank P r) :
    (sum P line).object.exteriorPower (r+1) ≅ P.object.exteriorPower r :=
  D.directSum P line r 1 hr line_rank ≪≫
    MonoidalCategory.tensorIso (Iso.refl (P.object.exteriorPower r))
      (ModuleCat.exteriorPower.iso₁ (line (R := R)).object) ≪≫
    (ρ_ (P.object.exteriorPower r))

structure Naturality : Prop where
  line : ∀ (P Q : Bundle R) (r : ℕ) (hr : HasRank P r) (hq : HasRank Q r)
    (e : P.object ≅ Q.object),
    (ModuleCat.exteriorPower.functor R (r+1)).map (sumIso e).hom ≫ (lineDet D Q hq).hom=
      (lineDet D P hr).hom ≫ (ModuleCat.exteriorPower.functor R r).map e.hom

def stepObject {r : ℕ} (P : Oriented R r) : Oriented R (r+1) where
  bundle := sum P.bundle line
  rank := sum_rank P.rank line_rank
  orientation := lineDet D P.bundle P.rank ≪≫ P.orientation

variable (N : Naturality D)

include N in
theorem step_compatible {r : ℕ} {P Q : Oriented R r} (h : Equivalent P Q) :
    Equivalent (stepObject D P) (stepObject D Q) := by
  obtain ⟨e,he⟩ := h
  refine ⟨sumIso e,?_⟩
  change (ModuleCat.exteriorPower.functor R (r+1)).map (sumIso e).hom ≫
    ((lineDet D Q.bundle Q.rank).hom ≫ Q.orientation.hom)=
    (lineDet D P.bundle P.rank).hom ≫ P.orientation.hom
  rw [←Category.assoc,N.line,Category.assoc,he]

def advance (r : ℕ) : Classes (R := R) (r := r) → Classes (R := R) (r := r+1) :=
  Quotient.map (stepObject D) (fun _ _ h => step_compatible D N h)

theorem step_change {r : ℕ} (u : Rˣ) (P : Oriented R r) :
    Equivalent (stepObject D (changeOrientation u P)) (changeOrientation u (stepObject D P)) := by
  refine ⟨Iso.refl _,?_⟩
  change (ModuleCat.exteriorPower.functor R (r+1)).map (𝟙 _) ≫
    (((lineDet D P.bundle P.rank).hom ≫ P.orientation.hom) ≫
      (ModuleUnitAutomorphisms.multiplication R u).hom)=
    (lineDet D P.bundle P.rank).hom ≫
      (P.orientation.hom ≫ (ModuleUnitAutomorphisms.multiplication R u).hom)
  rw [CategoryTheory.Functor.map_id,Category.id_comp,Category.assoc]

#print axioms sumIso
#print axioms lineDet
#print axioms Naturality
#print axioms stepObject
#print axioms step_compatible
#print axioms advance
#print axioms step_change
end Verification.OrientedLineStabilization
