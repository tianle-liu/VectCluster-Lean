/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OrientedLineStabilization
import Verification.PostnikovEulerClassification

/-!
# Postnikov Stabilization

The relative Postnikov argument for stabilization. Standard
representability, convergence and individual obstruction groups are
explicit uniform inputs. Bijectivity above the cohomological dimension
is deduced, for the actual oriented-module stabilization map.
-/
noncomputable section
universe v
namespace Verification.PostnikovStabilization
open CategoryTheory CategoryTheory.Limits
variable {R : Type} [CommRing R] [IsDomain R]
variable (D : DeterminantStandardInput.Standard R) (N : OrientedLineStabilization.Naturality D)
variable (C : Type*) (cochains : C → CochainComplex AddCommGrp.{v} ℕ)

def Above (h : ℕ) : Prop := ∀ (M : C) (q : ℕ),h<q → IsZero ((cochains M).homology q)

structure StandardStages (r : ℕ) where
  tower : PostnikovTowerLimit.Tower
  convergence : ActualOrientations.Classes (R := R) (r := r) ≃ PostnikovTowerLimit.Sections tower
  firstStage : tower.stage 0 ≃ ActualOrientations.Classes (R := R) (r := r+1)
  projection : ∀ P,firstStage ((convergence P).val 0)=OrientedLineStabilization.advance D N r P
  existence : ∀ n,(∀ M : C,IsZero ((cochains M).homology (r+n+1))) →
    Function.Surjective (tower.transition n)
  uniqueness : ∀ n,(∀ M : C,IsZero ((cochains M).homology (r+n))) →
    Function.Injective (tower.transition n)

variable {D N C cochains} {r h : ℕ}
variable (S : StandardStages D N C cochains r) (hc : Above C cochains h) (hr : h<r)

include hc hr in
theorem steps_bijective (n : ℕ) : Function.Bijective (S.tower.transition n) :=
  ⟨S.uniqueness n (fun M => hc M (r+n) (by omega)),
   S.existence n (fun M => hc M (r+n+1) (by omega))⟩

def equivalence : ActualOrientations.Classes (R := R) (r := r) ≃
    ActualOrientations.Classes (R := R) (r := r+1) :=
  S.convergence.trans ((PostnikovTowerLimit.equivalence S.tower (steps_bijective S hc hr)).trans
    S.firstStage)

theorem equivalence_apply (P : ActualOrientations.Classes (R := R) (r := r)) :
    equivalence S hc hr P=OrientedLineStabilization.advance D N r P := S.projection P

include S hc hr in
theorem advance_bijective : Function.Bijective (OrientedLineStabilization.advance D N r) := by
  have he : (equivalence S hc hr : _ → _)=OrientedLineStabilization.advance D N r :=
    funext (equivalence_apply S hc hr)
  rw [←he]
  exact (equivalence S hc hr).bijective

#print axioms Above
#print axioms StandardStages
#print axioms steps_bijective
#print axioms equivalence
#print axioms equivalence_apply
#print axioms advance_bijective
end Verification.PostnikovStabilization
