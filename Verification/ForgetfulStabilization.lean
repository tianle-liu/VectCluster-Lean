/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AllBundleEulerOrbits
import Verification.OrientedLineStabilization

/-!
# Forgetful Stabilization

Injectivity of oriented stabilization implies injectivity after
forgetting orientation when K_0 is classified by rank. The discrepancy
between determinant orientations is internally accounted for by an
actual unit, using compatibility of stabilization with unit changes.
-/
noncomputable section
namespace Verification.ForgetfulStabilization
open CategoryTheory Verification.ActualOrientations
open Verification.OrientedLineStabilization
variable {R : Type} [CommRing R] [IsDomain R]
variable (D : DeterminantStandardInput.Standard R) (N : Naturality D)
variable (k : Type) [Field k] [Algebra R k]
variable (hk : Function.Injective (ProjectiveFieldRank.rankMap R k))

include D N hk in
theorem injective {r : ℕ} (hi : Function.Injective (advance D N r)) :
    Function.Injective (RankedProjectiveClasses.stabilize R r) := by
  intro P Q
  induction P using Quotient.inductionOn with | _ P =>
    induction Q using Quotient.inductionOn with | _ Q =>
      intro h
      obtain ⟨eplus⟩ := Quotient.exact h
      let OP := StableOrientations.of_kzero D k hk P.val P.property
      let OQ := StableOrientations.of_kzero D k hk Q.val Q.property
      have he : Nonempty ((stepObject D OP).bundle.object ≅ (stepObject D OQ).bundle.object) :=
        ⟨eplus.toModuleIso⟩
      obtain ⟨u,hu⟩ := (underlying_iff_unit (stepObject D OP) (stepObject D OQ)).mp he
      have hp := equivalent_trans (step_change D u OP) hu
      have heq : (Quotient.mk _ (changeOrientation u OP) : Classes (R := R) (r := r))=
          Quotient.mk _ OQ := hi (Quotient.sound hp)
      obtain ⟨e,_⟩ := Quotient.exact heq
      exact Quotient.sound ⟨e.toLinearEquiv⟩

#print axioms injective
end Verification.ForgetfulStabilization
