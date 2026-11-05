/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualOrientations
import Verification.RankedProjectiveClasses
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# Determinant Standard Input

The ordinary determinant identities, stated uniformly for actual
finite projective modules. These are standard multilinear-algebra
inputs, separate from the article's deductions using stable freeness.
Neither a cluster matrix nor stable freeness is part of this interface.
-/
noncomputable section
namespace Verification.DeterminantStandardInput
open CategoryTheory Verification.ActualProjectiveSplitting
open Verification.ProjectiveFreeCoordinates Verification.RankedProjectiveClasses
open scoped MonoidalCategory
variable (R : Type) [CommRing R]

structure Standard where
  freeVolume : ∀ r,(freeBundle R r).object.exteriorPower r ≅ ModuleCat.of R R
  directSum : ∀ (P Q : Bundle R) (r s : ℕ),HasRank P r → HasRank Q s →
    ((sum P Q).object.exteriorPower (r+s) ≅
      MonoidalCategory.tensorObj (P.object.exteriorPower r) (Q.object.exteriorPower s))

variable {R} (S : Standard R) [IsDomain R]

def stabilization (P : Bundle R) {r : ℕ} (hr : HasRank P r) (n : ℕ) :
    (sum P (freeBundle R n)).object.exteriorPower (r+n) ≅ P.object.exteriorPower r :=
  S.directSum P (freeBundle R n) r n hr (freeBundle_rank R n) ≪≫
    MonoidalCategory.tensorIso (Iso.refl (P.object.exteriorPower r)) (S.freeVolume n) ≪≫
    (ρ_ (P.object.exteriorPower r))

#print axioms Standard
#print axioms stabilization
end Verification.DeterminantStandardInput
