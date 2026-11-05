/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StableOrientations
import Verification.ActualEulerOrbits

/-!
# All Bundle Euler Orbits

When K_0 is classified by rank, the orientable quotient is exactly
the set of all actual rank-r bundles. Combining this with the separate
Euler bijection derives the article's unoriented orbit classification.
-/
noncomputable section
namespace Verification.AllBundleEulerOrbits
open CategoryTheory Verification.ActualProjectiveSplitting
variable (R : Type) [CommRing R] [IsDomain R] (r : ℕ)

def forget : ActualEulerOrbits.OrientableClasses R r → RankedProjectiveClasses.Classes R r :=
  Quotient.map (fun P => ⟨P.bundle,P.rank⟩)
    (by intro P Q h; exact ⟨h.some.toLinearEquiv⟩)

omit [IsDomain R] in
theorem forget_injective : Function.Injective (forget R r) := by
  intro P Q
  induction P using Quotient.inductionOn with | _ P =>
    induction Q using Quotient.inductionOn with | _ Q =>
      intro h
      obtain ⟨e⟩ := Quotient.exact h
      exact Quotient.sound ⟨e.toModuleIso⟩

variable (D : DeterminantStandardInput.Standard R)
variable (k : Type) [Field k] [Algebra R k]
variable (hk : Function.Injective (ProjectiveFieldRank.rankMap R k))

include D hk in
theorem forget_surjective : Function.Surjective (forget R r) := by
  intro P
  induction P using Quotient.inductionOn with | _ P =>
    exact ⟨Quotient.mk _ (StableOrientations.of_kzero D k hk P.val P.property),rfl⟩

def allClassesEquiv : ActualEulerOrbits.OrientableClasses R r ≃ RankedProjectiveClasses.Classes R r :=
  Equiv.ofBijective (forget R r) ⟨forget_injective R r,forget_surjective R r D k hk⟩

variable {R r} {H : Type*} [MulAction Rˣ H]
variable (E : ActualOrientations.Classes (R := R) (r := r) ≃ H)
variable (hE : ∀ (u : Rˣ) (P : ActualOrientations.Oriented R r),
  E (Quotient.mk _ (ActualOrientations.changeOrientation u P))=u • E (Quotient.mk _ P))

def classification : RankedProjectiveClasses.Classes R r ≃ Quotient (MulAction.orbitRel Rˣ H) :=
  (allClassesEquiv R r D k hk).symm.trans (ActualEulerOrbits.unorientedEquiv E hE)

#print axioms forget
#print axioms forget_injective
#print axioms forget_surjective
#print axioms allClassesEquiv
#print axioms classification
end Verification.AllBundleEulerOrbits
