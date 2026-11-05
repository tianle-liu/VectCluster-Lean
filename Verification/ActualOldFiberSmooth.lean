/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualOldTorusSmooth
import Verification.LaurentBasepoint

/-!
# Actual Old Fiber Smooth

The old character fiber is smooth under the actual AS hypotheses.
Its finite presentation is its literal finite character quotient; formal
smoothness descends along the proved u=1 retraction of the actual old torus.
-/
noncomputable section
namespace Verification.ActualOldFiberSmooth
universe u
variable (R A P : Type u) [CommRing R] [CommRing A] [CommRing P]
variable [Algebra R A] [Algebra R P]

theorem formallySmooth_retract (f : P →ₐ[R] A) (s : A →ₐ[R] P)
    (hs : f.comp s = AlgHom.id R A) [Algebra.FormallySmooth R P] :
    Algebra.FormallySmooth R A := by
  constructor
  intro B _ _ I hI g
  let lift := Algebra.FormallySmooth.lift I ⟨2, hI⟩ (g.comp f)
  refine ⟨lift.comp s, ?_⟩
  apply AlgHom.ext
  intro a
  change Ideal.Quotient.mk I (lift (s a)) = g a
  rw [Algebra.FormallySmooth.mk_lift]
  change g (f (s a)) = g a
  exact congrArg g (AlgHom.congr_fun hs a)

variable (ι κ τ : Type u) [Fintype ι] [Fintype κ]
variable (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) (v : ι)
local notation "Old" => LocalTransverseOpen.OldFiber (ActualOpenChart.characters R ι κ τ B) v

theorem old_finitePresentation : Algebra.FinitePresentation R Old := by
  classical
  letI := TorusSmooth.torus_smooth R κ
  exact Algebra.FinitePresentation.quotient
    (Submodule.fg_span (Set.finite_range (fun i : LocalTransverseOpen.Old v =>
      1 + ((ActualOpenChart.characters R ι κ τ B i.val) : ActualOpenChart.Coefficients R κ))))

variable (j : τ → κ)
variable (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0)
variable (hf : Function.Injective (ActualOpenGeometry.columnMap ι κ τ B))
variable (hs : FreezingLattice.Saturated (LinearMap.range (ActualOpenGeometry.columnMap ι κ τ B)))

include j hB hf hs in
theorem old_smooth : Algebra.Smooth R Old := by
  letI := ActualOldTorusSmooth.old_smooth R ι κ τ j B hB v hf hs
  letI := old_finitePresentation R ι κ τ B v
  exact ⟨formallySmooth_retract R Old (LaurentBasepoint.Laurent Old)
    (LaurentBasepoint.atOne R Old) (LaurentBasepoint.coefficient R Old)
    (LaurentBasepoint.atOne_coefficient R Old), inferInstance⟩

set_option synthInstance.maxHeartbeats 100000 in
theorem laurent_smooth [Algebra.Smooth R A] : Algebra.Smooth R (LaurentBasepoint.Laurent A) := by
  letI : Algebra.Smooth A (Polynomial A) := {}
  letI : Algebra.Smooth R (Polynomial A) := Algebra.Smooth.comp R A (Polynomial A)
  letI : Algebra.Smooth (Polynomial A) (LaurentBasepoint.Laurent A) :=
    Algebra.Smooth.of_isLocalization_Away (Polynomial.X : Polynomial A)
  exact Algebra.Smooth.comp R (Polynomial A) (LaurentBasepoint.Laurent A)

#print axioms formallySmooth_retract
#print axioms old_finitePresentation
#print axioms old_smooth
#print axioms laurent_smooth
end Verification.ActualOldFiberSmooth
