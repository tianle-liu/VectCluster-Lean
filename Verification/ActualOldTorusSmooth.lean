/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualTorusFace
import Verification.ActualTransverseSmooth

/-!
# Actual Old Torus Smooth

Smoothness of the actual old torus follows from its actual affine chart.
The coefficient algebra of a finite polynomial algebra is a smooth retract;
its presentation and formal lifts are constructed here.
-/
noncomputable section
namespace Verification.ActualOldTorusSmooth
open MvPolynomial
universe u
variable (R A μ : Type u) [CommRing R] [CommRing A] [Algebra R A]

theorem evaluation_kernel : RingHom.ker (PolynomialSectionIso.zeroEvaluation R A μ).toRingHom =
    Ideal.span (Set.range (fun i : μ => (X i : MvPolynomial μ A))) := by
  apply le_antisymm
  · intro p hp
    let I : Ideal (MvPolynomial μ A) := Ideal.span (Set.range (fun i : μ => (X i : MvPolynomial μ A)))
    have hq : ∀ q : MvPolynomial μ A, Ideal.Quotient.mk I q =
        Ideal.Quotient.mk I (C (PolynomialSectionIso.zeroEvaluation R A μ q)) := by
      intro q
      induction q using MvPolynomial.induction_on with
      | C a => simp [PolynomialSectionIso.zeroEvaluation]
      | add p q hp hq => simp only [map_add, hp, hq]
      | mul_X p i hp =>
          have hx : Ideal.Quotient.mk I (X i) = 0 :=
            Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
          simp only [map_mul, hx, mul_zero]
          simp [PolynomialSectionIso.zeroEvaluation]
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [hq]
    change PolynomialSectionIso.zeroEvaluation R A μ p = 0 at hp
    rw [hp, map_zero, map_zero]
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change PolynomialSectionIso.zeroEvaluation R A μ (X i) = 0
    simp [PolynomialSectionIso.zeroEvaluation]

theorem polynomial_formallySmooth [Algebra.FormallySmooth R (MvPolynomial μ A)] :
    Algebra.FormallySmooth R A := by
  constructor
  intro B _ _ I hI f
  let z := PolynomialSectionIso.zeroEvaluation R A μ
  let g := Algebra.FormallySmooth.lift I ⟨2, hI⟩ (f.comp z)
  refine ⟨g.comp (PolynomialSectionIso.constant R A μ), ?_⟩
  apply AlgHom.ext
  intro a
  change Ideal.Quotient.mk I (g (C a)) = f a
  rw [Algebra.FormallySmooth.mk_lift]
  change f (z (C a)) = f a
  simp [z, PolynomialSectionIso.zeroEvaluation]

theorem polynomial_smooth [Fintype μ] [Algebra.Smooth R (MvPolynomial μ A)] :
    Algebra.Smooth R A := by
  have hz : Function.Surjective (PolynomialSectionIso.zeroEvaluation R A μ) := by
    intro a
    refine ⟨C a, ?_⟩
    exact MvPolynomial.aeval_C _ _
  have hk : (RingHom.ker (PolynomialSectionIso.zeroEvaluation R A μ).toRingHom).FG := by
    rw [evaluation_kernel]
    exact Submodule.fg_span (Set.finite_range _)
  letI : Algebra.FinitePresentation R A := Algebra.FinitePresentation.of_surjective hz hk
  exact ⟨polynomial_formallySmooth R A μ, inferInstance⟩

variable (ι κ τ : Type u) [Fintype ι] [Fintype κ]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
variable (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0) (v : ι)
variable (hf : Function.Injective (ActualOpenGeometry.columnMap ι κ τ B))
variable (hs : FreezingLattice.Saturated (LinearMap.range (ActualOpenGeometry.columnMap ι κ τ B)))

include j hB hf hs in
set_option synthInstance.maxHeartbeats 200000 in
theorem old_smooth : Algebra.Smooth R (ActualTorusFace.OldTorus R ι κ τ B v) := by
  classical
  letI := ActualTransverseSmooth.intermediate_smooth_AS R ι κ τ j B v hB hf hs
  letI : Algebra.Smooth (ActualTransverseSlice.Intermediate R ι κ τ j B v)
      (ActualTransverseLocalization.OpenSource R ι κ τ j B v) :=
    Algebra.Smooth.of_isLocalization_Away (ActualTransverseSlice.originalParameter R ι κ τ j B v)
  letI : Algebra.Smooth R (ActualTransverseLocalization.OpenSource R ι κ τ j B v) :=
    Algebra.Smooth.comp R (ActualTransverseSlice.Intermediate R ι κ τ j B v) _
  letI : Algebra.Smooth R (MvPolynomial (LocalTransverseOpen.Old v)
      (ActualTorusFace.OldTorus R ι κ τ B v)) :=
    Algebra.Smooth.of_equiv (ActualTransverseOpen.affineEquiv R ι κ τ j B hB v)
  exact polynomial_smooth R (ActualTorusFace.OldTorus R ι κ τ B v) (LocalTransverseOpen.Old v)

#print axioms evaluation_kernel
#print axioms polynomial_formallySmooth
#print axioms polynomial_smooth
#print axioms old_smooth
end Verification.ActualOldTorusSmooth
