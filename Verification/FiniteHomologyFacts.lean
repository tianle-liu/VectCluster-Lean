/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedHomologyTF
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Finite Homology Facts

Elementary finiteness and endpoint TF facts for the actual categorical
homology of finite complexes. These are used after the verified graph-cover
cancellation, not substituted for the cancellation.
-/

namespace Verification.FiniteHomologyFacts

open CategoryTheory Verification.GradedHomologyTF Verification.GradedPerturbation

variable {R : Type*} [CommRing R]

/-- Finite modules over a noetherian ring have finite short-complex homology. -/
theorem short_homology_finite [IsNoetherianRing R] (S : ShortComplex (ModuleCat R))
    [Module.Finite R S.X₂] : Module.Finite R S.homology := by
  letI : Module.Finite R S.moduleCatHomology := inferInstance
  exact Module.Finite.equiv S.moduleCatHomologyIso.symm.toLinearEquiv

/-- With zero incoming differential the homology embeds in the torsion-free middle module. -/
theorem short_homology_tf_of_zero_f (S : ShortComplex (ModuleCat R))
    [NoZeroSMulDivisors R S.X₂] (hf : S.f=0) : NoZeroSMulDivisors R S.homology := by
  apply shortComplex_tf_of_boundaries S
  intro a ha x _ hax
  obtain ⟨y,hy⟩ := hax
  have hx : a • x=0 := by
    rw [hf] at hy
    exact hy.symm
  have he : x=0 := (eq_zero_or_eq_zero_of_smul_eq_zero hx).resolve_left ha
  exact ⟨0,by rw [map_zero,he]⟩

/-- A vanished incoming degree leaves torsion-free homology. -/
theorem homology_tf_of_no_incoming (K : CochainComplex (ModuleCat R) ℤ) (p : ℤ)
    [Subsingleton (K.X (p-1))] [NoZeroSMulDivisors R (K.X p)] :
    NoZeroSMulDivisors R (K.homology p) := by
  let S := K.sc' (p-1) p (p+1)
  letI : NoZeroSMulDivisors R S.X₂ := inferInstanceAs (NoZeroSMulDivisors R (K.X p))
  letI : Subsingleton S.X₁ := inferInstanceAs (Subsingleton (K.X (p-1)))
  have hs : NoZeroSMulDivisors R S.homology := by
    apply short_homology_tf_of_zero_f S
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    rw [Subsingleton.elim y 0,map_zero]
    rfl
  letI := hs
  let e := (K.homologyIsoSc' (p-1) p (p+1) (by simp) (by simp)).toLinearEquiv
  exact Function.Injective.noZeroSMulDivisors e e.injective e.map_zero e.map_smul

/-- A vanished middle degree has torsion-free (indeed zero) homology. -/
theorem homology_tf_of_zero_at (K : CochainComplex (ModuleCat R) ℤ) (p : ℤ)
    [Subsingleton (K.X p)] : NoZeroSMulDivisors R (K.homology p) := by
  let S := K.sc' (p-1) p (p+1)
  letI : Subsingleton S.X₂ := inferInstanceAs (Subsingleton (K.X p))
  have hs : NoZeroSMulDivisors R S.homology := by
    apply shortComplex_tf_of_boundaries S
    intro _ _ x _ _
    exact ⟨0,by rw [map_zero]; exact Subsingleton.elim _ _⟩
  letI := hs
  let e := (K.homologyIsoSc' (p-1) p (p+1) (by simp) (by simp)).toLinearEquiv
  exact Function.Injective.noZeroSMulDivisors e e.injective e.map_zero e.map_smul

/-- Finite homogeneous matrix coordinates give finite actual homology in every degree. -/
theorem matrix_homology_finite [IsNoetherianRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (deg : ι → ℤ) (D : Matrix ι ι R) (hd : Homogeneous deg 1 D) (hsq : D*D=0) (p : ℤ) :
    Module.Finite R ((matrixComplex deg D hd hsq).homology p) := by
  let K := matrixComplex deg D hd hsq
  let S := K.sc' (p-1) p (p+1)
  letI : Module.Finite R S.X₂ := inferInstanceAs (Module.Finite R (degreeModule (R := R) deg p))
  letI := short_homology_finite S
  exact Module.Finite.equiv (K.homologyIsoSc' (p-1) p (p+1) (by simp) (by simp)).symm.toLinearEquiv

#print axioms short_homology_finite
#print axioms short_homology_tf_of_zero_f
#print axioms homology_tf_of_no_incoming
#print axioms homology_tf_of_zero_at
#print axioms matrix_homology_finite

end Verification.FiniteHomologyFacts
