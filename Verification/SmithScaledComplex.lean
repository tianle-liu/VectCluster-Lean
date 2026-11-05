/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SmithComplex
import Mathlib.Algebra.Homology.Linear

/-!
# Smith Scaled Complex

Scalar multiplication of an actual differential preserves every chain
isomorphism. Applied to the constructed Smith isomorphism, hA becomes scalar
blocks ha, as an actual complex rather than only a matrix calculation.
-/

noncomputable section
namespace Verification.SmithScaledComplex
open CategoryTheory
open Verification.SmithComplexCoordinates Verification.SmithComplex

variable {R : Type} [CommRing R]

/-- Multiply all differentials by a fixed scalar; objects are unchanged. -/
def scale (a : R) (C : CochainComplex (ModuleCat.{0} R) ℤ) :
    CochainComplex (ModuleCat.{0} R) ℤ where
  X := C.X
  d i j := a • C.d i j
  shape i j h := by rw [C.shape i j h, smul_zero]
  d_comp_d' i j k _ _ := by
    simp only [Linear.smul_comp, Linear.comp_smul, C.d_comp_d, smul_zero]

/-- The unchanged component maps are chain maps for the scaled differentials. -/
def scaleMap (a : R) {C D : CochainComplex (ModuleCat.{0} R) ℤ} (f : C ⟶ D) :
    scale a C ⟶ scale a D where
  f := f.f
  comm' i j _ := by
    change f.f i ≫ (a • D.d i j) = (a • C.d i j) ≫ f.f j
    rw [Linear.comp_smul, Linear.smul_comp, f.comm]

/-- Scaling transports an actual chain isomorphism, without any condition on a. -/
def scaleIso (a : R) {C D : CochainComplex (ModuleCat.{0} R) ℤ} (e : C ≅ D) :
    scale a C ≅ scale a D where
  hom := scaleMap a e.hom
  inv := scaleMap a e.inv
  hom_inv_id := by
    ext n : 1
    exact congrArg (fun f : C ⟶ C => f.f n) e.hom_inv_id
  inv_hom_id := by
    ext n : 1
    exact congrArg (fun f : D ⟶ D => f.f n) e.inv_hom_id

variable [IsDomain R] [IsPrincipalIdealRing R]
variable (C : CochainComplex (ModuleCat.{0} R) ℤ)
variable [∀ n, Module.Free R (C.X n)] [∀ n, Module.Finite R (C.X n)]

/-- Constructed simultaneous scalar-block normal form for a times an arbitrary complex. -/
def scaledSmithIso (a : R) : scale a C ≅ scale a (normalComplex C) :=
  scaleIso a (smithIso C)

theorem scaledNormal_d (a : R) (n : ℤ) :
    (scale a (normalComplex C)).d n (n+1) =
      a • ModuleCat.ofHom (normalDifferential C n) := by
  change a • (normalComplex C).d n (n+1) = _
  rw [normalComplex_d]

/-- The resulting actual chain differential on the ith pair is multiplication by a times a_i. -/
theorem scaledNormal_pair (a : R) (n : ℤ) (i : Fin (boundaryRank C (n+1))) :
    ((scale a (normalComplex C)).d n (n+1)).hom (0,Finsupp.single i 1) =
      (Finsupp.single ((smith C (n+1)).f i) (a * (smith C (n+1)).a i),0) := by
  rw [scaledNormal_d]
  change a • normalDifferential C n (0,Finsupp.single i 1) = _
  rw [normalDifferential_pair]
  simp

#print axioms scale
#print axioms scaleMap
#print axioms scaleIso
#print axioms scaledSmithIso
#print axioms scaledNormal_d
#print axioms scaledNormal_pair

end Verification.SmithScaledComplex
