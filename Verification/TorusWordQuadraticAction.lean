/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.TorusModelWordBasis

/-!
# Torus Word Quadratic Action

The genuine ordered torus word coordinates respect the ordinary
quadratic Thom scalar and all of its powers.
-/
noncomputable section
namespace Verification.TorusWordQuadraticAction
open CategoryTheory AlgebraicGeometry
open Verification.BinaryWordCoordinates Verification.TorusModelWordBasis
variable (R S μ : Type) [CommRing R] [CommRing S] [Algebra R S]
variable [Fintype μ] [LinearOrder μ]
variable (e : S ≃ₐ[R] OriginalTorus.Torus R μ)
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : GradedMilnorWittSheaf.Standard site N)
variable (K : StandardThomContractionNormalization.Grading R site N)
variable (P : GradedMilnorWittLaurent.Standard R site N D K)
local notation "DR" => D.symbols (CommRingCat.of R)
local notation "DS" => D.symbols (CommRingCat.of S)
include P

theorem basis_power (ν : ℕ) (f : Index (Fintype.card μ) → D.Total (CommRingCat.of R)) :
    basis R S μ e site N D K (fun i => (DR).g^ν*f i)=
      (DS).g^ν*basis R S μ e site N D K f := by
  rw [basis_expansion R S μ e site N D K P,basis_expansion R S μ e site N D K P,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hg : GradedMilnorWittScalarNaturality.scalar R S site N D (DR).g=(DS).g :=
    (GradedMilnorWittSheaf.compatible site N D (S:=CommRingCat.of R) (T:=CommRingCat.of S)
      (algebraMap R S)).g
  rw [map_mul,map_pow,hg,←mul_assoc,←((DS).central_g (word R S μ e site N D i)).pow_left ν |>.eq,mul_assoc]

theorem coordinates_power (ν : ℕ) (a : D.Total (CommRingCat.of S)) :
    (basis R S μ e site N D K).symm ((DS).g^ν*a)=
      fun i => (DR).g^ν*((basis R S μ e site N D K).symm a) i := by
  apply (basis R S μ e site N D K).injective
  rw [AddEquiv.apply_symm_apply,basis_power R S μ e site N D K P,AddEquiv.apply_symm_apply]

#print axioms basis_power
#print axioms coordinates_power
end Verification.TorusWordQuadraticAction
