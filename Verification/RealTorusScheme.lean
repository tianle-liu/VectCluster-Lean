/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalTorus
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.Data.Real.Basic

/-!
# Real Torus Scheme

Literal real torus schemes and the actual real points with prescribed
coordinate signs. These give evaluation maps on genuine sheaf sections.
-/
noncomputable section
namespace Verification.RealTorusScheme
open CategoryTheory AlgebraicGeometry
variable (α : Type) [Fintype α] [DecidableEq α]

abbrev ring := OriginalTorus.Torus ℝ α
abbrev torus := Spec (CommRingCat.of (ring α))
abbrev base := Spec (CommRingCat.of ℝ)

def point (p : ring α →ₐ[ℝ] ℝ) : base ⟶ torus α :=
  Scheme.Spec.map (CommRingCat.ofHom p.toRingHom).op

def signedUnit (T : Finset α) (a : α) : ℝˣ := if a∈T then -1 else 1

def sample (T : Finset α) : ring α →ₐ[ℝ] ℝ :=
  MonoidAlgebra.lift ℝ _ _ ((Units.coeHom ℝ).comp
    (PrimitiveCharacters.basisCharacter Finsupp.basisSingleOne (signedUnit α T)))

omit [Fintype α] in
theorem sample_coordinate (T : Finset α) (a : α) :
    sample α T (OriginalTorus.torusCoordinate ℝ α a)=(if a∈T then -1 else 1) := by
  change MonoidAlgebra.lift ℝ _ _ _ (MonoidAlgebra.of ℝ _
    (Multiplicative.ofAdd (Finsupp.basisSingleOne a)))=_
  rw [MonoidAlgebra.lift_of]
  change (PrimitiveCharacters.basisCharacter Finsupp.basisSingleOne
    (signedUnit α T) (Multiplicative.ofAdd (Finsupp.basisSingleOne a)) : ℝ)=_
  rw [PrimitiveCharacters.basisCharacter_apply]
  classical
  by_cases ha : a∈T <;> simp [signedUnit,ha]

def pattern (p : ring α →ₐ[ℝ] ℝ) : Finset α :=
  Finset.univ.filter (fun a => p (OriginalTorus.torusCoordinate ℝ α a)<0)

theorem sample_pattern (T : Finset α) : pattern α (sample α T)=T := by
  classical
  ext a
  simp only [pattern,Finset.mem_filter,Finset.mem_univ,true_and,sample_coordinate]
  by_cases ha : a∈T <;> simp [ha]

#print axioms ring
#print axioms torus
#print axioms base
#print axioms point
#print axioms signedUnit
#print axioms sample
#print axioms sample_coordinate
#print axioms pattern
#print axioms sample_pattern
end Verification.RealTorusScheme
