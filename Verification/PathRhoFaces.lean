/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Ring

/-!
# Path Rho Faces

Literal minimal-coordinate path face matrices including rho. A middle
normal coordinate is contracted; its two neighbors are identified. If both
neighbor symbols occur, their product becomes rho times the common symbol.
The adjacent two-face square is proved on the actual finite free modules.
These are local operators, not yet an assembled full path complex.
-/

namespace Verification.PathRhoFaces

open Classical

abbrev Triple := Bool × Bool × Bool
abbrev Five := Bool × Bool × Bool × Bool × Bool

variable {R : Type*} [CommRing R] (ε ρ : R)

/-- The normal-order factor contributed by one preceding symbol. -/
def phase (b : Bool) : R := if b then ε else 1

/-- Exact reduction of two equal coordinate symbols, including the repeated-symbol term. -/
def repeatFactor (a b : Bool) : R := if a && b then ρ else 1

noncomputable def middleColumn (w : Triple) : Bool →₀ R :=
  if w.2.1 then (phase ε w.1 * repeatFactor ρ w.1 w.2.2) •
    Finsupp.single (w.1 || w.2.2) 1 else 0

noncomputable def middle : (Triple →₀ R) →ₗ[R] (Bool →₀ R) :=
  Finsupp.linearCombination R (middleColumn ε ρ)

/-- Add the left one of two independent zero vertices separated by one coordinate. -/
noncomputable def leftColumn (w : Five) : Triple →₀ R :=
  if w.2.1 then (phase ε w.1 * repeatFactor ρ w.1 w.2.2.1) •
    Finsupp.single (w.1 || w.2.2.1, w.2.2.2.1, w.2.2.2.2) 1 else 0

noncomputable def leftFace : (Five →₀ R) →ₗ[R] (Triple →₀ R) :=
  Finsupp.linearCombination R (leftColumn ε ρ)

/-- Add the right zero vertex, including every preceding selected normal symbol. -/
noncomputable def rightColumn (w : Five) : Triple →₀ R :=
  if w.2.2.2.1 then
    (phase ε w.1 * phase ε w.2.1 * phase ε w.2.2.1 * repeatFactor ρ w.2.2.1 w.2.2.2.2) •
      Finsupp.single (w.1, w.2.1, w.2.2.1 || w.2.2.2.2) 1 else 0

noncomputable def rightFace : (Five →₀ R) →ₗ[R] (Triple →₀ R) :=
  Finsupp.linearCombination R (rightColumn ε ρ)

/-- This is the nontrivial overlapping-neighbor two-face identity, including rho terms. -/
theorem adjacent_diamond (hε : ε*ε=1) (hρ : ε*ρ=ρ) :
    (middle ε ρ).comp (leftFace ε ρ)=ε • (middle ε ρ).comp (rightFace ε ρ) := by
  have hρε : ρ*ε=ρ := by simpa only [mul_comm] using hρ
  have hρρ : ε*(ρ*ρ)=ρ*ρ := by rw [← mul_assoc,hρ]
  apply Finsupp.lhom_ext
  rintro ⟨a,i,b,j,c⟩ r
  have hr : Finsupp.single (a,i,b,j,c) r=r • Finsupp.single (a,i,b,j,c) (1 : R) := by simp
  rw [hr,map_smul,map_smul]
  congr 1
  change middle ε ρ (leftFace ε ρ (Finsupp.single (a,i,b,j,c) 1))=
    ε • middle ε ρ (rightFace ε ρ (Finsupp.single (a,i,b,j,c) 1))
  cases a <;> cases i <;> cases b <;> cases j <;> cases c <;>
    simp only [leftFace,rightFace,middle,Finsupp.linearCombination_single,one_smul,
      leftColumn,rightColumn,middleColumn,phase,repeatFactor,Bool.false_eq_true,
      Bool.and_false,Bool.and_true,Bool.false_and,Bool.true_and,Bool.or_false,
      Bool.or_true,Bool.false_or,Bool.true_or,↓reduceIte,map_zero,map_smul,smul_zero,
      Finsupp.linearCombination_single,one_smul,one_mul,mul_one,smul_smul,hε,hρ]
  all_goals simp only [hρε,hρρ]

/-- The formal path coefficient relations give precisely the required braided identities. -/
theorem epsilon_relations (g : R) (hg : g*g=1) (hr : (1+g)*ρ=0) :
    (-g)*(-g)=1 ∧ (-g)*ρ=ρ := by
  constructor
  · simpa only [neg_mul_neg] using hg
  · have hh : ρ+g*ρ=0 := by simpa only [add_mul,one_mul] using hr
    calc
      (-g)*ρ= -(g*ρ) := neg_mul _ _
      _=ρ := by exact neg_eq_iff_add_eq_zero.mpr (by simpa only [add_comm] using hh)

/-- The incidence correction g cancels the two literal normal-order contributions. -/
theorem adjacent_square_zero (g : R) (hg : g*g=1) (hr : (1+g)*ρ=0) :
    g • (middle (-g) ρ).comp (leftFace (-g) ρ)+
      (middle (-g) ρ).comp (rightFace (-g) ρ)=0 := by
  obtain ⟨hε,hρ⟩ := epsilon_relations ρ g hg hr
  rw [adjacent_diamond (-g) ρ hε hρ, smul_smul]
  have hh : g*(-g)= -1 := by rw [mul_neg,hg]
  rw [hh,neg_one_smul,neg_add_cancel]

#print axioms Triple
#print axioms Five
#print axioms phase
#print axioms repeatFactor
#print axioms middleColumn
#print axioms middle
#print axioms leftColumn
#print axioms leftFace
#print axioms rightColumn
#print axioms rightFace
#print axioms adjacent_diamond
#print axioms epsilon_relations
#print axioms adjacent_square_zero

end Verification.PathRhoFaces
