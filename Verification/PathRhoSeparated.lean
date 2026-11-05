/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathRhoFaces

/-!
# Path Rho Separated

Two disjoint local path faces, with an arbitrary scalar accounting for every
unchanged intermediate selected coordinate. The maps are actual finite free
operators, and no commuting-square identity is an input.
-/

namespace Verification.PathRhoSeparated

open Classical Verification.PathRhoFaces

abbrev Pair := Bool × Bool
abbrev Four := Bool × Bool × Bool × Bool
abbrev Six := Bool × Bool × Bool × Bool × Bool × Bool

variable {R : Type*} [CommRing R] (ε ρ τ : R)

theorem phase_squared (hε : ε*ε=1) (a : Bool) : phase ε a*phase ε a=1 := by
  cases a <;> simp [phase,hε]

theorem phase_merge (hε : ε*ε=1) (hρ : ε*ρ=ρ) (a b : Bool) :
    phase ε a*phase ε (a || b)*repeatFactor ρ a b=phase ε b*repeatFactor ρ a b := by
  cases a <;> cases b <;> simp only [phase,repeatFactor,Bool.false_eq_true,Bool.and_false,
    Bool.and_true,Bool.false_and,Bool.true_and,Bool.or_false,Bool.or_true,
    Bool.false_or,Bool.true_or,↓reduceIte,one_mul,mul_one,hε,hρ]

noncomputable def firstLeftColumn (w : Six) : Four →₀ R :=
  if w.2.1 then (phase ε w.1*repeatFactor ρ w.1 w.2.2.1) •
    Finsupp.single (w.1 || w.2.2.1,w.2.2.2.1,w.2.2.2.2.1,w.2.2.2.2.2) 1 else 0

noncomputable def firstRightColumn (w : Six) : Four →₀ R :=
  if w.2.2.2.2.1 then
    (phase ε w.1*phase ε w.2.1*phase ε w.2.2.1*τ*phase ε w.2.2.2.1*
      repeatFactor ρ w.2.2.2.1 w.2.2.2.2.2) •
    Finsupp.single (w.1,w.2.1,w.2.2.1,w.2.2.2.1 || w.2.2.2.2.2) 1 else 0

noncomputable def afterLeftColumn (w : Four) : Pair →₀ R :=
  if w.2.2.1 then (phase ε w.1*τ*phase ε w.2.1*repeatFactor ρ w.2.1 w.2.2.2) •
    Finsupp.single (w.1,w.2.1 || w.2.2.2) 1 else 0

noncomputable def afterRightColumn (w : Four) : Pair →₀ R :=
  if w.2.1 then (phase ε w.1*repeatFactor ρ w.1 w.2.2.1) •
    Finsupp.single (w.1 || w.2.2.1,w.2.2.2) 1 else 0

noncomputable def firstLeft : (Six →₀ R) →ₗ[R] (Four →₀ R) :=
  Finsupp.linearCombination R (firstLeftColumn ε ρ)

noncomputable def firstRight : (Six →₀ R) →ₗ[R] (Four →₀ R) :=
  Finsupp.linearCombination R (firstRightColumn ε ρ τ)

noncomputable def afterLeft : (Four →₀ R) →ₗ[R] (Pair →₀ R) :=
  Finsupp.linearCombination R (afterLeftColumn ε ρ τ)

noncomputable def afterRight : (Four →₀ R) →ₗ[R] (Pair →₀ R) :=
  Finsupp.linearCombination R (afterRightColumn ε ρ)

/-- Disjoint local faces obey the same braided relation, with all rho corrections retained. -/
theorem separated_diamond (hε : ε*ε=1) (hρ : ε*ρ=ρ) :
    (afterLeft ε ρ τ).comp (firstLeft ε ρ)=
      ε • (afterRight ε ρ).comp (firstRight ε ρ τ) := by
  apply Finsupp.lhom_ext
  rintro ⟨a,i,b,c,j,d⟩ r
  have hr : Finsupp.single (a,i,b,c,j,d) r=r • Finsupp.single (a,i,b,c,j,d) (1 : R) := by simp
  rw [hr,map_smul,map_smul]
  congr 1
  change afterLeft ε ρ τ (firstLeft ε ρ (Finsupp.single (a,i,b,c,j,d) 1))=
    ε • afterRight ε ρ (firstRight ε ρ τ (Finsupp.single (a,i,b,c,j,d) 1))
  cases i <;> cases j <;>
    simp only [firstLeft,firstRight,afterLeft,afterRight,Finsupp.linearCombination_single,one_smul,
      firstLeftColumn,firstRightColumn,afterLeftColumn,afterRightColumn,Bool.false_eq_true,
      ↓reduceIte,map_zero,map_smul,smul_zero,Finsupp.linearCombination_single,one_smul,smul_smul,one_mul]
  congr 1
  change (phase ε a*repeatFactor ρ a b)*(phase ε (a || b)*τ*phase ε c*repeatFactor ρ c d)=
    ε*((phase ε a*ε*phase ε b*τ*phase ε c*repeatFactor ρ c d)*(phase ε a*repeatFactor ρ a b))
  calc
    _=(phase ε a*phase ε (a || b)*repeatFactor ρ a b)*(τ*phase ε c*repeatFactor ρ c d) := by ring
    _=(phase ε b*repeatFactor ρ a b)*(τ*phase ε c*repeatFactor ρ c d) := by rw [phase_merge ε ρ hε hρ]
    _=(ε*ε)*(phase ε a*phase ε a)*(phase ε b*repeatFactor ρ a b)*(τ*phase ε c*repeatFactor ρ c d) := by
      rw [hε,phase_squared ε hε,one_mul,one_mul]
    _=_ := by ring

theorem separated_square_zero (g : R) (hg : g*g=1) (hr : (1+g)*ρ=0) :
    g • (afterLeft (-g) ρ τ).comp (firstLeft (-g) ρ)+
      (afterRight (-g) ρ).comp (firstRight (-g) ρ τ)=0 := by
  obtain ⟨hε,hρ⟩ := epsilon_relations ρ g hg hr
  rw [separated_diamond (-g) ρ τ hε hρ,smul_smul]
  have hh : g*(-g)= -1 := by rw [mul_neg,hg]
  rw [hh,neg_one_smul,neg_add_cancel]

#print axioms Pair
#print axioms Four
#print axioms Six
#print axioms phase_squared
#print axioms phase_merge
#print axioms firstLeftColumn
#print axioms firstRightColumn
#print axioms afterLeftColumn
#print axioms afterRightColumn
#print axioms firstLeft
#print axioms firstRight
#print axioms afterLeft
#print axioms afterRight
#print axioms separated_diamond
#print axioms separated_square_zero

end Verification.PathRhoSeparated
