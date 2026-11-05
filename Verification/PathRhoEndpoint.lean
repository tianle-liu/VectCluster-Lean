/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathRhoFaces

/-!
# Path Rho Endpoint

The remaining overlapping two-face relation at a constant endpoint.
Both endpoint constants +1 and -1 are represented, by symbol values 0 and rho.
-/

namespace Verification.PathRhoEndpoint

open Classical Verification.PathRhoFaces

abbrev Pair := Bool × Bool
abbrev Four := Bool × Bool × Bool × Bool

variable {R : Type*} [CommRing R] (ε ρ k : R)

def evaluation (a : Bool) : R := if a then k else 1

noncomputable def endpointColumn (w : Pair) : R := if w.1 then evaluation k w.2 else 0

noncomputable def endpoint : (Pair →₀ R) →ₗ[R] R :=
  Finsupp.linearCombination R (endpointColumn k)

noncomputable def leftColumn (w : Four) : Pair →₀ R :=
  if w.1 then evaluation k w.2.1 • Finsupp.single (w.2.2.1,w.2.2.2) 1 else 0

noncomputable def leftFace : (Four →₀ R) →ₗ[R] (Pair →₀ R) :=
  Finsupp.linearCombination R (leftColumn k)

noncomputable def rightColumn (w : Four) : Pair →₀ R :=
  if w.2.2.1 then (phase ε w.1 * phase ε w.2.1 * repeatFactor ρ w.2.1 w.2.2.2) •
    Finsupp.single (w.1,w.2.1 || w.2.2.2) 1 else 0

noncomputable def rightFace : (Four →₀ R) →ₗ[R] (Pair →₀ R) :=
  Finsupp.linearCombination R (rightColumn ε ρ)

/-- Literal endpoint matrix calculation, valid for either allowed constant symbol. -/
theorem endpoint_diamond (hε : ε*ε=1) (hρ : ε*ρ=ρ) (hkε : ε*k=k) (hk : k*k=ρ*k) :
    (endpoint k).comp (leftFace k)=ε • (endpoint k).comp (rightFace ε ρ) := by
  have hρk : ε*(ρ*k)=ρ*k := by rw [← mul_assoc,hρ]
  apply Finsupp.lhom_ext
  rintro ⟨i,a,j,b⟩ r
  have hr : Finsupp.single (i,a,j,b) r=r • Finsupp.single (i,a,j,b) (1 : R) := by simp
  rw [hr,map_smul,map_smul]
  congr 1
  change endpoint k (leftFace k (Finsupp.single (i,a,j,b) 1))=
    ε • endpoint k (rightFace ε ρ (Finsupp.single (i,a,j,b) 1))
  cases i <;> cases a <;> cases j <;> cases b <;>
    simp only [leftFace,rightFace,endpoint,Finsupp.linearCombination_single,one_smul,
      leftColumn,rightColumn,endpointColumn,evaluation,phase,repeatFactor,Bool.false_eq_true,
      Bool.and_false,Bool.and_true,Bool.false_and,Bool.true_and,Bool.or_false,
      Bool.or_true,Bool.false_or,Bool.true_or,↓reduceIte,map_zero,map_smul,smul_zero,
      Finsupp.linearCombination_single,one_smul,one_mul,mul_one,smul_eq_mul,mul_zero,zero_mul,hε,hρ,hkε,hk]
  all_goals simp only [hρk]

/-- Exactly the two signed constants that occur after the manuscript's coordinate changes. -/
theorem constant_relations (g : R) (hg : g*g=1) (hr : (1+g)*ρ=0) (negative : Bool) :
    (-g)*(-g)=1 ∧ (-g)*ρ=ρ ∧
      (-g)*(if negative then ρ else 0)=(if negative then ρ else 0) ∧
      (if negative then ρ else 0)*(if negative then ρ else 0)=ρ*(if negative then ρ else 0) := by
  obtain ⟨hε,hρ⟩ := epsilon_relations ρ g hg hr
  refine ⟨hε,hρ,?_,?_⟩
  · cases negative <;> simp [hρ]
  · cases negative <;> simp

/-- The full formal incidence sign cancels the endpoint square before any specialization. -/
theorem endpoint_square_zero (g : R) (hg : g*g=1) (hr : (1+g)*ρ=0) (negative : Bool) :
    g • (endpoint (if negative then ρ else 0)).comp (leftFace (if negative then ρ else 0))+
      (endpoint (if negative then ρ else 0)).comp (rightFace (-g) ρ)=0 := by
  obtain ⟨hε,hρ,hkε,hk⟩ := constant_relations ρ g hg hr negative
  rw [endpoint_diamond (-g) ρ _ hε hρ hkε hk,smul_smul]
  have hh : g*(-g)= -1 := by rw [mul_neg,hg]
  rw [hh,neg_one_smul,neg_add_cancel]

#print axioms Pair
#print axioms Four
#print axioms evaluation
#print axioms endpointColumn
#print axioms endpoint
#print axioms leftColumn
#print axioms leftFace
#print axioms rightColumn
#print axioms rightFace
#print axioms endpoint_diamond
#print axioms constant_relations
#print axioms endpoint_square_zero

end Verification.PathRhoEndpoint
