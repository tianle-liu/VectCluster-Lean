/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathRhoWords

/-!
# Path First Cofaces

Literal transpose columns of the rho faces. This computes actual chain
relations before identifying the zero-rho first-boundary cokernel.
-/

namespace Verification.PathFirstCofaces

open Classical Verification.PathRhoWords Verification.PathRhoFaces

variable {R : Type*} [CommRing R]

theorem prepend_same (a : Bool) (x : List Bool →₀ R) (w : List Bool) :
    prepend a x (a::w)=x w :=
  Finsupp.mapDomain_apply (fun _ _ h => List.cons.inj h |>.2) x w

theorem prepend_other (a b : Bool) (h : a ≠ b) (x : List Bool →₀ R) (w : List Bool) :
    prepend a x (b::w)=0 := by
  apply Finsupp.mapDomain_notin_range
  rintro ⟨v,hv⟩
  exact h (List.cons.inj hv).1

theorem prepend_nil (a : Bool) (x : List Bool →₀ R) : prepend a x []=0 := by
  apply Finsupp.mapDomain_notin_range
  rintro ⟨v,hv⟩
  exact List.cons_ne_nil _ _ hv

noncomputable def cofaceColumn (ε ρ : R) : ℕ → List Bool → (List Bool →₀ R)
  | 0, false::tail => Finsupp.single (false::true::false::tail) 1
  | 0, true::tail =>
      ε • Finsupp.single (true::true::false::tail) 1+
        Finsupp.single (false::true::true::tail) 1+
          (ε*ρ) • Finsupp.single (true::true::true::tail) 1
  | 0, [] => 0
  | i+1, a::tail => phase ε a • prepend a (cofaceColumn ε ρ i tail)
  | _+1, [] => 0

noncomputable def coface (ε ρ : R) (i : ℕ) : (List Bool →₀ R) →ₗ[R] (List Bool →₀ R) :=
  Finsupp.linearCombination R (cofaceColumn ε ρ i)

theorem coface_single (ε ρ : R) (i : ℕ) (w : List Bool) :
    coface ε ρ i (Finsupp.single w 1)=cofaceColumn ε ρ i w := by
  simp only [coface,Finsupp.linearCombination_single,one_smul]

/-- Equality of every matrix entry with its literal transpose column. -/
theorem coface_adjoint (ε ρ : R) (i : ℕ) (w v : List Bool) :
    faceColumn ε ρ i w v=cofaceColumn ε ρ i v w := by
  induction i generalizing w v with
  | zero =>
    cases v with
    | nil =>
      cases w with
      | nil => rfl
      | cons a w =>
        cases w with
        | nil => rfl
        | cons b w =>
          cases w with
          | nil => rfl
          | cons c w => cases b <;> simp [faceColumn,cofaceColumn,Finsupp.single_apply]
    | cons bit v =>
      cases w with
      | nil => cases bit <;> simp [faceColumn,cofaceColumn,Finsupp.single_apply]
      | cons a w =>
        cases w with
        | nil => cases bit <;> simp [faceColumn,cofaceColumn,Finsupp.single_apply]
        | cons b w =>
          cases w with
          | nil => cases bit <;> simp [faceColumn,cofaceColumn,Finsupp.single_apply]
          | cons c w =>
            cases a <;> cases b <;> cases c <;> cases bit <;>
              simp [faceColumn,cofaceColumn,phase,repeatFactor,Finsupp.single_apply,eq_comm]
  | succ i ih =>
    cases w with
    | nil =>
      cases v with
      | nil => rfl
      | cons b v => simp only [faceColumn,cofaceColumn,Finsupp.zero_apply,Finsupp.smul_apply,prepend_nil,smul_zero]
    | cons a w =>
      cases v with
      | nil => simp only [faceColumn,cofaceColumn,Finsupp.zero_apply,Finsupp.smul_apply,prepend_nil,smul_zero]
      | cons b v =>
        by_cases hab : a=b
        · subst b
          simp only [faceColumn,cofaceColumn,Finsupp.smul_apply,prepend_same,ih]
        · simp only [faceColumn,cofaceColumn,Finsupp.smul_apply,
            prepend_other a b hab,prepend_other b a (Ne.symm hab),smul_zero]

theorem coface_head_kill (ε : R) (tail : List Bool) :
    cofaceColumn ε 0 0 (false::tail)=Finsupp.single (false::true::false::tail) 1 := rfl

/-- At rho=0 these are exactly the two slid words, with their computed incidence units. -/
theorem coface_head_slide (ε : R) (tail : List Bool) :
    cofaceColumn ε 0 0 (true::tail)=
      ε • Finsupp.single (true::true::false::tail) 1+Finsupp.single (false::true::true::tail) 1 := by
  simp only [cofaceColumn,mul_zero,zero_smul,add_zero]

#print axioms prepend_same
#print axioms prepend_other
#print axioms prepend_nil
#print axioms cofaceColumn
#print axioms coface
#print axioms coface_single
#print axioms coface_adjoint
#print axioms coface_head_kill
#print axioms coface_head_slide

end Verification.PathFirstCofaces
