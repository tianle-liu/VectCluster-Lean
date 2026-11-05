/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.TerminalProjectionEquiv
import Verification.PathPureContractionData
import Verification.SurvivorBaseChange

/-!
# Terminal Matrix Projection

Explicit terminal cokernel coordinates for a normalized nonpositive finite
complex. This comparison is evaluated on representatives, so later weight
claims can be checked on literal vectors rather than an opaque homology iso.
-/

namespace Verification.TerminalMatrixProjection

open Verification.GradedPerturbation Verification.FinitePerturbation
  Verification.PathPureContractionData

variable {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι]
variable (d : ι → ℤ) (A : Matrix ι ι R) (T : Data d A)

abbrev boundary := matrixDegreeMap d A 1 T.differential_degree (-1) 0 (by omega)
abbrev homotopy := matrixDegreeMap d T.homotopy (-1) T.homotopy_degree 0 (-1) (by omega)

theorem generalized : (boundary d A T).comp ((homotopy d A T).comp (boundary d A T))=
    boundary d A T := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change A.mulVec (T.homotopy.mulVec (A.mulVec x.val))=A.mulVec x.val
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,T.generalized]

include T in
theorem terminal_differential_zero (hn : ∀i,d i≤0) (x : degreeModule (R:=R) d 0) :
    A.mulVec x.val=0 := by
  funext i
  change ∑j,A i j*x.val j=0
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : d j=0
  · rw [T.differential_degree i j (by have hi:=hn i;omega),zero_mul]
  · rw [x.property j hj,mul_zero]

theorem terminal_projector (hn : ∀i,d i≤0) (x : degreeModule (R:=R) d 0) :
    (Verification.TerminalProjectionEquiv.projector (boundary d A T) (homotopy d A T) x).val=
      (pureProjection A T.homotopy).mulVec x.val := by
  change x.val-A.mulVec (T.homotopy.mulVec x.val)=_
  simp only [pureProjection,Matrix.sub_mulVec,Matrix.one_mulVec,←Matrix.mulVec_mulVec,
    terminal_differential_zero d A T hn x,Matrix.mulVec_zero,sub_zero]

noncomputable def fixedEquiv (hn : ∀i,d i≤0) :
    Verification.TerminalProjectionEquiv.fixed (boundary d A T) (homotopy d A T) ≃ₗ[R]
      Verification.SurvivorBaseChange.fixedModule (pureProjection A T.homotopy) where
  toFun x := ⟨x.val.val,by
    change (pureProjection A T.homotopy).mulVec x.val.val-x.val.val=0
    rw [←terminal_projector d A T hn x.val]
    exact sub_eq_zero.mpr (congrArg Subtype.val
      (Verification.TerminalProjectionEquiv.fixed_property _ _ x))⟩
  invFun x := ⟨⟨x.val,by
    intro i hi
    have hx := congrFun (Verification.SurvivorBaseChange.fixed_property _ x) i
    change (∑j,pureProjection A T.homotopy i j*x.val j)=x.val i at hx
    rw [Finset.sum_eq_zero (fun j _ => by rw [T.supported i j hi,zero_mul])] at hx
    exact hx.symm⟩,by
      apply sub_eq_zero.mpr
      apply Subtype.ext
      rw [terminal_projector d A T hn]
      exact Verification.SurvivorBaseChange.fixed_property _ x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def quotientEquiv (hn : ∀i,d i≤0) :
    (degreeModule (R:=R) d 0 ⧸ LinearMap.range (boundary d A T)) ≃ₗ[R]
      Verification.SurvivorBaseChange.fixedModule (pureProjection A T.homotopy) :=
  (Verification.TerminalProjectionEquiv.quotientEquiv (boundary d A T) (homotopy d A T)
    (generalized d A T)).trans (fixedEquiv d A T hn)

theorem quotientEquiv_mk (hn : ∀i,d i≤0) (x : degreeModule (R:=R) d 0) :
    (quotientEquiv d A T hn ((LinearMap.range (boundary d A T)).mkQ x)).val=
      (pureProjection A T.homotopy).mulVec x.val := terminal_projector d A T hn x

#print axioms boundary
#print axioms homotopy
#print axioms generalized
#print axioms terminal_differential_zero
#print axioms terminal_projector
#print axioms fixedEquiv
#print axioms quotientEquiv
#print axioms quotientEquiv_mk

end Verification.TerminalMatrixProjection
