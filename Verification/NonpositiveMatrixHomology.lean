/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.TerminalHomology
import Verification.PerturbedHomologyModel
import Verification.BoundaryCokernelTransport

/-!
# Nonpositive Matrix Homology

Degree-zero homology of an actual matrix complex supported in nonpositive
degrees is the literal first-boundary cokernel.
-/

namespace Verification.NonpositiveMatrixHomology

open Classical CategoryTheory Verification.GradedPerturbation
  Verification.PerturbedHomologyModel

variable {R ι : Type} [CommRing R] [Fintype ι]

omit [Fintype ι] in
theorem degree_eq_zero (d : ι → ℤ) (hd : ∀ i,d i≤0) (p : ℤ) (hp : 0<p)
    (x : degreeModule (R := R) d p) : x=0 := by
  apply Subtype.ext
  funext i
  exact x.property i (by have := hd i; omega)

theorem outgoing_zero (d : ι → ℤ) (D : Matrix ι ι R) (hd : Homogeneous d 1 D)
    (hsq : D*D=0) (hn : ∀ i,d i≤0) : (matrixComplex d D hd hsq).d 0 1=0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact degree_eq_zero d hn 1 (by omega) _

noncomputable def homologyZeroIso (d : ι → ℤ) (D : Matrix ι ι R)
    (hd : Homogeneous d 1 D) (hsq : D*D=0) (hn : ∀ i,d i≤0) :
    (matrixComplex d D hd hsq).homology 0 ≅
      ModuleCat.of R (degreeModule (R := R) d 0 ⧸ LinearMap.range
        (matrixDegreeMap d D 1 hd (-1) 0 (by omega))) := by
  let K := matrixComplex d D hd hsq
  have hg : (K.sc' (-1) 0 1).g=0 := outgoing_zero d D hd hsq hn
  let E := Verification.TerminalHomology.homologyIso (K.sc' (-1) 0 1) hg
  have hf : (K.sc' (-1) 0 1).f.hom=matrixDegreeMap d D 1 hd (-1) 0 (by omega) := by
    change (K.d (-1) 0).hom=_
    rw [matrixComplex_d d D hd hsq (-1) 0 (by omega)]
    rfl
  exact K.homologyIsoSc' (-1) 0 1 (by simp) (by simp) ≪≫ E ≪≫
    (Submodule.quotEquivOfEq _ _ (congrArg LinearMap.range hf)).toModuleIso

#print axioms degree_eq_zero
#print axioms outgoing_zero
#print axioms homologyZeroIso

end Verification.NonpositiveMatrixHomology
