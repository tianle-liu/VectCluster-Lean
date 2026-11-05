/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.TFEvenReduction

/-!
# Pure Degree Survivors

Each degree of the actual survivor lattice is canonically isomorphic to the
corresponding categorical homology of the pure complex.  Thus the finite
integral generators of the residual complex are actual pure-homology bases,
not merely bases of an unrelated free module of the same rank.
-/

namespace Verification.PureDegreeSurvivors

open CategoryTheory Verification.FinitePerturbation Verification.GradedPerturbation
open Verification.PerturbedHomologyModel

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (deg : ι → ℤ) (U H : Matrix ι ι R)
variable (hdU : Homogeneous deg 1 U) (hdH : Homogeneous deg (-1) H)
variable (hU : U*U=0) (hHH : H*H=0) (hHUH : H*U*H=H) (hUHU : U*H*U=U)

include hdU hdH in
/-- The normalized pure-homology projector has cellular degree zero. -/
theorem projection_degree : Homogeneous deg 0 (pureProjection U H) := by
  have hUH : Homogeneous deg 0 (U*H) := by
    simpa using homogeneous_mul deg 1 (-1) U H hdU hdH
  have hHU : Homogeneous deg 0 (H*U) := by
    simpa using homogeneous_mul deg (-1) 1 H U hdH hdU
  exact homogeneous_sub deg 0 _ _
    (homogeneous_sub deg 0 _ _ (homogeneous_one deg) hUH) hHU

/-- The actual normalized pure contraction, before any perturbation. -/
def pureRetraction : GradedRetraction deg U (pureProjection U H) where
  differential := 0
  inclusion := pureProjection U H
  retraction := pureProjection U H
  homotopy := H
  square := mul_zero _
  inclusion_chain := by rw [mul_zero]; exact u_pureProjection U H hU hUHU
  retraction_chain := by rw [zero_mul]; exact pureProjection_u U H hU hUHU
  retract := pureProjection_square U H hU hHH hHUH hUHU
  homotopy_identity := pureProjection_square U H hU hHH hHUH hUHU
  homotopy_square := hHH
  homotopy_regular := hHUH
  degreeD := hdU
  squareD := hU
  degreeS := homogeneous_zero deg 1
  degreeI := projection_degree deg U H hdU hdH
  degreeJ := projection_degree deg U H hdU hdH
  degreeH := hdH
  retraction_support := pureProjection_square U H hU hHH hHUH hUHU
  differential_support := mul_zero _

/-- Zero differential on the actual survivor lattices. -/
def zeroComplex (P : Matrix ι ι R) : CochainComplex (ModuleCat R) ℤ :=
  fixedComplex deg P 0 (homogeneous_zero deg 1) (mul_zero _) (mul_zero _)

/-- Every adjacent differential of this survivor complex is literally zero. -/
theorem zeroComplex_d (P : Matrix ι ι R) (p : ℤ) :
    (zeroComplex deg P).d p (p+1)=0 := by
  simp only [zeroComplex, fixedComplex, CochainComplex.of_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact Matrix.zero_mulVec _

/-- All positions, including nonadjacent indices, have zero differential. -/
theorem zeroComplex_d_any (P : Matrix ι ι R) (p q : ℤ) :
    (zeroComplex deg P).d p q=0 := by
  by_cases hpq : p+1=q
  · subst q
    exact zeroComplex_d deg P p
  · exact (zeroComplex deg P).shape p q hpq

/-- Homology of the zero residual complex is its actual module in that degree. -/
noncomputable def zeroHomologyIso (P : Matrix ι ι R) (p : ℤ) :
    (zeroComplex deg P).homology p ≅ ModuleCat.of R (fixedModule deg P p) := by
  let K := zeroComplex deg P
  let S := K.sc' (p-1) p (p+1)
  have hf : S.f=0 := by
    change K.d (p-1) p=0
    exact zeroComplex_d_any deg P (p-1) p
  have hg : S.g=0 := zeroComplex_d deg P p
  exact (K.homologyIsoSc' (p-1) p (p+1) (by simp) (by simp)).trans
    ((S.asIsoHomologyπ hf).symm.trans (S.cyclesIsoX₂ hg))

/-- Actual degreewise pure homology equals the survivor module used in cancellation. -/
noncomputable def pureHomologyIso (p : ℤ) :
    (matrixComplex deg U hdU hU).homology p ≅
      ModuleCat.of R (fixedModule deg (pureProjection U H) p) :=
  (homotopyEquiv deg U (pureProjection U H)
    (pureRetraction deg U H hdU hdH hU hHH hHUH hUHU)).toHomologyIso p ≪≫
    zeroHomologyIso deg (pureProjection U H) p

/-- For the constructed TF reduction, its integer generators are a basis of actual pure homology. -/
noncomputable def pureHomologyBasis (T : Verification.TFEvenReduction.Input (ι := ι)) (p : ℤ) :
    Basis (Fin (Module.finrank ℤ (Verification.SurvivorBaseChange.fixedModule
      (Verification.GradedSurvivorBasis.cut T.degree p (Verification.TFEvenReduction.projection T)))))
      ℤ ((matrixComplex T.degree T.pure T.pure_degree T.pure_square).homology p) :=
  by
    let e := pureHomologyIso T.degree T.pure (Verification.TFEvenReduction.contraction T)
      T.pure_degree (Verification.TFEvenReduction.contraction_degree T)
      T.pure_square (Verification.TFEvenReduction.contraction_square T)
      (Verification.TFEvenReduction.contraction_regular T)
      (Verification.TFEvenReduction.contraction_generalized T) p
    let ea : ((Verification.TFEvenReduction.integerComplex T).X p) ≃+
        ((matrixComplex T.degree T.pure T.pure_degree T.pure_square).homology p) := by
      letI : Module ℤ ((Verification.TFEvenReduction.integerComplex T).X p) :=
        ModuleCat.isModule ((Verification.TFEvenReduction.integerComplex T).X p)
      letI : Module ℤ ((matrixComplex T.degree T.pure T.pure_degree T.pure_square).homology p) :=
        ModuleCat.isModule ((matrixComplex T.degree T.pure T.pure_degree T.pure_square).homology p)
      exact e.symm.toLinearEquiv.toAddEquiv
    exact (Verification.TFEvenReduction.integerBasis T p).map ea.toIntLinearEquiv

/-- Vanishing actual pure homology leaves no degree-p generator in the constructed basis. -/
theorem basisIndex_empty (T : Verification.TFEvenReduction.Input (ι := ι)) (p : ℤ)
    (hz : Limits.IsZero ((matrixComplex T.degree T.pure T.pure_degree T.pure_square).homology p)) :
    IsEmpty (Fin (Module.finrank ℤ (Verification.SurvivorBaseChange.fixedModule
      (Verification.GradedSurvivorBasis.cut T.degree p (Verification.TFEvenReduction.projection T))))) := by
  constructor
  intro i
  apply (pureHomologyBasis T p).ne_zero i
  have he := hz.eq_of_src (𝟙 _) (0 :
    (matrixComplex T.degree T.pure T.pure_degree T.pure_square).homology p ⟶ _)
  exact congrArg (fun f => f.hom ((pureHomologyBasis T p) i)) he

/-- Every degree-vanishing bound for pure homology holds for the actual hyperbolic survivor module. -/
theorem survivor_zero_of_pure_zero (T : Verification.TFEvenReduction.Input (ι := ι)) (p : ℤ)
    (hz : Limits.IsZero ((matrixComplex T.degree T.pure T.pure_degree T.pure_square).homology p)) :
    Limits.IsZero ((targetComplex T.degree _ _ (Verification.TFEvenReduction.retractionData T)).X p) := by
  letI := basisIndex_empty T p hz
  letI : Subsingleton ((targetComplex T.degree _ _ (Verification.TFEvenReduction.retractionData T)).X p) :=
    (Verification.TFEvenReduction.targetBasis T p).repr.injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

/-- Nonzero residual generators necessarily come from nonzero actual pure homology in that degree. -/
theorem nonzero_survivor_homology (T : Verification.TFEvenReduction.Input (ι := ι)) (p : ℤ)
    (hn : ¬Limits.IsZero
      ((targetComplex T.degree _ _ (Verification.TFEvenReduction.retractionData T)).X p)) :
    ¬Limits.IsZero ((matrixComplex T.degree T.pure T.pure_degree T.pure_square).homology p) := by
  intro hz
  exact hn (survivor_zero_of_pure_zero T p hz)

#print axioms projection_degree
#print axioms pureRetraction
#print axioms zeroComplex
#print axioms zeroComplex_d
#print axioms zeroComplex_d_any
#print axioms zeroHomologyIso
#print axioms pureHomologyIso
#print axioms pureHomologyBasis
#print axioms basisIndex_empty
#print axioms survivor_zero_of_pure_zero
#print axioms nonzero_survivor_homology

end Verification.PureDegreeSurvivors
