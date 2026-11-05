/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PerturbedHomologyModel
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-!
# Matrix Degree Equivalence

An actual degree-preserving finite coefficient equivalence and its proved
matrix intertwining induce an isomorphism of the literal matrix complexes.
-/

namespace Verification.MatrixDegreeEquivalence

open CategoryTheory Verification.GradedPerturbation Verification.PerturbedHomologyModel

variable {R : Type} [CommRing R]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (d : ι → ℤ) (e : κ → ℤ) (E : (ι → R) ≃ₗ[R] (κ → R))
variable (hE : ∀ p x, x ∈ degreeModule d p → E x ∈ degreeModule e p)
variable (hI : ∀ p x, x ∈ degreeModule e p → E.symm x ∈ degreeModule d p)

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
noncomputable def degreeEquiv (p : ℤ) : degreeModule (R := R) d p ≃ₗ[R] degreeModule (R := R) e p where
  toFun x := ⟨E x.val,hE p x.val x.property⟩
  invFun y := ⟨E.symm y.val,hI p y.val y.property⟩
  left_inv x := Subtype.ext (E.symm_apply_apply x.val)
  right_inv y := Subtype.ext (E.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (E.map_add x.val y.val)
  map_smul' r x := Subtype.ext (E.map_smul r x.val)

variable (A : Matrix ι ι R) (B : Matrix κ κ R)
variable (hA : Homogeneous d 1 A) (hB : Homogeneous e 1 B) (sA : A*A=0) (sB : B*B=0)
variable (hD : (Matrix.toLin' B).comp E.toLinearMap=E.toLinearMap.comp (Matrix.toLin' A))

noncomputable def complexIso : matrixComplex d A hA sA ≅ matrixComplex e B hB sB :=
  HomologicalComplex.Hom.isoOfComponents
    (C₁ := matrixComplex d A hA sA) (C₂ := matrixComplex e B hB sB)
    (fun p => (degreeEquiv d e E hE hI p).toModuleIso) (by
      intro p q hpq
      have heq : p+1=q := hpq
      subst q
      rw [matrixComplex_d d A hA sA p (p+1) rfl,matrixComplex_d e B hB sB p (p+1) rfl]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change B.mulVec (E x.val)=E (A.mulVec x.val)
      exact LinearMap.congr_fun hD x.val)

noncomputable def homologyIso (p : ℤ) :
    (matrixComplex d A hA sA).homology p ≅ (matrixComplex e B hB sB).homology p :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) p).mapIso
    (complexIso d e E hE hI A B hA hB sA sB hD)

#print axioms degreeEquiv
#print axioms complexIso
#print axioms homologyIso

end Verification.MatrixDegreeEquivalence
