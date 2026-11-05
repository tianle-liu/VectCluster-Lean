/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarBlockComplex
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# Scalar Block Tensor

Evaluation of the actual scalar-block complex on any coefficient module.
The tensor product is identified with literal coordinate functions, and all
differentials are transported. No flatness hypothesis is used.
-/

noncomputable section
namespace Verification.ScalarBlockTensor
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct MonoidalCategory Classical

variable {R : Type} [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
variable {I K : ℤ → Type} [∀ n, Fintype (I n)] [∀ n, Fintype (K n)]
variable (e : ∀ n, I n ↪ K n) (a : ∀ n, I n → R)

def scalarEntry (n : ℤ) (i : I n) : Module.End R R := LinearMap.mulLeft R (a n i)

def moduleEntry (n : ℤ) (i : I n) : Module.End R M := a n i • LinearMap.id

def coefficientFunctor : ModuleCat R ⥤ ModuleCat R :=
  (tensoringRight (ModuleCat R)).obj (ModuleCat.of R M)

instance coefficientFunctor_additive : (coefficientFunctor (R := R) M).Additive := by
  unfold coefficientFunctor
  infer_instance

def functionTensor (J : Type) [Fintype J] : ((J → R) ⊗[R] M) ≃ₗ[R] (J → M) :=
  (TensorProduct.comm R _ _).trans (TensorProduct.piScalarRight R R M J)

theorem functionTensor_tmul (J : Type) [Fintype J] (x : J → R) (m : M) :
    functionTensor (R := R) M J (x ⊗ₜ[R] m) = fun j => x j • m := by
  simp [functionTensor]

def tensorCoordinates (n : ℤ) :
    (ScalarBlockComplex.Term (M := R) (I := I) (K := K) n ⊗[R] M) ≃ₗ[R]
      ScalarBlockComplex.Term (M := M) (I := I) (K := K) n :=
  (TensorProduct.prodLeft R R _ _ M).trans
    (LinearEquiv.prodCongr (functionTensor M (K n)) (functionTensor M (I (n+1))))

theorem tensorCoordinates_tmul (n : ℤ)
    (x : ScalarBlockComplex.Term (M := R) (I := I) (K := K) n) (m : M) :
    tensorCoordinates M (I := I) (K := K) n (x ⊗ₜ[R] m) =
      (fun i => x.1 i • m, fun i => x.2 i • m) := by
  rcases x with ⟨x,y⟩
  simp [tensorCoordinates, functionTensor_tmul]

omit [∀ n, Fintype (I n)] [∀ n, Fintype (K n)] in
theorem diagonal_tensor (n : ℤ) (x : I n → R) (m : M) :
    DiagonalHomology.diagonal (e n) (moduleEntry M a n) (fun i => x i • m) =
      fun j => DiagonalHomology.diagonal (e n) (scalarEntry a n) x j • m := by
  apply (DiagonalHomology.coordinates (R := R) (e n)).injective
  rw [DiagonalHomology.diagonal_coordinates]
  apply Prod.ext
  · funext i
    change a n i • (x i • m) =
      DiagonalHomology.diagonal (e n) (scalarEntry a n) x (e n i) • m
    rw [DiagonalHomology.diagonal_at]
    exact (mul_smul (a n i) (x i) m).symm
  · funext j
    change 0 = DiagonalHomology.diagonal (e n) (scalarEntry a n) x j.val • m
    rw [DiagonalHomology.diagonal_unmatched, zero_smul]

def evaluatedComplex : CochainComplex (ModuleCat R) ℤ :=
  ((coefficientFunctor M).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (ScalarBlockComplex.complex e (scalarEntry a))

/-- All coordinate maps and all differentials agree under actual tensor evaluation. -/
def tensorIso : evaluatedComplex M e a ≅ ScalarBlockComplex.complex e (moduleEntry M a) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (tensorCoordinates M (I := I) (K := K) n).toModuleIso) (by
      intro n k hnk
      have hk : n+1=k := hnk
      subst k
      change _ ≫ (ScalarBlockComplex.complex e (moduleEntry M a)).d n (n+1) =
        (coefficientFunctor M).map ((ScalarBlockComplex.complex e (scalarEntry a)).d n (n+1)) ≫ _
      rw [ScalarBlockComplex.complex_d, ScalarBlockComplex.complex_d]
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro m
      change ScalarBlockComplex.differential e (moduleEntry M a) n
        (tensorCoordinates M n (x ⊗ₜ[R] m)) =
        tensorCoordinates M (n+1) ((ScalarBlockComplex.differential e (scalarEntry a) n x) ⊗ₜ[R] m)
      rw [tensorCoordinates_tmul, tensorCoordinates_tmul, ScalarBlockComplex.differential_apply]
      apply Prod.ext
      · exact diagonal_tensor M e a (n+1) x.2 m
      · funext i
        exact (zero_smul R m).symm)

def evaluatedHomologyIso (n : ℤ) : (evaluatedComplex M e a).homology n ≅
    ModuleCat.of R (ScalarBlockComplex.HomologyTerms e (moduleEntry M a) n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) n).mapIso
      (tensorIso M e a) ≪≫ ScalarBlockComplex.homologyIso e (moduleEntry M a) n

#print axioms scalarEntry
#print axioms moduleEntry
#print axioms coefficientFunctor
#print axioms coefficientFunctor_additive
#print axioms functionTensor
#print axioms functionTensor_tmul
#print axioms tensorCoordinates
#print axioms tensorCoordinates_tmul
#print axioms diagonal_tensor
#print axioms evaluatedComplex
#print axioms tensorIso
#print axioms evaluatedHomologyIso

end Verification.ScalarBlockTensor
