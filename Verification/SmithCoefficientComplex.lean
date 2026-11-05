/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SmithExtendedComplex
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.EuclideanDomain.Int
import Verification.FiniteCoefficientTensor
import Verification.ScalarBlockComplex

/-!
# Smith Coefficient Complex

The tensor extension of the constructed integral Smith complex is actually
isomorphic to the independently defined scalar-block complex.  Hence the
kernel/cokernel formula computes its categorical homology, degree by degree.
-/

noncomputable section
namespace Verification.SmithCoefficientComplex
open CategoryTheory
open scoped TensorProduct
open Verification.SmithComplexCoordinates Verification.SmithComplex
open Verification.SmithScaledComplex Verification.SmithExtendedComplex

variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable (C : CochainComplex (ModuleCat.{0} R) ℤ)
variable [∀ n, Module.Free R (C.X n)] [∀ n, Module.Finite R (C.X n)]
variable (S : Type) [CommRing S] [Algebra R S] (h : S)

def embedding (n : ℤ) : Fin (boundaryRank C n) ↪ Fin (Module.finrank R (cycles C n)) :=
  (smith C n).f

def entry (n : ℤ) (i : Fin (boundaryRank C n)) : Module.End S S :=
  LinearMap.mulLeft S (h * algebraMap R S ((smith C n).a i))

def coefficientComplex : CochainComplex (ModuleCat.{0} S) ℤ :=
  ScalarBlockComplex.complex (embedding C) (entry C S h)

def finsuppTensor (J : Type) [Fintype J] [DecidableEq J] :
    (S ⊗[R] (J →₀ R)) ≃ₗ[S] (J → S) :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S)
    (Finsupp.linearEquivFunOnFinite R R J)).trans
      (TensorProduct.piScalarRight R S S J)

def tensorCoordinates (n : ℤ) : (S ⊗[R] NormalModule C n) ≃ₗ[S]
    ScalarBlockComplex.Term (M := S) (I := fun n => Fin (boundaryRank C n))
      (K := fun n => Fin (Module.finrank R (cycles C n))) n :=
  (TensorProduct.prodRight R S S _ _).trans
    (LinearEquiv.prodCongr (finsuppTensor (R := R) S _) (finsuppTensor (R := R) S _))

theorem tensorCoordinates_tmul (n : ℤ) (r : S) (x : NormalModule C n) :
    tensorCoordinates C S n (r ⊗ₜ[R] x) =
      (fun i => x.1 i • r, fun i => x.2 i • r) :=
  by simp [tensorCoordinates, finsuppTensor]

theorem integral_diagonal_at (n : ℤ) (x : Fin (boundaryRank C n) →₀ R)
    (i : Fin (boundaryRank C n)) :
    diagonal C n x ((smith C n).f i) = x i * (smith C n).a i := by
  classical
  by_cases hx : x i=0
  · simp [diagonal, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.single_apply,
      (smith C n).f.injective.eq_iff, eq_comm, hx]
  · simp [diagonal, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.single_apply,
      (smith C n).f.injective.eq_iff, eq_comm, hx, Ne.symm hx]

theorem integral_diagonal_unmatched (n : ℤ) (x : Fin (boundaryRank C n) →₀ R)
    (j : DiagonalHomology.Unmatched (embedding C n)) : diagonal C n x j.val=0 := by
  classical
  have hj : ∀ i, (smith C n).f i ≠ j.val := fun i hi => j.property ⟨i,hi⟩
  simp [diagonal, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.single_apply, hj]

theorem diagonal_tensor (n : ℤ) (r : S) (x : Fin (boundaryRank C n) →₀ R) :
    DiagonalHomology.diagonal (embedding C n) (entry C S h n) (fun i => x i • r) =
      fun j => (diagonal C n x j) • (h*r) := by
  apply (DiagonalHomology.coordinates (R := S) (embedding C n)).injective
  rw [DiagonalHomology.diagonal_coordinates]
  apply Prod.ext
  · funext i
    change h * algebraMap R S ((smith C n).a i) * (x i • r) =
      diagonal C n x ((smith C n).f i) • (h*r)
    rw [integral_diagonal_at]
    simp only [Algebra.smul_def, map_mul]
    ring
  · funext j
    change 0 = diagonal C n x j.val • (h*r)
    rw [integral_diagonal_unmatched, zero_smul]

theorem differential_tmul (n : ℤ) (r : S) (x : NormalModule C n) :
    tensorCoordinates C S (n+1)
      (((scale h (extendComplex S (normalComplex C))).d n (n+1)).hom (r ⊗ₜ[R] x)) =
      ScalarBlockComplex.differential (embedding C) (entry C S h) n
        (tensorCoordinates C S n (r ⊗ₜ[R] x)) := by
  change tensorCoordinates C S (n+1)
    (h • (((extensionFunctor S).map ((normalComplex C).d n (n+1))).hom (r ⊗ₜ[R] x))) = _
  rw [normalComplex_d]
  change tensorCoordinates C S (n+1) (h • (r ⊗ₜ[R] normalDifferential C n x)) = _
  rw [TensorProduct.smul_tmul', tensorCoordinates_tmul, tensorCoordinates_tmul]
  rw [ScalarBlockComplex.differential_apply]
  apply Prod.ext
  · exact (diagonal_tensor C S h (n+1) r x.2).symm
  · funext i
    exact zero_smul R (h*r)

/-- Actual chain isomorphism, not merely agreement of ranks or scalar entries. -/
def coefficientIso : scale h (extendComplex S (normalComplex C)) ≅ coefficientComplex C S h :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (tensorCoordinates C S n).toModuleIso) (by
      intro n m hnm
      have hm : n+1=m := hnm
      subst m
      change _ ≫ (ScalarBlockComplex.complex (embedding C) (entry C S h)).d n (n+1) = _
      rw [ScalarBlockComplex.complex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul r x => exact (differential_tmul C S h n r x).symm
      | add x y hx hy => simp only [map_add, hx, hy])

/-- Full h-times scalar extension, in constructed Smith coordinates. -/
def extendedCoefficientIso : scale h (extendComplex S C) ≅ coefficientComplex C S h :=
  extendedSmithIso S C h ≪≫ coefficientIso C S h

/-- Homology of the actual extended complex, with the precise shifted kernel terms. -/
def extendedHomologyIso (n : ℤ) :
    (scale h (extendComplex S C)).homology n ≅ ModuleCat.of S
      (ScalarBlockComplex.HomologyTerms (embedding C) (entry C S h) n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.up ℤ) n).mapIso
      (extendedCoefficientIso C S h) ≪≫
    ScalarBlockComplex.homologyIso (embedding C) (entry C S h) n

#print axioms embedding
#print axioms entry
#print axioms coefficientComplex
#print axioms finsuppTensor
#print axioms tensorCoordinates
#print axioms tensorCoordinates_tmul
#print axioms integral_diagonal_at
#print axioms integral_diagonal_unmatched
#print axioms diagonal_tensor
#print axioms differential_tmul
#print axioms coefficientIso
#print axioms extendedCoefficientIso
#print axioms extendedHomologyIso

end Verification.SmithCoefficientComplex
