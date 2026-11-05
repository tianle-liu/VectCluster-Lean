/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PowerTensorProduct
import Verification.GlobalSmithStratum

/-!
# Power Nontrivial

A positive monic power quotient retains a copy of its coefficient
ring. The finite tensor product therefore has a linear functional taking
one to one, and the actual Smith zero stratum is nonzero.
-/
noncomputable section
universe u
namespace Verification.PowerNontrivial
open Verification.PowerTensorProduct Verification.DiagonalPowerFibers
open Verification.SmoothPowerChart Verification.GlobalSmithStratum
open Verification.ActualStratum Verification.ExchangeCharacters
open scoped TensorProduct
variable {R I : Type u} [CommRing R] [Nontrivial R]

def constantFunctional (e : ℕ) (b : Rˣ) (he : 0 < e) :
    Verification.SmoothPowerChart.PowerAlgebra R e b →ₗ[R] R :=
  (AdjoinRoot.powerBasis' (power_monic R e b he)).basis.coord
    ⟨0, by simpa [powerPolynomial] using he⟩

theorem constantFunctional_one (e : ℕ) (b : Rˣ) (he : 0 < e) :
    constantFunctional e b he 1 = 1 := by
  let pb := AdjoinRoot.powerBasis' (power_monic R e b he)
  let i : Fin pb.dim := ⟨0, by simpa [pb, powerPolynomial] using he⟩
  have hi : pb.basis i = 1 := by rw [pb.basis_eq_pow]; simp [i]
  change pb.basis.coord i 1 = 1
  rw [← hi]
  simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same]

variable [Fintype I] [DecidableEq I]

def tensorFunctional (e : I → ℕ) (b : I → Rˣ) (he : ∀ i, 0 < e i) :
    TensorAlgebra e b →ₗ[R] R :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra R I R).compLinearMap
    (fun i => constantFunctional (e i) (b i) (he i)))

omit [DecidableEq I] in
theorem tensorFunctional_one (e : I → ℕ) (b : I → Rˣ) (he : ∀ i, 0 < e i) :
    tensorFunctional e b he 1 = 1 := by
  change tensorFunctional e b he (PiTensorProduct.tprod R (fun _ => 1)) = 1
  simp [tensorFunctional, PiTensorProduct.lift.tprod, constantFunctional_one]

theorem power_nontrivial (e : I → ℕ) (b : I → Rˣ) (he : ∀ i, 0 < e i) :
    Nontrivial (Verification.DiagonalPowerFibers.PowerAlgebra e b) := by
  have hn : (1 : TensorAlgebra e b) ≠ 0 := by
    intro h
    have := congrArg (tensorFunctional e b he) h
    rw [tensorFunctional_one, map_zero] at this
    exact one_ne_zero this
  letI : Nontrivial (TensorAlgebra e b) := ⟨⟨1, 0, hn⟩⟩
  exact (tensorEquiv e b).symm.toEquiv.nontrivial

variable {K T P : Type u} [Fintype K] [AddCommGroup P]

omit [DecidableEq I] in
theorem zero_stratum_nontrivial
    (j : T → K) (B : (I ⊕ K) → (I ⊕ T) → ℤ)
    (hB : ∀ a i : I, B (Sum.inl a) (Sum.inl i) = 0)
    (f : P →ₗ[ℤ] (K →₀ ℤ)) (b : Basis I ℤ P)
    (hf : ∀ i, f (b i) = column Finset.univ
      (fun a => B (Sum.inr a) (Sum.inl i)) (fun v => Finsupp.single v 1))
    (hinj : Function.Injective f) {n : ℕ}
    (s : Basis.SmithNormalForm (LinearMap.range f) K n) :
    Nontrivial (GlobalZeroStratum R I K T j B) := by
  classical
  letI := power_nontrivial (smithExponent f s) (smithValue (R := R) f hinj b s)
    (smithExponent_positive f s)
  exact (globalSmithEquiv (R := R) j B hB f b hf hinj s).toEquiv.nontrivial

#print axioms constantFunctional
#print axioms constantFunctional_one
#print axioms tensorFunctional
#print axioms tensorFunctional_one
#print axioms power_nontrivial
#print axioms zero_stratum_nontrivial
end Verification.PowerNontrivial
