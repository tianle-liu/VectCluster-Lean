/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ExchangeZeroFiber
import Verification.AffineContraction

/-!
# Exchange Zero Evaluation

The closed restriction of the transverse slice is exactly evaluation
of every affine partner at zero, through the proved closed-layer isomorphism.
-/
noncomputable section
universe u
namespace Verification.ExchangeZeroEvaluation
open MvPolynomial Verification.LocalExchangeSmooth Verification.ExchangeTransverseSlice
variable {R S ι : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (χ : ι → Sˣ) (v : ι)

def zeroSection : ExchangeZeroFiber.Affine χ →ₐ[R] Fiber χ :=
  (AffineContraction.zeroSection (Fiber χ) ι).restrictScalars R

def lineZero : Slice χ →ₐ[R] Fiber χ :=
  (Polynomial.aeval (0 : Fiber χ)).restrictScalars R

theorem zeroSection_equiv :
    (zeroSection (R := R) χ).comp ((ExchangeZeroFiber.affineEquiv (R := R) χ).toAlgHom.comp
      (ExchangeZeroFiber.quotient (R := R) χ)) =
    (lineZero (R := R) χ).comp (sliceMap (R := R) χ v) := by
  apply LocalExchangeSmooth.hom_ext χ
  · intro s
    change zeroSection (R := R) χ (ExchangeZeroFiber.toAffineRaw (R := R) χ (algebraMap S (LocalAlgebra χ) s)) =
      lineZero (R := R) χ (sliceMap (R := R) χ v (algebraMap S (LocalAlgebra χ) s))
    rw [ExchangeZeroFiber.toAffineRaw_coefficient,slice_coefficient]
    simp [zeroSection,lineZero,AffineContraction.zeroSection]
  · intro i
    change zeroSection (R := R) χ (ExchangeZeroFiber.toAffineRaw (R := R) χ (x χ i)) =
      lineZero (R := R) χ (sliceMap (R := R) χ v (x χ i))
    rw [ExchangeZeroFiber.toAffineRaw_x,map_zero,slice_x]
    classical
    by_cases hi : i = v
    · simp [coordinate,hi,lineZero]
    · simp [coordinate,hi]
  · intro i
    change zeroSection (R := R) χ (ExchangeZeroFiber.toAffineRaw (R := R) χ (y χ i)) =
      lineZero (R := R) χ (sliceMap (R := R) χ v (y χ i))
    rw [ExchangeZeroFiber.toAffineRaw_y,slice_y,map_zero]
    exact aeval_X _ _

theorem zeroSection_equiv_apply (z : LocalAlgebra χ) :
    zeroSection (R := R) χ (ExchangeZeroFiber.affineEquiv (R := R) χ (ExchangeZeroFiber.quotient (R := R) χ z)) =
      lineZero (R := R) χ (sliceMap (R := R) χ v z) := AlgHom.congr_fun (zeroSection_equiv (R := R) χ v) z

#print axioms zeroSection
#print axioms lineZero
#print axioms zeroSection_equiv
#print axioms zeroSection_equiv_apply
end Verification.ExchangeZeroEvaluation
