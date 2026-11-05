/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.UniversalExchangeChart
import Mathlib.RingTheory.Localization.Integral

/-!
# Universal Exchange Regular

Smoothness and integrality of the actual simultaneous xy-1 open
polynomial models, over smooth integral coefficient rings.
-/
noncomputable section
namespace Verification.UniversalExchangeRegular
open Verification.UniversalExchangeChart
variable (R ι : Type) [CommRing R] [Fintype ι]
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem smooth : Algebra.Smooth R (OpenPolynomial R ι) := by
  letI : Algebra.Smooth R (Polynomial R ι) := {}
  letI : Algebra.Smooth (Polynomial R ι) (OpenPolynomial R ι) :=
    SplitExchangeChart.valueLocalization_smooth (value R ι)
  exact Algebra.Smooth.comp R (Polynomial R ι) (OpenPolynomial R ι)

omit [Fintype ι] in
theorem value_ne_zero [Nontrivial R] (i : ι) : value R ι i ≠ 0 := by
  intro h
  have hc := congrArg (MvPolynomial.constantCoeff : Polynomial R ι →+* R) h
  simp [value] at hc

omit [Fintype ι] in
theorem monoid_regular [IsDomain R] :
    SplitExchangeChart.valueMonoid (value R ι) ≤ nonZeroDivisors (Polynomial R ι) := by
  apply Submonoid.closure_le.mpr
  rintro _ ⟨i,rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (value_ne_zero R ι i)

omit [Fintype ι] in
theorem domain [IsDomain R] : IsDomain (OpenPolynomial R ι) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (Polynomial R ι) (monoid_regular R ι)

#print axioms smooth
#print axioms value_ne_zero
#print axioms monoid_regular
#print axioms domain
end Verification.UniversalExchangeRegular
