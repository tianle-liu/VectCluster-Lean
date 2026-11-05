/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.TwoDegreeResidualInverse
import Verification.PathBalancedPivot

/-!
# Two Degree Residual Pivot

The finite rank balance and the *actual categorical zeroth homology*
construct a left inverse for the residual first boundary and then a literal
ambient generalized inverse.
-/

namespace Verification.TwoDegreeResidualPivot

open CategoryTheory Verification.GradedPerturbation Verification.PerturbedHomologyModel
  Verification.GradedFixedProjection Verification.TwoDegreeFixedComplex

variable {R ι Q : Type} [CommRing R] [Fintype ι] [DecidableEq ι]
variable [AddCommGroup Q] [Module R Q] [Module.Projective R Q]
variable (d : ι → ℤ) (P S : Matrix ι ι R)
variable (hd : Homogeneous d 1 S) (hdP : Homogeneous d 0 P) (hPP : P*P=P)
variable (hPS : P*S=S) (hSP : S*P=S) (hSS : S*S=0)
variable (hP : ∀ i j,d i ≠ -1 → d i ≠ 0 → P i j=0)
variable (h0 : (fixedComplex d P S hd hPS hSS).homology 0 ≃ₗ[R] Q)
variable (balance : (fixedModule d P (-1) × Q) ≃ₗ[R] fixedModule d P 0)

omit [AddCommGroup Q] [Module R Q] [Module.Projective R Q] in
include hdP hPP in
theorem fixed_finite (p : ℤ) : Module.Finite R (fixedModule d P p) :=
  Module.Finite.of_surjective (projection d P hdP hPP p)
    (fun x => ⟨x.val,projection_fixed d P hdP hPP p x⟩)

noncomputable def coordinates : fixedModule d P 0 ≃ₗ[R] (fixedModule d P (-1) × Q) := by
  letI := fixed_finite d P hdP hPP 0
  let coker := (homologyZeroIso d P S hd hPS hSS hP).symm.toLinearEquiv.trans h0
  exact Classical.choose (Verification.PathBalancedPivot.exists_coordinates_of_cokernel
    (firstMap d P S hd hPS) coker balance)

theorem coordinates_first (x : fixedModule d P (-1)) :
    coordinates d P S hd hdP hPP hPS hSS hP h0 balance (firstMap d P S hd hPS x)=(x,0) := by
  letI := fixed_finite d P hdP hPP 0
  exact Classical.choose_spec (Verification.PathBalancedPivot.exists_coordinates_of_cokernel
    (firstMap d P S hd hPS)
    ((homologyZeroIso d P S hd hPS hSS hP).symm.toLinearEquiv.trans h0) balance) x

noncomputable def leftInverse : fixedModule d P 0 →ₗ[R] fixedModule d P (-1) :=
  (LinearMap.fst R (fixedModule d P (-1)) Q).comp
    (coordinates d P S hd hdP hPP hPS hSS hP h0 balance).toLinearMap

theorem left_inverse : (leftInverse d P S hd hdP hPP hPS hSS hP h0 balance).comp
    (firstMap d P S hd hPS)=LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact congrArg Prod.fst (coordinates_first d P S hd hdP hPP hPS hSS hP h0 balance x)

include hdP hPP hP h0 balance in
theorem first_injective : Function.Injective (firstMap d P S hd hPS) := by
  intro x y h
  have hh := congrArg (leftInverse d P S hd hdP hPP hPS hSS hP h0 balance) h
  have hx := LinearMap.congr_fun (left_inverse d P S hd hdP hPP hPS hSS hP h0 balance) x
  have hy := LinearMap.congr_fun (left_inverse d P S hd hdP hPP hPS hSS hP h0 balance) y
  exact hx.symm.trans (hh.trans hy)

noncomputable def generalizedInverse : Matrix ι ι R :=
  Verification.TwoDegreeResidualInverse.inverseMatrix d P hdP hPP
    (leftInverse d P S hd hdP hPP hPS hSS hP h0 balance)

include hSP in
theorem generalized : S*generalizedInverse d P S hd hdP hPP hPS hSS hP h0 balance*S=S :=
  Verification.TwoDegreeResidualInverse.generalized d P S hd hdP hPP hPS hSP hP
    _ (left_inverse d P S hd hdP hPP hPS hSS hP h0 balance)

theorem inverse_degree : Homogeneous d (-1)
    (generalizedInverse d P S hd hdP hPP hPS hSS hP h0 balance) :=
  Verification.TwoDegreeResidualInverse.inverse_degree d P hdP hPP _

include hdP hPP hP h0 balance in
theorem homology_vanishes (p : ℤ) (hp : p ≠ 0) :
    Limits.IsZero ((fixedComplex d P S hd hPS hSS).homology p) :=
  homology_zero d P S hd hPS hSS hP (first_injective d P S hd hdP hPP hPS hSS hP h0 balance) p hp

#print axioms fixed_finite
#print axioms coordinates
#print axioms coordinates_first
#print axioms leftInverse
#print axioms left_inverse
#print axioms first_injective
#print axioms generalizedInverse
#print axioms generalized
#print axioms inverse_degree
#print axioms homology_vanishes

end Verification.TwoDegreeResidualPivot
