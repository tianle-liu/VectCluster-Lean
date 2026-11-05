/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathProjectedDegree
import Verification.PathStratumGrading

/-!
# Path Differential Degree

The literal full-rho total differentials raise the cellular degree by one.
-/

namespace Verification.PathDifferentialDegree

open Verification.PathCochains Verification.PathRecursionDegree Verification.PathProjectedDegree
  Verification.PathEndpointComplex

variable {R : Type*} [CommRing R]

theorem differential_degree (g ρ : R) (n : ℕ) (p : ℤ) (x : Total (R := R) n)
    (hx : TotalDegree n p x) : TotalDegree n (p+1) (differential g ρ n x) := by
  intro J hJ
  apply Verification.PathStratumGrading.differential_stratum_zero
  intro j hj
  apply hx
  change ((J.val.erase j).card : ℤ) ≠ p
  have hh := Finset.card_erase_add_one hj
  change (J.val.erase j).card+1=J.val.card at hh
  omega

theorem z_differential_degree (g ρ : R) (n : ℕ) (p : ℤ) (x : ZModule ρ n)
    (hx : TotalDegree n p x.val) : TotalDegree n (p+1) (zDifferential g ρ n x).val :=
  right_degree _ n (p+1) _ (differential_degree g ρ n p x.val hx)

theorem y_differential_degree (g ρ : R) (m : ℕ) (p : ℤ) (x : YModule ρ m)
    (hx : TotalDegree (2*m) p x.val) : TotalDegree (2*m) (p+1) (yDifferential g ρ m x).val :=
  left_degree _ (2*m) (p+1) _ (right_degree _ (2*m) (p+1) _ (differential_degree g ρ (2*m) p x.val hx))

#print axioms differential_degree
#print axioms z_differential_degree
#print axioms y_differential_degree

end Verification.PathDifferentialDegree
