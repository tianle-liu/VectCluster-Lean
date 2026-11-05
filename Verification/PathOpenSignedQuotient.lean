/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOpenDifferential
import Verification.PathClosedSignedComplex

/-!
# Path Open Signed Quotient

Removing the actual preceding-coordinate phase gives the direct sum of two
shorter full-rho differentials, on the literal quotient by closed strata.
-/

namespace Verification.PathOpenSignedQuotient

open Classical Verification.PathCompression Verification.PathCochains Verification.PathRhoFaces
  Verification.PathRhoConfiguration Verification.PathRhoSeparated
  Verification.PathOpenEmbedding Verification.PathOpenDifferential
  Verification.PathClosedSignedComplex

variable {R : Type*} [CommRing R]

theorem differential_scalar_twist (g ρ u : R) (hu : u*u=1) (n : ℕ) :
    (differential g ρ n).comp (degreeTwist u n)=
      u • (degreeTwist u n).comp (differential g ρ n) := by
  apply LinearMap.ext
  intro x
  funext J
  apply Subtype.ext
  change ambientDifferential g ρ n (inclusion n (degreeTwist u n x)) J=
    u • (u^J.val.card • ambientDifferential g ρ n (inclusion n x) J)
  rw [smul_smul,ambientDifferential_apply,ambientDifferential_apply,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change faceMap g ρ (eraseConfig J j).val j
    (u^(J.val.erase j).card • (x (eraseConfig J j)).val)=_
  rw [map_smul]
  have he : u^(J.val.erase j).card=u*u^J.val.card := by
    rw [← Finset.card_erase_add_one hj,pow_succ]
    calc
      _=u^(J.val.erase j).card*(u*u) := by rw [hu,mul_one]
      _=_ := by ring
  rw [he]
  rfl

noncomputable def twistEquiv (g : R) (hg : g*g=1) (n : ℕ) :
    (Bool → Total (R := R) n) ≃ₗ[R] (Bool → Total (R := R) n) :=
  LinearEquiv.piCongrRight (fun bit => degreeTwistEquiv (phase (-g) bit)
    (phase_squared (-g) (by simpa only [neg_mul_neg] using hg) bit) n)

noncomputable def directDifferential (g ρ : R) (n : ℕ) :
    (Bool → Total (R := R) n) →ₗ[R] (Bool → Total (R := R) n) :=
  LinearMap.pi (fun bit => (differential g ρ n).comp (LinearMap.proj bit))

theorem twist_intertwining (g ρ : R) (hg : g*g=1) (n : ℕ) :
    (directDifferential g ρ n).comp (twistEquiv g hg n).toLinearMap=
      (twistEquiv g hg n).toLinearMap.comp (openDifferential g ρ n) := by
  apply LinearMap.ext
  intro x
  funext bit
  change differential g ρ n (degreeTwist (phase (-g) bit) n (x bit))=
    degreeTwist (phase (-g) bit) n (phase (-g) bit • differential g ρ n (x bit))
  rw [map_smul]
  exact LinearMap.congr_fun (differential_scalar_twist g ρ (phase (-g) bit)
    (phase_squared (-g) (by simpa only [neg_mul_neg] using hg) bit) n) (x bit)

noncomputable def quotientDifferential (g ρ : R) (n : ℕ) :
    (Total (R := R) (n+1) ⧸ LinearMap.ker (projection n)) →ₗ[R]
      (Total (R := R) (n+1) ⧸ LinearMap.ker (projection n)) :=
  Submodule.mapQ _ _ (differential g ρ (n+1)) (closed_kernel_preserved g ρ n)

/-- Both sides are built from the original differential, not postulated model operators. -/
theorem quotient_intertwining (g ρ : R) (n : ℕ) :
    (quotientEquiv n).toLinearMap.comp (quotientDifferential g ρ n)=
      (openDifferential g ρ n).comp (quotientEquiv n).toLinearMap := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
    exact LinearMap.congr_fun (projection_differential g ρ n) x

noncomputable def signedQuotientEquiv (g : R) (hg : g*g=1) (n : ℕ) :
    (Total (R := R) (n+1) ⧸ LinearMap.ker (projection n)) ≃ₗ[R]
      (Bool → Total (R := R) n) :=
  (quotientEquiv n).trans (twistEquiv g hg n)

theorem signedQuotient_intertwining (g ρ : R) (hg : g*g=1) (n : ℕ) :
    (signedQuotientEquiv g hg n).toLinearMap.comp (quotientDifferential g ρ n)=
      (directDifferential g ρ n).comp (signedQuotientEquiv g hg n).toLinearMap := by
  apply LinearMap.ext
  intro x
  have hq := LinearMap.congr_fun (quotient_intertwining g ρ n) x
  have ht := LinearMap.congr_fun (twist_intertwining g ρ hg n) (quotientEquiv n x)
  change twistEquiv g hg n (quotientEquiv n (quotientDifferential g ρ n x))=
    directDifferential g ρ n (twistEquiv g hg n (quotientEquiv n x))
  rw [show quotientEquiv n (quotientDifferential g ρ n x)=
    openDifferential g ρ n (quotientEquiv n x) from hq]
  exact ht.symm

#print axioms differential_scalar_twist
#print axioms twistEquiv
#print axioms directDifferential
#print axioms twist_intertwining
#print axioms quotientDifferential
#print axioms quotient_intertwining
#print axioms signedQuotientEquiv
#print axioms signedQuotient_intertwining

end Verification.PathOpenSignedQuotient
