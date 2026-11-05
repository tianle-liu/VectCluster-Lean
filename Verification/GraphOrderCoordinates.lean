/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OrientationWords
import Verification.GraphChainMatrix
import Verification.GraphVertexBound

/-!
# Graph Order Coordinates

Changing the vertex order gives an explicit diagonal chain isomorphism on the
actual signed independence chains.  The diagonal units are the signs of the
actual simplex enumeration permutations; chain compatibility is proved through
the injective exterior realization and its order-independent contraction.
-/

set_option maxHeartbeats 400000

namespace Verification.GraphOrderChange

open Classical

open CategoryTheory Verification.GraphCover Verification.GraphSimplexChains
open Verification.OrientationWords Verification.EvenGraphBridge
open Verification.GraphChainMatrix Verification.GradedPerturbation

variable {R V : Type} [CommRing R] [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) (T : Finset V)

/-- The coordinate unit carrying order-one coefficients to order-two coefficients. -/
noncomputable def orientationUnit (o₁ o₂ : LinearOrder V) (J : Simplex G T) : Rˣ :=
  Units.map (Int.castRingHom R) (orientation o₁ o₂ J.val)⁻¹

omit [Fintype V] in
/-- Each rescaled word is exactly the original oriented exterior simplex. -/
theorem orientationUnit_word (o₁ o₂ : LinearOrder V) (J : Simplex G T) :
    (orientationUnit (R := R) G T o₁ o₂ J : R) • orderedWord (R := R) o₂ J.val=
      orderedWord (R := R) o₁ J.val := by
  have he := congrArg (fun x : ExteriorAlgebra R (V → R) =>
    (orientation o₁ o₂ J.val)⁻¹ • x) (orderedWord_change (R := R) o₁ o₂ J.val)
  simp only [inv_smul_smul] at he
  change ((↑((orientation o₁ o₂ J.val)⁻¹) : ℤ) : R) • orderedWord (R := R) o₂ J.val=_
  rw [Int.cast_smul_eq_zsmul]
  exact he

/-- The actual diagonal change on finite ordinary coefficient functions. -/
noncomputable def coefficientEquiv (o₁ o₂ : LinearOrder V) :
    (Simplex G T → R) ≃ₗ[R] (Simplex G T → R) :=
  LinearEquiv.piCongrRight (fun J => LinearEquiv.smulOfUnit (R := R) (M := R) (orientationUnit (R := R) G T o₁ o₂ J))

omit [Fintype V] [DecidableEq V] in
theorem coefficientEquiv_apply (o₁ o₂ : LinearOrder V) (f : Simplex G T → R) (J : Simplex G T) :
    coefficientEquiv G T o₁ o₂ f J=(orientationUnit (R := R) G T o₁ o₂ J : R)*f J := rfl

/-- The same true linear equivalence on the independent signed-chain coefficient module. -/
noncomputable def chainsEquiv (o₁ o₂ : LinearOrder V) :
    (Simplex G T →₀ R) ≃ₗ[R] (Simplex G T →₀ R) :=
  (Finsupp.linearEquivFunOnFinite R R _).trans
    ((coefficientEquiv G T o₁ o₂).trans (Finsupp.linearEquivFunOnFinite R R _).symm)

theorem chainsEquiv_single (o₁ o₂ : LinearOrder V) (J : Simplex G T) (r : R) :
    chainsEquiv G T o₁ o₂ (Finsupp.single J r)=
      Finsupp.single J ((orientationUnit (R := R) G T o₁ o₂ J : R)*r) := by
  classical
  ext K
  change (orientationUnit (R := R) G T o₁ o₂ K : R)*(Finsupp.single J r) K=_
  by_cases hJK : J=K
  · subst K
    simp
  · simp [Finsupp.single_eq_of_ne hJK]

/-- The literal independently defined exterior realization in a chosen order. -/
noncomputable def realizationFor (o : LinearOrder V) :
    (Simplex G T →₀ R) →ₗ[R] ExteriorAlgebra R (V → R) :=
  letI := o
  realization G T

/-- The literal independently defined signed-deletion operator in a chosen order. -/
noncomputable def boundaryFor (o : LinearOrder V) :
    (Simplex G T →₀ R) →ₗ[R] (Simplex G T →₀ R) :=
  letI := o
  boundary G T

/-- The orientation equivalence identifies the actual exterior realizations. -/
theorem realization_change (o₁ o₂ : LinearOrder V) :
    (realizationFor G T o₂).comp (chainsEquiv (R := R) G T o₁ o₂).toLinearMap=
      realizationFor G T o₁ := by
  apply Finsupp.lhom_ext
  intro J r
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, chainsEquiv_single]
  rw [show realizationFor G T o₂ (Finsupp.single J ((orientationUnit (R := R) G T o₁ o₂ J:R)*r))=
      ((orientationUnit (R := R) G T o₁ o₂ J:R)*r) • orderedWord (R:=R) o₂ J.val from by
    rw [orderedWord_sorted]
    convert @realization_single R V _ o₂ G T J _ using 1
    congr 2
    exact Subsingleton.elim _ _]
  rw [show realizationFor G T o₁ (Finsupp.single J r)=r • orderedWord (R:=R) o₁ J.val from by
    rw [orderedWord_sorted]
    convert @realization_single R V _ o₁ G T J r using 1
    congr 2
    exact Subsingleton.elim _ _]
  rw [mul_smul, smul_comm, orientationUnit_word]

/-- The actual signed boundaries intertwine because the exterior contraction is order-independent. -/
theorem boundary_change (o₁ o₂ : LinearOrder V) :
    (chainsEquiv (R := R) G T o₁ o₂).toLinearMap.comp (boundaryFor G T o₁)=
      (boundaryFor G T o₂).comp (chainsEquiv G T o₁ o₂).toLinearMap := by
  apply LinearMap.ext
  intro f
  apply @realization_injective R V _ _ o₂ G T
  have he (g : Simplex G T →₀ R) := LinearMap.congr_fun (realization_change (R:=R) G T o₁ o₂) g
  have hb₁ := LinearMap.congr_fun (@realization_boundary R V _ _ o₁ G T) f
  have hb₂ := LinearMap.congr_fun (@realization_boundary R V _ _ o₂ G T)
    (chainsEquiv G T o₁ o₂ f)
  change realizationFor G T o₂ (chainsEquiv G T o₁ o₂ (boundaryFor G T o₁ f))=
    realizationFor G T o₂ (boundaryFor G T o₂ (chainsEquiv G T o₁ o₂ f))
  change realizationFor G T o₁ (boundaryFor G T o₁ f)=
    Verification.AugmentedSimplexContraction.boundary (realizationFor G T o₁ f) at hb₁
  change realizationFor G T o₂ (boundaryFor G T o₂ (chainsEquiv G T o₁ o₂ f))=
    Verification.AugmentedSimplexContraction.boundary
      (realizationFor G T o₂ (chainsEquiv G T o₁ o₂ f)) at hb₂
  exact (he _).trans (hb₁.trans (congrArg Verification.AugmentedSimplexContraction.boundary (he f).symm |>.trans hb₂.symm))

/-- The ordinary signed boundary matrix in the specified order. -/
noncomputable def matrixFor (o : LinearOrder V) : Matrix (Simplex G T) (Simplex G T) R :=
  letI := o
  chainMatrix G T

/-- Its already proved actual degreewise chain complex. -/
noncomputable def complexFor (o : LinearOrder V) : CochainComplex (ModuleCat R) ℤ :=
  letI := o
  chainComplex G T

/-- Finite ordinary coordinates identify the actual boundary with its literal matrix. -/
theorem matrix_coordinates (o : LinearOrder V) :
    (Matrix.toLin' (matrixFor (R := R) G T o)).comp
      (Finsupp.linearEquivFunOnFinite R R (Simplex G T)).toLinearMap=
    (Finsupp.linearEquivFunOnFinite R R (Simplex G T)).toLinearMap.comp (boundaryFor G T o) := by
  classical
  apply Finsupp.lhom_ext
  intro J r
  funext K
  change (matrixFor G T o).mulVec (Finsupp.single J r) K=(boundaryFor G T o (Finsupp.single J r)) K
  rw [show ((Finsupp.single J r : Simplex G T →₀ R) : Simplex G T → R)=Pi.single J r from by
      funext K
      simp [Finsupp.single_apply, Pi.single_apply, eq_comm],
    Matrix.mulVec_single]
  change matrixFor G T o K J*r=(boundaryFor G T o (Finsupp.single J r)) K
  rw [show matrixFor G T o K J=(@basisBoundary R V _ o G T J) K from
    @chainMatrix_entry R _ V _ o G T K J]
  simp only [boundaryFor, boundary, Finsupp.linearCombination_single,
    Finsupp.smul_apply, smul_eq_mul, mul_comm]

/-- Actual finite coefficient matrices intertwine under the diagonal orientation change. -/
theorem matrix_change (o₁ o₂ : LinearOrder V) :
    (Matrix.toLin' (matrixFor (R := R) G T o₂)).comp (coefficientEquiv G T o₁ o₂).toLinearMap=
      (coefficientEquiv G T o₁ o₂).toLinearMap.comp (Matrix.toLin' (matrixFor G T o₁)) := by
  apply LinearMap.ext
  intro f
  obtain ⟨g,rfl⟩ := (Finsupp.linearEquivFunOnFinite R R (Simplex G T)).surjective f
  have hb := LinearMap.congr_fun (boundary_change (R:=R) G T o₁ o₂) g
  have hm₁ := LinearMap.congr_fun (matrix_coordinates (R:=R) G T o₁) g
  have hm₂ := LinearMap.congr_fun (matrix_coordinates (R:=R) G T o₂) (chainsEquiv G T o₁ o₂ g)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hb hm₁ hm₂ ⊢
  have he (z : Simplex G T →₀ R) :
      coefficientEquiv G T o₁ o₂ ((Finsupp.linearEquivFunOnFinite R R (Simplex G T)) z)=
      (Finsupp.linearEquivFunOnFinite R R (Simplex G T)) (chainsEquiv G T o₁ o₂ z) := by
    simp only [chainsEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [he,hm₂,←hb,←he,←hm₁]

omit [Fintype V] [DecidableEq V] in
theorem coefficientEquiv_symm_apply (o₁ o₂ : LinearOrder V) (f : Simplex G T → R) (J : Simplex G T) :
    (coefficientEquiv G T o₁ o₂).symm f J=↑((orientationUnit (R := R) G T o₁ o₂ J)⁻¹)*f J := rfl

/-- Orientation acts within each actual cellular degree module. -/
noncomputable def degreeEquiv (o₁ o₂ : LinearOrder V) (p : ℤ) :
    degreeModule (R := R) (Verification.GraphCoverGrading.degree G T) p ≃ₗ[R]
      degreeModule (R := R) (Verification.GraphCoverGrading.degree G T) p where
  toFun f := ⟨coefficientEquiv G T o₁ o₂ f.val, by
    intro J hJ
    rw [coefficientEquiv_apply, f.property J hJ, mul_zero]⟩
  invFun f := ⟨(coefficientEquiv G T o₁ o₂).symm f.val, by
    intro J hJ
    rw [coefficientEquiv_symm_apply, f.property J hJ, mul_zero]⟩
  left_inv f := Subtype.ext ((coefficientEquiv G T o₁ o₂).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((coefficientEquiv G T o₁ o₂).apply_symm_apply f.val)
  map_add' f g := Subtype.ext ((coefficientEquiv G T o₁ o₂).map_add f.val g.val)
  map_smul' a f := Subtype.ext ((coefficientEquiv G T o₁ o₂).map_smul a f.val)

#print axioms orientationUnit
#print axioms orientationUnit_word
#print axioms coefficientEquiv
#print axioms coefficientEquiv_apply
#print axioms chainsEquiv
#print axioms chainsEquiv_single
#print axioms realizationFor
#print axioms boundaryFor
#print axioms realization_change
#print axioms boundary_change
#print axioms matrixFor
#print axioms complexFor
#print axioms matrix_coordinates
#print axioms matrix_change
#print axioms coefficientEquiv_symm_apply
#print axioms degreeEquiv

end Verification.GraphOrderChange
