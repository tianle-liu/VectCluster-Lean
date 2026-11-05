/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathEndpointTotal
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Path Endpoint Complex

Actual full-rho endpoint quotient modules and differentials for Y and Z.
The constant symbols are those of the global coordinates
x_i=(-1)^(floor(i/2)) z_i. No geometric cellular comparison or contraction
is asserted by this construction.
-/

namespace Verification.PathEndpointComplex

open Classical Verification.PathCochains Verification.PathEndpointTotal

variable {R : Type*} [CommRing R]

section Projectors
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- The literal differential on the image of a quotient projector. -/
noncomputable def imageDifferential (P D : M →ₗ[R] M) :
    LinearMap.range P →ₗ[R] LinearMap.range P :=
  LinearMap.codRestrict _ (P.comp (D.comp (LinearMap.range P).subtype))
    (fun x => ⟨D x.val,rfl⟩)

theorem imageDifferential_squared (P D : M →ₗ[R] M)
    (hq : P.comp (D.comp P)=P.comp D) (hd : D.comp D=0) :
    (imageDifferential P D).comp (imageDifferential P D)=0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change P (D (P (D x.val)))=0
  have he := congrArg (fun f : M →ₗ[R] M => f (D x.val)) hq
  change P (D (P (D x.val)))=P (D (D x.val)) at he
  rw [he]
  have hz := congrArg (fun f : M →ₗ[R] M => f x.val) hd
  change D (D x.val)=0 at hz
  rw [hz,map_zero]

/-- The image is canonically the actual quotient by the endpoint relations. -/
noncomputable def imageQuotientEquiv (P : M →ₗ[R] M) :
    (M ⧸ LinearMap.ker P) ≃ₗ[R] LinearMap.range P := P.quotKerEquivRange

theorem product_idempotent (L Q : M →ₗ[R] M)
    (hL : L.comp L=L) (hQ : Q.comp Q=Q) (hc : L.comp Q=Q.comp L) :
    (L.comp Q).comp (L.comp Q)=L.comp Q := by
  apply LinearMap.ext
  intro x
  have hl (y : M) : L (L y)=L y := congrArg (fun f : M →ₗ[R] M => f y) hL
  have hq (y : M) : Q (Q y)=Q y := congrArg (fun f : M →ₗ[R] M => f y) hQ
  have hh (y : M) : L (Q y)=Q (L y) := congrArg (fun f : M →ₗ[R] M => f y) hc
  change L (Q (L (Q x)))=L (Q x)
  rw [← hh (Q x),hl,hq]

theorem product_quotient (L Q D : M →ₗ[R] M)
    (hL : L.comp (D.comp L)=L.comp D) (hQ : Q.comp (D.comp Q)=Q.comp D)
    (hc : L.comp Q=Q.comp L) :
    (L.comp Q).comp (D.comp (L.comp Q))=(L.comp Q).comp D := by
  apply LinearMap.ext
  intro x
  have hl (y : M) : L (D (L y))=L (D y) := congrArg (fun f : M →ₗ[R] M => f y) hL
  have hq (y : M) : Q (D (Q y))=Q (D y) := congrArg (fun f : M →ₗ[R] M => f y) hQ
  have hh (y : M) : L (Q y)=Q (L y) := congrArg (fun f : M →ₗ[R] M => f y) hc
  change L (Q (D (L (Q x))))=L (Q (D x))
  rw [hh,hl,← hh,hq]
end Projectors

/-- The sign of the fixed right endpoint in the globally normalized coordinates. -/
def endpointConstant (ρ : R) (n : ℕ) : R :=
  if ((n+1)/2)%2=0 then 0 else ρ

theorem endpointConstant_relation (ρ : R) (n : ℕ) :
    endpointConstant ρ n*endpointConstant ρ n=ρ*endpointConstant ρ n := by
  unfold endpointConstant
  split <;> simp

noncomputable def zProjection (ρ : R) (n : ℕ) : Total (R := R) n →ₗ[R] Total (R := R) n :=
  right (endpointConstant ρ n) n

noncomputable def yProjection (ρ : R) (a : ℕ) :
    Total (R := R) (2*a) →ₗ[R] Total (R := R) (2*a) :=
  (left 0 (2*a)).comp (right (endpointConstant ρ (2*a)) (2*a))

theorem zProjection_idempotent (ρ : R) (n : ℕ) :
    (zProjection ρ n).comp (zProjection ρ n)=zProjection ρ n := right_idempotent _ _

theorem yProjection_idempotent (ρ : R) (a : ℕ) :
    (yProjection ρ a).comp (yProjection ρ a)=yProjection ρ a :=
  product_idempotent _ _ (left_idempotent _ _) (right_idempotent _ _) (endpoints_commute _ _ _)

theorem zProjection_quotient (g ρ : R) (n : ℕ) :
    (zProjection ρ n).comp ((differential g ρ n).comp (zProjection ρ n))=
      (zProjection ρ n).comp (differential g ρ n) :=
  right_quotient _ _ _ _ (endpointConstant_relation ρ n)

theorem yProjection_quotient (g ρ : R) (a : ℕ) :
    (yProjection ρ a).comp ((differential g ρ (2*a)).comp (yProjection ρ a))=
      (yProjection ρ a).comp (differential g ρ (2*a)) :=
  product_quotient _ _ _ (left_quotient 0 g ρ (2*a) (by simp) (by simp))
    (right_quotient _ _ _ _ (endpointConstant_relation ρ (2*a))) (endpoints_commute _ _ _)

noncomputable abbrev ZModule (ρ : R) (n : ℕ) := LinearMap.range (zProjection ρ n)
noncomputable abbrev YModule (ρ : R) (a : ℕ) := LinearMap.range (yProjection ρ a)

noncomputable def zDifferential (g ρ : R) (n : ℕ) : ZModule ρ n →ₗ[R] ZModule ρ n :=
  imageDifferential (zProjection ρ n) (differential g ρ n)

noncomputable def yDifferential (g ρ : R) (a : ℕ) : YModule ρ a →ₗ[R] YModule ρ a :=
  imageDifferential (yProjection ρ a) (differential g ρ (2*a))

theorem zDifferential_squared (g ρ : R) (n : ℕ) (hg : g*g=1) (hr : (1+g)*ρ=0) :
    (zDifferential g ρ n).comp (zDifferential g ρ n)=0 :=
  imageDifferential_squared _ _ (zProjection_quotient g ρ n)
    (Verification.PathCochainSquare.differential_squared g ρ n hg hr)

theorem yDifferential_squared (g ρ : R) (a : ℕ) (hg : g*g=1) (hr : (1+g)*ρ=0) :
    (yDifferential g ρ a).comp (yDifferential g ρ a)=0 :=
  imageDifferential_squared _ _ (yProjection_quotient g ρ a)
    (Verification.PathCochainSquare.differential_squared g ρ (2*a) hg hr)

noncomputable def zQuotientEquiv (ρ : R) (n : ℕ) :
    (Total (R := R) n ⧸ LinearMap.ker (zProjection ρ n)) ≃ₗ[R] ZModule ρ n :=
  imageQuotientEquiv _

noncomputable def yQuotientEquiv (ρ : R) (a : ℕ) :
    (Total (R := R) (2*a) ⧸ LinearMap.ker (yProjection ρ a)) ≃ₗ[R] YModule ρ a :=
  imageQuotientEquiv _

#print axioms imageDifferential
#print axioms imageDifferential_squared
#print axioms imageQuotientEquiv
#print axioms product_idempotent
#print axioms product_quotient
#print axioms endpointConstant
#print axioms endpointConstant_relation
#print axioms zProjection
#print axioms yProjection
#print axioms zProjection_idempotent
#print axioms yProjection_idempotent
#print axioms zProjection_quotient
#print axioms yProjection_quotient
#print axioms ZModule
#print axioms YModule
#print axioms zDifferential
#print axioms yDifferential
#print axioms zDifferential_squared
#print axioms yDifferential_squared
#print axioms zQuotientEquiv
#print axioms yQuotientEquiv

end Verification.PathEndpointComplex
