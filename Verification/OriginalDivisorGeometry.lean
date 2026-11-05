/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalScalarNormalization
import Verification.ScalarDivisorGeometry

/-!
# Original Divisor Geometry

Smoothness and the normal parameter on the original whole divisor.
The quotient is transported by the coordinate-preserving unit-scalar
equivalence. Regularity is transported on the ambient ring itself, so
the displayed conormal basis is literally the class of the original x_v.
-/
noncomputable section
namespace Verification.OriginalDivisorGeometry
open Verification.FrozenAcyclicCover Verification.ActualFreezingDivisor
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)

theorem map_divisorIdeal (v : Fin n) :
    ScalarDivisorPresentation.divisorIdeal R κ n B (fun _=>1) (fun _=>1) v =
      (divisorIdeal R κ n B v).map (OriginalScalarOne.globalEquiv R κ n B).toRingHom := by
  rw [divisorIdeal,Ideal.map_span,Set.image_singleton]
  change Ideal.span {ScalarFrozenGlobal.initial R κ n B (fun _=>1) (fun _=>1) (Sum.inl v)} =
    Ideal.span {OriginalScalarOne.globalEquiv R κ n B (initial R κ n B (Sum.inl v))}
  rw [OriginalScalarNormalization.one_initial]

def scalarEquiv (v : Fin n) : Divisor R κ n B v ≃ₐ[R]
    ScalarDivisorPresentation.Divisor R κ n B (fun _ => 1) (fun _ => 1) v :=
  Ideal.quotientEquivAlg (divisorIdeal R κ n B v)
    (ScalarDivisorPresentation.divisorIdeal R κ n B (fun _ => 1) (fun _ => 1) v)
    (OriginalScalarOne.globalEquiv R κ n B) (map_divisorIdeal R κ n B v)

theorem scalarEquiv_coordinate (v : Fin n) (i : Fin n ⊕ κ) :
    scalarEquiv R κ n B v (coordinate R κ n B v i) =
      ScalarDivisorPresentation.coordinate R κ n B (fun _ => 1) (fun _ => 1) v i := by
  change Ideal.Quotient.mk
    (ScalarDivisorPresentation.divisorIdeal R κ n B (fun _=>1) (fun _=>1) v)
    (OriginalScalarOne.globalEquiv R κ n B (initial R κ n B i)) = _
  exact congrArg (Ideal.Quotient.mk _)
    (OriginalScalarNormalization.one_initial R κ n B i)

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)
variable (hall : ∀ I : Finset (Fin n),ExchangeOpenCover.Independent (laterWeights κ n B) I →
  AnticliqueSubcolumns.AS (fun a i => B a (Sum.inl i)) I)

include hpos hneg hsupport hall in
theorem divisor_smooth (v : Fin n) : Algebra.Smooth R (Divisor R κ n B v) := by
  letI := ScalarDivisorGeometry.divisor_smooth R κ n B (fun _=>1) (fun _=>1)
    hpos hneg hsupport hall v
  exact Algebra.Smooth.of_equiv (scalarEquiv R κ n B v).symm

variable [Nontrivial R]

include hpos hneg hsupport hall in
theorem coordinate_regular (v : Fin n) :
    IsSMulRegular (Global R κ n B) (initial R κ n B (Sum.inl v)) := by
  have hr := ScalarGlobalNonzerodivisors.coordinate_regular R κ n B (fun _=>1) (fun _=>1)
    hpos hneg hsupport hall v
  intro a b hab
  apply (OriginalScalarOne.globalEquiv R κ n B).injective
  apply hr
  change ScalarFrozenGlobal.initial R κ n B (fun _=>1) (fun _=>1) (Sum.inl v) *
    OriginalScalarOne.globalEquiv R κ n B a =
      ScalarFrozenGlobal.initial R κ n B (fun _=>1) (fun _=>1) (Sum.inl v) *
        OriginalScalarOne.globalEquiv R κ n B b
  rw [← OriginalScalarNormalization.one_initial,← map_mul,← map_mul]
  exact congrArg (OriginalScalarOne.globalEquiv R κ n B) hab

local instance conormalModule (v : Fin n) :
    Module (Divisor R κ n B v) (divisorIdeal R κ n B v).Cotangent :=
  inferInstanceAs (Module (Global R κ n B ⧸ divisorIdeal R κ n B v)
    (divisorIdeal R κ n B v).Cotangent)

def conormalBasis (v : Fin n) : Basis PUnit (Divisor R κ n B v)
    (divisorIdeal R κ n B v).Cotangent :=
  PrincipalConormal.basis (initial R κ n B (Sum.inl v))
    (coordinate_regular R κ n B hpos hneg hsupport hall v)

theorem conormalBasis_apply (v : Fin n) (u : PUnit) :
    conormalBasis R κ n B hpos hneg hsupport hall v u =
      (divisorIdeal R κ n B v).toCotangent
        ⟨initial R κ n B (Sum.inl v),Ideal.subset_span (Set.mem_singleton _)⟩ :=
  PrincipalConormal.basis_apply _ _ u

def normalParameter (v : Fin n) : Module.Dual (Divisor R κ n B v)
    (divisorIdeal R κ n B v).Cotangent :=
  (conormalBasis R κ n B hpos hneg hsupport hall v).coord PUnit.unit

theorem normalParameter_apply (v : Fin n) :
    normalParameter R κ n B hpos hneg hsupport hall v
      ((divisorIdeal R κ n B v).toCotangent
        ⟨initial R κ n B (Sum.inl v),Ideal.subset_span (Set.mem_singleton _)⟩) = 1 := by
  rw [← conormalBasis_apply R κ n B hpos hneg hsupport hall v PUnit.unit]
  change ((conormalBasis R κ n B hpos hneg hsupport hall v).repr
    (conormalBasis R κ n B hpos hneg hsupport hall v PUnit.unit)) PUnit.unit = 1
  rw [Basis.repr_self,Finsupp.single_eq_same]

#print axioms map_divisorIdeal
#print axioms scalarEquiv
#print axioms scalarEquiv_coordinate
#print axioms divisor_smooth
#print axioms coordinate_regular
#print axioms conormalModule
#print axioms conormalBasis
#print axioms conormalBasis_apply
#print axioms normalParameter
#print axioms normalParameter_apply
end Verification.OriginalDivisorGeometry
