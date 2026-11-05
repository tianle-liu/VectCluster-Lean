/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualTransverseSlice

/-!
# Actual Transverse Localization

The transverse slice defines a morphism of the actual principal-open
and closed pairs. Both squares commute as algebra homomorphisms; the
closed map sends every selected mutated coordinate to the zero section.
-/
noncomputable section
universe u
namespace Verification.ActualTransverseLocalization
open Verification.ActualOpenChart Verification.ActualTransverseSlice
open Verification.ExchangeTransverseSlice
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
variable (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0) (v : ι)

abbrev OpenSource := Localization.Away (originalParameter R ι κ τ j B v)
abbrev OpenTarget := Localization.Away (Polynomial.X : Slice (characters R ι κ τ B))
abbrev ClosedSource := Intermediate R ι κ τ j B v ⧸ closedIdeal R ι κ τ j B v

def openCoefficient : Intermediate R ι κ τ j B v →ₐ[R] OpenTarget R ι κ τ B :=
  (IsScalarTower.toAlgHom R (Slice (characters R ι κ τ B)) (OpenTarget R ι κ τ B)).comp
    (transverseSlice R ι κ τ j B hB v)

theorem parameter_unit : IsUnit (openCoefficient R ι κ τ j B hB v (originalParameter R ι κ τ j B v)) := by
  change IsUnit (algebraMap (Slice (characters R ι κ τ B)) (OpenTarget R ι κ τ B)
    (transverseSlice R ι κ τ j B hB v (originalParameter R ι κ τ j B v)))
  rw [transverse_parameter]
  exact IsLocalization.Away.algebraMap_isUnit Polynomial.X

def localizedSlice : OpenSource R ι κ τ j B v →ₐ[R] OpenTarget R ι κ τ B :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (originalParameter R ι κ τ j B v))
    (f := openCoefficient R ι κ τ j B hB v) (fun z => by
      obtain ⟨m,hm⟩ := z.2
      change IsUnit (openCoefficient R ι κ τ j B hB v z.1)
      rw [← hm,map_pow]
      exact (parameter_unit R ι κ τ j B hB v).pow m)

theorem localizedSlice_coefficient (z : Intermediate R ι κ τ j B v) :
    localizedSlice R ι κ τ j B hB v
      (algebraMap (Intermediate R ι κ τ j B v) (OpenSource R ι κ τ j B v) z) =
    openCoefficient R ι κ τ j B hB v z := IsLocalization.lift_eq _ _

theorem open_square :
    (localizedSlice R ι κ τ j B hB v).comp
      (IsScalarTower.toAlgHom R (Intermediate R ι κ τ j B v) (OpenSource R ι κ τ j B v)) =
    (IsScalarTower.toAlgHom R (Slice (characters R ι κ τ B)) (OpenTarget R ι κ τ B)).comp
      (transverseSlice R ι κ τ j B hB v) := by
  apply AlgHom.ext
  exact localizedSlice_coefficient R ι κ τ j B hB v

def zeroEvaluation : Slice (characters R ι κ τ B) →ₐ[R] Fiber (characters R ι κ τ B) :=
  (Polynomial.aeval (0 : Fiber (characters R ι κ τ B))).restrictScalars R

def closedCoefficient : Intermediate R ι κ τ j B v →ₐ[R] Fiber (characters R ι κ τ B) :=
  (zeroEvaluation R ι κ τ B).comp (transverseSlice R ι κ τ j B hB v)

theorem closedCoefficient_parameter :
    closedCoefficient R ι κ τ j B hB v (originalParameter R ι κ τ j B v) = 0 := by
  change zeroEvaluation R ι κ τ B
    (transverseSlice R ι κ τ j B hB v (originalParameter R ι κ τ j B v)) = 0
  rw [transverse_parameter]
  exact Polynomial.aeval_X 0

def closedSlice : ClosedSource R ι κ τ j B v →ₐ[R] Fiber (characters R ι κ τ B) :=
  Ideal.Quotient.liftₐ (closedIdeal R ι κ τ j B v) (closedCoefficient R ι κ τ j B hB v) (by
    change closedIdeal R ι κ τ j B v ≤ RingHom.ker (closedCoefficient R ι κ τ j B hB v).toRingHom
    apply Ideal.span_le.mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact closedCoefficient_parameter R ι κ τ j B hB v)

theorem closedSlice_coefficient (z : Intermediate R ι κ τ j B v) :
    closedSlice R ι κ τ j B hB v (Ideal.Quotient.mk (closedIdeal R ι κ τ j B v) z) =
      closedCoefficient R ι κ τ j B hB v z := rfl

theorem closed_square :
    (closedSlice R ι κ τ j B hB v).comp (Ideal.Quotient.mkₐ R (closedIdeal R ι κ τ j B v)) =
      (zeroEvaluation R ι κ τ B).comp (transverseSlice R ι κ τ j B hB v) := by
  rfl

theorem closedSlice_partner (i : ι) :
    closedSlice R ι κ τ j B hB v (Ideal.Quotient.mk (closedIdeal R ι κ τ j B v)
      (Ideal.Quotient.mk (partialIdeal R ι κ τ j B v) (ActualOpenPartners.globalPartner R ι κ τ j B i))) = 0 := by
  rw [closedSlice_coefficient]
  change zeroEvaluation R ι κ τ B
    (transverseSlice R ι κ τ j B hB v (Ideal.Quotient.mk (partialIdeal R ι κ τ j B v)
      (ActualOpenPartners.globalPartner R ι κ τ j B i))) = 0
  rw [transverse_partner,map_zero]

#print axioms OpenSource
#print axioms OpenTarget
#print axioms ClosedSource
#print axioms openCoefficient
#print axioms parameter_unit
#print axioms localizedSlice
#print axioms localizedSlice_coefficient
#print axioms open_square
#print axioms zeroEvaluation
#print axioms closedCoefficient
#print axioms closedCoefficient_parameter
#print axioms closedSlice
#print axioms closedSlice_coefficient
#print axioms closed_square
#print axioms closedSlice_partner
end Verification.ActualTransverseLocalization
