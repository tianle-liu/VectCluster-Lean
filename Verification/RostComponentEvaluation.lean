/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RostCanonicalCoefficients

/-!
# Rost Component Evaluation

The already constructed component coordinates for K^M_0 agree with
ordinary evaluation at actual component generic points. This comparison is
proved from the uniform canonical coefficient inputs; it is not another
independent identification of the row or its differential.
-/
noncomputable section
namespace Verification.RostComponentEvaluation
open CategoryTheory AlgebraicGeometry
open Verification.RostCanonicalCoefficients
variable (T : RostAffineInput.Theory) (F : RostFiniteProducts.Standard T)
variable (Z : RostWeightZero.IntegralConvention T) (E : GenericZeroEvaluation T F Z)
variable {J : Type} [Fintype J] (R : J → Type) [∀ j,CommRing (R j)] [∀ j,IsDomain (R j)]
variable {A : Type} [CommRing A] (e : A ≃+* ∀ j,R j)

def point (j : J) : PrimeSpectrum A :=
  PrimeSpectrum.comap e.toRingHom (productPoint R j)

omit [Fintype J] in
theorem point_minimal (j : J) : (point R e j).asIdeal ∈ minimalPrimes A :=
  transportPoint_minimal e _ (productPoint_minimal R j)

theorem point_component (j : J) :
    DomainProductComponents.transport R e (ConnectedComponents.mk (point R e j)) = j := by
  change DomainProductComponents.components R
    (ConnectedComponents.mk ((PrimeSpectrum.homeomorphOfRingEquiv e)
      ((PrimeSpectrum.homeomorphOfRingEquiv e).symm (productPoint R j)))) = j
  rw [Homeomorph.apply_symm_apply]
  exact DomainProductComponents.components_mk R j (domainPoint (R j))

theorem component_value (j : J) (a : Sections T A 0) :
    E.value A (point R e j) (point_minimal R e j) a =
      (RostComponentZero.componentIso T F Z R e).hom a
        (ConnectedComponents.mk (point R e j)) := by
  change E.value A (PrimeSpectrum.comap e.toRingHom (productPoint R j))
    (point_minimal R e j) a = _
  rw [transported_product_value T F Z E R e j (productPoint_minimal R j)
    (point_minimal R e j) a]
  change (Z.zero (R j)).hom (F.product J R 0 0 (transport T e 0 a) j) =
    (Z.zero (R (DomainProductComponents.transport R e (ConnectedComponents.mk (point R e j))))).hom
      (F.product J R 0 0 (transport T e 0 a)
        (DomainProductComponents.transport R e (ConnectedComponents.mk (point R e j))))
  rw [point_component R e j]

theorem generic_values_injective (a b : Sections T A 0)
    (h : ∀ j,E.value A (point R e j) (point_minimal R e j) a =
      E.value A (point R e j) (point_minimal R e j) b) : a = b := by
  apply (RostComponentZero.componentIso T F Z R e).addCommGroupIsoToAddEquiv.injective
  apply funext
  intro c
  let j := DomainProductComponents.transport R e c
  have hc : c = ConnectedComponents.mk (point R e j) := by
    apply (DomainProductComponents.transport R e).injective
    exact (point_component R e j).symm
  change (RostComponentZero.componentIso T F Z R e).hom a c =
    (RostComponentZero.componentIso T F Z R e).hom b c
  rw [hc,← component_value T F Z E R e j a,← component_value T F Z E R e j b]
  exact h j

#print axioms point
#print axioms point_minimal
#print axioms point_component
#print axioms component_value
#print axioms generic_values_injective
end Verification.RostComponentEvaluation
