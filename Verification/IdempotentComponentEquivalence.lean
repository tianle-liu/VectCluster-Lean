/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.DomainProductComponentLabels

/-!
# Idempotent Component Equivalence

A ring map preserving all actual product idempotents induces the
computed bijection on connected components. It is the continuous-map
functor on the actual spectra, not an arbitrary equivalence of labels.
-/
noncomputable section
namespace Verification.IdempotentComponentEquivalence
variable {A S I : Type} [CommRing A] [CommRing S] [Finite I]
variable (C D : I → Type) [∀ i,CommRing (C i)] [∀ i,IsDomain (C i)]
variable [∀ i,CommRing (D i)] [∀ i,IsDomain (D i)]
variable (eS : S ≃+* ∀ i,C i) (eA : A ≃+* ∀ i,D i)
variable (f : S →+* A)
variable (h : ∀ i,f (ProductComponentIdempotents.indicator C eS i) =
  ProductComponentIdempotents.indicator D eA i)

def components : ConnectedComponents (PrimeSpectrum A) ≃ ConnectedComponents (PrimeSpectrum S) :=
  (DomainProductComponents.transport D eA).trans (DomainProductComponents.transport C eS).symm

include h in
theorem components_mk (p : PrimeSpectrum A) :
    components C D eS eA (ConnectedComponents.mk p) =
      ConnectedComponents.mk (PrimeSpectrum.comap f p) := by
  apply (DomainProductComponents.transport C eS).injective
  change (DomainProductComponents.transport C eS)
    ((DomainProductComponents.transport C eS).symm
      (DomainProductComponents.transport D eA (ConnectedComponents.mk p))) = _
  rw [Equiv.apply_symm_apply]
  symm
  apply (DomainProductComponentLabels.indicator_not_mem C eS (PrimeSpectrum.comap f p) _).mp
  change f (ProductComponentIdempotents.indicator C eS _) ∉ p.asIdeal
  rw [h]
  exact (DomainProductComponentLabels.indicator_not_mem D eA p _).mpr rfl

include h in
theorem components_eq_map :
    (components C D eS eA : ConnectedComponents (PrimeSpectrum A) → ConnectedComponents (PrimeSpectrum S)) =
      (PrimeSpectrum.comap f).continuous.connectedComponentsMap := by
  funext c
  obtain ⟨p,rfl⟩ := ConnectedComponents.surjective_coe c
  exact components_mk C D eS eA f h p

#print axioms components
#print axioms components_mk
#print axioms components_eq_map
end Verification.IdempotentComponentEquivalence
