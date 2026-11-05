/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.DomainProductComponents
import Verification.ProductComponentIdempotents

/-!
# Domain Product Component Labels

Product labels are detected by the actual connected-component clopens,
and equivalently by the corresponding idempotents.
-/
noncomputable section
namespace Verification.DomainProductComponentLabels
variable {A I : Type} [CommRing A] [Finite I]
variable (C : I → Type) [∀ i,CommRing (C i)] [∀ i,IsDomain (C i)]
variable (e : A ≃+* ∀ i,C i)

theorem componentMap (i : I) (p : PrimeSpectrum (C i)) :
    DomainProductComponents.transport C e
      (ConnectedComponents.mk (StratumComponents.componentMap C e i p)) = i := by
  change DomainProductComponents.components C
    (ConnectedComponents.mk ((PrimeSpectrum.homeomorphOfRingEquiv e)
      ((PrimeSpectrum.homeomorphOfRingEquiv e).symm (PrimeSpectrum.comap (Pi.evalRingHom C i) p)))) = i
  rw [Homeomorph.apply_symm_apply]
  exact DomainProductComponents.components_mk C i p

theorem label_iff (p : PrimeSpectrum A) (i : I) :
    DomainProductComponents.transport C e (ConnectedComponents.mk p) = i ↔
      p ∈ Set.range (StratumComponents.componentMap C e i) := by
  constructor
  · intro h
    have hc := Set.eq_univ_iff_forall.mp (StratumComponents.componentMap_cover C e) p
    obtain ⟨j,q,rfl⟩ := Set.mem_iUnion.mp hc
    rw [componentMap] at h
    subst j
    exact ⟨q,rfl⟩
  · rintro ⟨q,rfl⟩
    exact componentMap C e i q

theorem indicator_not_mem (p : PrimeSpectrum A) (i : I) :
    ProductComponentIdempotents.indicator C e i ∉ p.asIdeal ↔
      DomainProductComponents.transport C e (ConnectedComponents.mk p) = i :=
  (ProductComponentIdempotents.not_mem_iff_component C e i p).trans (label_iff C e p i).symm

#print axioms componentMap
#print axioms label_iff
#print axioms indicator_not_mem
end Verification.DomainProductComponentLabels
