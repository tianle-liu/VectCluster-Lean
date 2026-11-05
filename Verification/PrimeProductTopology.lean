/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Connected.Clopen

/-!
# Prime Product Topology

Finite products of domain factors give the actual connected components
of their prime spectra. The maps are the canonical comaps of projections.
-/
noncomputable section
namespace Verification.PrimeProductTopology
open Set
variable {J : Type*} (R : J → Type*) [∀ j, CommRing (R j)]

theorem continuous_sigmaToPi : Continuous (PrimeSpectrum.sigmaToPi R) := by
  apply continuous_sigma
  intro j
  exact (PrimeSpectrum.comap (Pi.evalRingHom R j)).continuous

theorem closed_sigmaToPi [Finite J] : IsClosedMap (PrimeSpectrum.sigmaToPi R) := by
  intro s hs
  have heq : PrimeSpectrum.sigmaToPi R '' s =
      ⋃ j, (PrimeSpectrum.comap (Pi.evalRingHom R j)) ''
        ((@Sigma.mk J (fun j => PrimeSpectrum (R j)) j) ⁻¹' s) := by
    ext p
    constructor
    · rintro ⟨⟨j,q⟩,hq,rfl⟩
      exact mem_iUnion.mpr ⟨j,q,hq,rfl⟩
    · intro hp
      obtain ⟨j,q,hq,rfl⟩ := mem_iUnion.mp hp
      exact ⟨⟨j,q⟩,hq,rfl⟩
  rw [heq]
  apply isClosed_iUnion_of_finite
  intro j
  exact (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
    (show Function.Surjective (Pi.evalRingHom R j) from
      RingHomSurjective.is_surjective)).isClosedMap _
      (isClosed_sigma_iff.mp hs j)

def spectrumProductHomeomorph [Finite J] :
    (Σ j, PrimeSpectrum (R j)) ≃ₜ PrimeSpectrum (∀ j, R j) :=
  (Equiv.ofBijective (PrimeSpectrum.sigmaToPi R)
    (PrimeSpectrum.sigmaToPi_bijective R)).toHomeomorphOfContinuousClosed
      (continuous_sigmaToPi R) (closed_sigmaToPi R)

theorem spectrumProductHomeomorph_apply [Finite J] (j : J) (p : PrimeSpectrum (R j)) :
    spectrumProductHomeomorph R ⟨j,p⟩ = PrimeSpectrum.comap (Pi.evalRingHom R j) p := rfl

theorem sigma_connectedComponent [∀ j, IsDomain (R j)] (j : J) (p : PrimeSpectrum (R j)) :
    connectedComponent (⟨j,p⟩ : Σ j, PrimeSpectrum (R j)) = Set.range (Sigma.mk j) := by
  apply Set.Subset.antisymm
  · exact isClopen_range_sigmaMk.connectedComponent_subset ⟨p,rfl⟩
  · have h : IsPreconnected (Set.range
        (@Sigma.mk J (fun j => PrimeSpectrum (R j)) j)) :=
      isPreconnected_range (continuous_sigmaMk (σ := fun j => PrimeSpectrum (R j)) (i := j))
    exact h.subset_connectedComponent ⟨p,rfl⟩

theorem image_component_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) : e '' connectedComponent x = connectedComponent (e x) := by
  apply Set.Subset.antisymm (e.continuous.image_connectedComponent_subset x)
  intro y hy
  refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
  have h := e.symm.continuous.image_connectedComponent_subset (e x)
  simpa only [e.symm_apply_apply] using h ⟨y,hy,rfl⟩

theorem product_connectedComponent [Finite J] [∀ j, IsDomain (R j)]
    (j : J) (p : PrimeSpectrum (R j)) :
    connectedComponent (PrimeSpectrum.comap (Pi.evalRingHom R j) p) =
      Set.range (PrimeSpectrum.comap (Pi.evalRingHom R j)) := by
  rw [← spectrumProductHomeomorph_apply R j p,
    ← image_component_homeomorph, sigma_connectedComponent]
  ext x
  constructor
  · rintro ⟨y,⟨q,rfl⟩,rfl⟩
    exact ⟨q,rfl⟩
  · rintro ⟨q,rfl⟩
    exact ⟨⟨j,q⟩,⟨q,rfl⟩,rfl⟩

#print axioms continuous_sigmaToPi
#print axioms closed_sigmaToPi
#print axioms spectrumProductHomeomorph
#print axioms spectrumProductHomeomorph_apply
#print axioms sigma_connectedComponent
#print axioms image_component_homeomorph
#print axioms product_connectedComponent
end Verification.PrimeProductTopology
