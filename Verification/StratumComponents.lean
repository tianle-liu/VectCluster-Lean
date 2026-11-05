/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SmithComponents
import Verification.PrimeProductTopology

/-!
# Stratum Components

Connected components of the actual zero-stratum ring, obtained from its
proved separable-field product decomposition.
-/
noncomputable section
universe u
namespace Verification.StratumComponents
open Verification.PrimeProductTopology
open Verification.GlobalSmithStratum Verification.PartialPowerProduct
open Verification.ActualStratum Verification.ExchangeCharacters
open Verification.DiagonalPowerFibers

section Transport
variable {A J : Type*} [CommRing A] (R : J → Type*) [∀ j, CommRing (R j)]

def componentMap (e : A ≃+* ∀ j, R j) (j : J) :
    C(PrimeSpectrum (R j), PrimeSpectrum A) :=
  (PrimeSpectrum.comap e.toRingHom).comp (PrimeSpectrum.comap (Pi.evalRingHom R j))

theorem componentMap_component [Finite J] [∀ j, IsDomain (R j)]
    (e : A ≃+* ∀ j, R j) (j : J) (p : PrimeSpectrum (R j)) :
    connectedComponent (componentMap R e j p) = Set.range (componentMap R e j) := by
  have h := image_component_homeomorph (PrimeSpectrum.homeomorphOfRingEquiv e).symm
    (PrimeSpectrum.comap (Pi.evalRingHom R j) p)
  rw [product_connectedComponent] at h
  change connectedComponent ((PrimeSpectrum.homeomorphOfRingEquiv e).symm
    (PrimeSpectrum.comap (Pi.evalRingHom R j) p)) = _
  rw [← h]
  ext x
  constructor
  · rintro ⟨y,⟨q,rfl⟩,rfl⟩
    exact ⟨q,rfl⟩
  · rintro ⟨q,rfl⟩
    exact ⟨_,⟨q,rfl⟩,rfl⟩

theorem componentMap_cover [Finite J] (e : A ≃+* ∀ j, R j) :
    ⋃ j, Set.range (componentMap R e j) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  obtain ⟨⟨j,q⟩,hq⟩ := (PrimeSpectrum.sigmaToPi_bijective R).2
    ((PrimeSpectrum.homeomorphOfRingEquiv e) p)
  apply Set.mem_iUnion.mpr
  refine ⟨j,q,?_⟩
  change (PrimeSpectrum.homeomorphOfRingEquiv e).symm
    (PrimeSpectrum.sigmaToPi R ⟨j,q⟩) = p
  rw [hq, Homeomorph.symm_apply_apply]

theorem componentMap_disjoint (e : A ≃+* ∀ j, R j) {i j : J} (hij : i ≠ j) :
    Disjoint (Set.range (componentMap R e i)) (Set.range (componentMap R e j)) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨q,hq⟩ ⟨r,hr⟩
  have hh : PrimeSpectrum.sigmaToPi R ⟨i,q⟩ = PrimeSpectrum.sigmaToPi R ⟨j,r⟩ :=
    (PrimeSpectrum.homeomorphOfRingEquiv e).symm.injective (hq.trans hr.symm)
  exact hij (congrArg Sigma.fst ((PrimeSpectrum.sigmaToPi_injective R) hh))
end Transport

variable {k I K T P : Type u} [Field k] [AddCommGroup P] [Fintype I] [Fintype K]

theorem zero_stratum_connected_components
    (j : T → K) (B : (I ⊕ K) → (I ⊕ T) → ℤ)
    (hB : ∀ a i : I, B (Sum.inl a) (Sum.inl i) = 0)
    (f : P →ₗ[ℤ] (K →₀ ℤ)) (b : Basis I ℤ P)
    (hf : ∀ i, f (b i) = column Finset.univ
      (fun a => B (Sum.inr a) (Sum.inl i)) (fun v => Finsupp.single v 1))
    (hinj : Function.Injective f) {n : ℕ}
    (s : Basis.SmithNormalForm (LinearMap.range f) K n)
    (he : ∀ i, IsUnit ((s.a i).natAbs : k)) :
    ∃ (J : Type u) (_ : Finite J) (L : J → Type u) (_ : ∀ i, Field (L i))
      (_ : ∀ i, Algebra k (L i))
      (e : GlobalZeroStratum k I K T j B ≃ₐ[k]
        ∀ i, MvPolynomial I (Laurent (L i) (FreeIndex (smithEmbedding f s)))),
      (∀ i, Module.Finite k (L i) ∧ Algebra.IsSeparable k (L i)) ∧
      (∀ i (p : PrimeSpectrum (MvPolynomial I
        (Laurent (L i) (FreeIndex (smithEmbedding f s))))),
        connectedComponent (componentMap _ e.toRingEquiv i p) =
          Set.range (componentMap _ e.toRingEquiv i)) ∧
      (⋃ i, Set.range (componentMap _ e.toRingEquiv i)) = Set.univ := by
  obtain ⟨J,hJ,L,hL,aL,e,hsep⟩ :=
    Verification.SmithComponents.zero_stratum_separable_product j B hB f b hf hinj s he
  letI := hJ
  letI := hL
  letI := aL
  letI : ∀ i, IsDomain (MvPolynomial I
      (Laurent (L i) (FreeIndex (smithEmbedding f s)))) := fun i => (hsep i).2.2
  exact ⟨J,hJ,L,hL,aL,e,fun i => ⟨(hsep i).1,(hsep i).2.1⟩,
    fun i p => componentMap_component _ e.toRingEquiv i p,
    componentMap_cover _ e.toRingEquiv⟩

#print axioms componentMap
#print axioms componentMap_component
#print axioms componentMap_cover
#print axioms componentMap_disjoint
#print axioms zero_stratum_connected_components
end Verification.StratumComponents
