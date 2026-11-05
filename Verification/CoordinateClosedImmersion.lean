/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimeKoszulCover
import Verification.PrimeLocalPair
import Verification.PrimeSchemeFiltration
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Coordinate Closed Immersion

The affine coordinate stratum is a genuine closed subscheme of the
appropriate global filtration stage. Its map is the original quotient
after complementary-coordinate localization, factored through that open.
No global closed-immersion assertion is supplied as an input.
-/
noncomputable section
namespace Verification.CoordinateClosedImmersion
open CategoryTheory AlgebraicGeometry
variable (A V : Type) [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V → A) (I : Finset V)

abbrev source := Spec (CommRingCat.of (PrimeStratumPresentation.ClosedRing x I))

def globalMap : source A V x I ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (PrimeStratumPresentation.coordinateMap x I))

theorem globalMap_factor : globalMap A V x I =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (PrimeStratumPresentation.zeroIdeal x I))) ≫
      PrimeLocalPair.inclusion A V x I := by
  exact Spec.map_comp
    (CommRingCat.ofHom (algebraMap A (PrimeStratumPresentation.OpenRing x I)))
    (CommRingCat.ofHom (Ideal.Quotient.mk (PrimeStratumPresentation.zeroIdeal x I)))

instance globalMap_preimmersion : IsPreimmersion (globalMap A V x I) := by
  rw [globalMap_factor]
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (PrimeStratumPresentation.zeroIdeal x I)))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  letI : IsPreimmersion (PrimeLocalPair.inclusion A V x I) := inferInstance
  infer_instance

theorem range_globalMap : Set.range (globalMap A V x I).base =
    PrimeStratumIncidence.stratum x I := PrimeStratumPresentation.range_coordinateMap x I

def ambient : (Spec (CommRingCat.of A)).Opens :=
  PrimeSchemeFiltration.stageOpen A x (I.card+1)

theorem range_subset : Set.range (globalMap A V x I).base ⊆
    Set.range (ambient A V x I).ι.base := by
  rw [range_globalMap,Scheme.Opens.range_ι,PrimeKoszulCover.stratum_zeroLocus]
  exact Set.inter_subset_left

def inclusion : source A V x I ⟶ (ambient A V x I).toScheme :=
  IsOpenImmersion.lift (ambient A V x I).ι (globalMap A V x I) (range_subset A V x I)

theorem inclusion_fac : inclusion A V x I ≫ (ambient A V x I).ι = globalMap A V x I :=
  IsOpenImmersion.lift_fac _ _ _

instance inclusion_preimmersion : IsPreimmersion (inclusion A V x I) := by
  letI : IsPreimmersion (inclusion A V x I ≫ (ambient A V x I).ι) := by
    rw [inclusion_fac]
    infer_instance
  exact IsPreimmersion.of_comp (inclusion A V x I) (ambient A V x I).ι

theorem range_inclusion : Set.range (inclusion A V x I).base =
    (ambient A V x I).ι.base ⁻¹'
      PrimeSpectrum.zeroLocus (Set.range (fun i : I => x i.val)) := by
  have hf (z : source A V x I) :
      (ambient A V x I).ι.base ((inclusion A V x I).base z) = (globalMap A V x I).base z :=
    congrArg (fun f => f.base z) (inclusion_fac A V x I)
  ext p
  constructor
  · rintro ⟨z,rfl⟩
    change (ambient A V x I).ι.base ((inclusion A V x I).base z) ∈
      PrimeSpectrum.zeroLocus (Set.range (fun i : I => x i.val))
    rw [hf]
    have hm : (globalMap A V x I).base z ∈ Set.range (globalMap A V x I).base := ⟨z,rfl⟩
    rw [range_globalMap,PrimeKoszulCover.stratum_zeroLocus] at hm
    exact hm.2
  · intro hz
    have hp : (ambient A V x I).ι.base p ∈ Set.range (ambient A V x I).ι.base := ⟨p,rfl⟩
    rw [Scheme.Opens.range_ι] at hp
    have hm : (ambient A V x I).ι.base p ∈ Set.range (globalMap A V x I).base := by
      rw [range_globalMap,PrimeKoszulCover.stratum_zeroLocus]
      exact ⟨hp,hz⟩
    obtain ⟨z,hz'⟩ := hm
    refine ⟨z,(ambient A V x I).ι.isOpenEmbedding.injective ?_⟩
    exact (hf z).trans hz'

instance inclusion_closed : IsClosedImmersion (inclusion A V x I) := by
  apply IsClosedImmersion.of_isPreimmersion
  rw [range_inclusion]
  exact (PrimeSpectrum.isClosed_zeroLocus _).preimage (ambient A V x I).ι.continuous

#print axioms source
#print axioms globalMap
#print axioms globalMap_factor
#print axioms globalMap_preimmersion
#print axioms range_globalMap
#print axioms ambient
#print axioms range_subset
#print axioms inclusion
#print axioms inclusion_fac
#print axioms inclusion_preimmersion
#print axioms range_inclusion
#print axioms inclusion_closed
end Verification.CoordinateClosedImmersion
