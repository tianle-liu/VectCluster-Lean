/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinatePurityInput
import Verification.PrimeCoordinateFiltration
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Prime Local Pair

On the actual principal localization at the complementary coordinate
product, the preceding global filtration stage is exactly the punctured
coordinate pair. All scheme arrows below are the original open immersions.
-/
noncomputable section
namespace Verification.PrimeLocalPair
open CategoryTheory AlgebraicGeometry
open Verification.PrimeCoordinateFiltration
variable (A V : Type) [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V → A) (I : Finset V)

abbrev OpenRing := Localization.Away (∏ i ∈ Iᶜ,x i)

def chartOpen : (Spec (CommRingCat.of A)).Opens := openBy x I

def previous : (Spec (CommRingCat.of A)).Opens := stage x I.card

def coordinate (i : I) : OpenRing A V x I := algebraMap A _ (x i)

def inclusion : Spec (CommRingCat.of (OpenRing A V x I)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A _))

instance inclusion_open : IsOpenImmersion (inclusion A V x I) :=
  inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (algebraMap A (Localization.Away (∏ i ∈ Iᶜ,x i))))))

theorem inclusion_range : Set.range (inclusion A V x I).base = (chartOpen A V x I : Set (Spec (CommRingCat.of A))) :=
  PrimeSpectrum.localization_away_comap_range (OpenRing A V x I) (∏ i ∈ Iᶜ,x i)

def ambientIso : Spec (CommRingCat.of (OpenRing A V x I)) ≅ (chartOpen A V x I).toScheme :=
  IsOpenImmersion.isoOfRangeEq (inclusion A V x I) (chartOpen A V x I).ι
    ((inclusion_range A V x I).trans (Scheme.Opens.range_ι _).symm)

theorem ambientIso_inclusion : (ambientIso A V x I).hom ≫ (chartOpen A V x I).ι = inclusion A V x I :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

theorem puncture_preimage : (inclusion A V x I) ⁻¹ᵁ previous A V x I =
    CoordinatePurityInput.puncture (OpenRing A V x I) I (coordinate A V x I) := by
  classical
  ext p
  change (inclusion A V x I).base p ∈ stage x I.card ↔
    p ∈ (⨆ i,PrimeSpectrum.basicOpen (coordinate A V x I i) : TopologicalSpace.Opens (PrimeSpectrum (OpenRing A V x I)))
  rw [mem_stage,TopologicalSpace.Opens.mem_iSup]
  have hsub : zeroSet x ((inclusion A V x I).base p) ⊆ I :=
    (mem_openBy x I _).mp (by
      change (inclusion A V x I).base p ∈ (chartOpen A V x I : Set (Spec (CommRingCat.of A)))
      rw [← inclusion_range A V x I]
      exact ⟨p,rfl⟩)
  constructor
  · intro hcard
    have hne : I ≠ zeroSet x ((inclusion A V x I).base p) := by
      intro heq
      rw [← heq] at hcard
      exact (Nat.lt_irrefl _) hcard
    obtain ⟨i,hi,hn⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hsub,Ne.symm hne⟩)
    refine ⟨⟨i,hi⟩,?_⟩
    change algebraMap A (OpenRing A V x I) (x i) ∉ p.asIdeal
    exact fun h => hn ((mem_zeroSet x _ i).mpr h)
  · rintro ⟨i,hi⟩
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub,?_⟩
    intro heq
    have hm : i.val ∈ zeroSet x ((inclusion A V x I).base p) :=
      (congrArg (fun S : Finset V => i.val ∈ S) heq).mpr i.property
    exact hi ((mem_zeroSet x _ i.val).mp hm)

theorem puncture_image : (inclusion A V x I) ''ᵁ
    CoordinatePurityInput.puncture (OpenRing A V x I) I (coordinate A V x I) =
      previous A V x I ⊓ chartOpen A V x I := by
  rw [← puncture_preimage,Scheme.Hom.image_preimage_eq_opensRange_inter]
  have hr : (inclusion A V x I).opensRange = chartOpen A V x I :=
    TopologicalSpace.Opens.ext (inclusion_range A V x I)
  rw [hr,inf_comm]

def punctureIso :
    (CoordinatePurityInput.puncture (OpenRing A V x I) I (coordinate A V x I)).toScheme ≅
      (previous A V x I ⊓ chartOpen A V x I).toScheme :=
  (inclusion A V x I).isoImage _ ≪≫ (Spec (CommRingCat.of A)).isoOfEq (puncture_image A V x I)

theorem punctureIso_square :
    (CoordinatePurityInput.puncture (OpenRing A V x I) I (coordinate A V x I)).ι ≫
        (ambientIso A V x I).hom =
      (punctureIso A V x I).hom ≫ (Spec (CommRingCat.of A)).homOfLE inf_le_right := by
  rw [← cancel_mono (chartOpen A V x I).ι]
  simp only [Category.assoc,ambientIso_inclusion,Scheme.homOfLE_ι,punctureIso,Iso.trans_hom,
    Scheme.isoOfEq_hom_ι,Scheme.Hom.isoImage_hom_ι]

#print axioms OpenRing
#print axioms chartOpen
#print axioms previous
#print axioms coordinate
#print axioms inclusion
#print axioms inclusion_open
#print axioms inclusion_range
#print axioms ambientIso
#print axioms ambientIso_inclusion
#print axioms puncture_preimage
#print axioms puncture_image
#print axioms punctureIso
#print axioms punctureIso_square
end Verification.PrimeLocalPair
