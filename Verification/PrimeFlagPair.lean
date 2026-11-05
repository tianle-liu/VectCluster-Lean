/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimeFlagOpens
import Verification.PrimeLocalPair

/-!
# Prime Flag Pair

The three opens used to compute an adjacent global boundary are
identified with the literal coordinate flag on the actual complementary
principal localization. The old, full and ambient arrows all commute.
-/
noncomputable section
namespace Verification.PrimeFlagPair
open CategoryTheory AlgebraicGeometry
open Verification.PrimeCoordinateFiltration Verification.PrimeAdjacentExcision
open Verification.PrimeLocalPair
variable (A V : Type) [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V → A) (J : Finset V) (r : ℕ) (hr : J.card = r+1) (v : J)

theorem old_preimage : (inclusion A V x J) ⁻¹ᵁ PrimeFlagOpens.old A V x J v =
    CoordinateFlag.oldComplement (OpenRing A V x J) J (coordinate A V x J) v := by
  ext p
  change (inclusion A V x J).base p ∈ PrimeFlagOpens.old A V x J v ↔ _
  change (inclusion A V x J).base p ∈ (⨆ w : CoordinateFlag.Old J v,
    edgeChart A V x J w.val : (Spec (CommRingCat.of A)).Opens) ↔
    p ∈ (⨆ w : CoordinateFlag.Old J v,
      PrimeSpectrum.basicOpen (coordinate A V x J w.val) :
        (Spec (CommRingCat.of (OpenRing A V x J))).Opens)
  rw [TopologicalSpace.Opens.mem_iSup,TopologicalSpace.Opens.mem_iSup]
  have hp : (inclusion A V x J).base p ∈ chartOpen A V x J := by
    change _ ∈ (chartOpen A V x J : Set (Spec (CommRingCat.of A)))
    rw [← inclusion_range A V x J]
    exact ⟨p,rfl⟩
  constructor
  · rintro ⟨w,hw⟩
    change _ ∈ openBy x (J.erase w.val.val) at hw
    rw [Verification.PrimeAdjacentCharts.chart_erase] at hw
    exact ⟨w,hw.2⟩
  · rintro ⟨w,hw⟩
    refine ⟨w,?_⟩
    change _ ∈ openBy x (J.erase w.val.val)
    rw [Verification.PrimeAdjacentCharts.chart_erase]
    exact ⟨hp,hw⟩

include hr in
theorem old_image : (inclusion A V x J) ''ᵁ
    CoordinateFlag.oldComplement (OpenRing A V x J) J (coordinate A V x J) v =
      PrimeFlagOpens.old A V x J v := by
  rw [← old_preimage, Scheme.Hom.image_preimage_eq_opensRange_inter]
  have he : (inclusion A V x J).opensRange = chartOpen A V x J :=
    TopologicalSpace.Opens.ext (inclusion_range A V x J)
  rw [he,inf_eq_right.mpr]
  exact (PrimeFlagOpens.old_le_current A V x J r hr v).trans inf_le_right

def oldIso :
    (CoordinateFlag.oldComplement (OpenRing A V x J) J (coordinate A V x J) v).toScheme ≅
      (PrimeFlagOpens.old A V x J v).toScheme :=
  (inclusion A V x J).isoImage _ ≪≫
    (Spec (CommRingCat.of A)).isoOfEq (old_image A V x J r hr v)

def fullIso :
    (CoordinateFlag.fullComplement (OpenRing A V x J) J (coordinate A V x J)).toScheme ≅
      (current A V x J r).toScheme :=
  punctureIso A V x J ≪≫ (Spec (CommRingCat.of A)).isoOfEq
    (by dsimp only [PrimeLocalPair.previous,chartOpen,current]; rw [hr])

theorem full_square : CoordinateFlag.fullToAmbient (OpenRing A V x J) J (coordinate A V x J) ≫
    (ambientIso A V x J).hom = (fullIso A V x J r hr).hom ≫
      (Spec (CommRingCat.of A)).homOfLE (inf_le_right : current A V x J r ≤ openBy x J) := by
  rw [← cancel_mono (chartOpen A V x J).ι]
  rw [Category.assoc,ambientIso_inclusion]
  dsimp only [chartOpen]
  rw [Category.assoc,Scheme.homOfLE_ι]
  simp only [fullIso,Iso.trans_hom,Category.assoc,Scheme.isoOfEq_hom_ι,
    punctureIso,Scheme.Hom.isoImage_hom_ι]
  rfl

theorem old_square : CoordinateFlag.oldToFull (OpenRing A V x J) J (coordinate A V x J) v ≫
    (fullIso A V x J r hr).hom = (oldIso A V x J r hr v).hom ≫
      (Spec (CommRingCat.of A)).homOfLE (PrimeFlagOpens.old_le_current A V x J r hr v) := by
  rw [← cancel_mono (current A V x J r).ι]
  simp only [Category.assoc,Scheme.homOfLE_ι,oldIso,fullIso,Iso.trans_hom,
    Scheme.isoOfEq_hom_ι,punctureIso,Scheme.Hom.isoImage_hom_ι]
  simpa only [CoordinateFlag.fullToAmbient,Category.assoc] using congrArg
    (fun f => f ≫ inclusion A V x J)
      (CoordinateFlag.open_triangle (OpenRing A V x J) J (coordinate A V x J) v)

#print axioms old_preimage
#print axioms old_image
#print axioms oldIso
#print axioms fullIso
#print axioms full_square
#print axioms old_square
end Verification.PrimeFlagPair
