/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinateClosedLayer
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Coordinate Layer Restriction

Actual inclusions between consecutive filtration opens, with the
closed-family complement and noetherian hypotheses for G-localization.
-/
noncomputable section
namespace Verification.CoordinateLayerRestriction
open CategoryTheory AlgebraicGeometry Verification.PrimeCoordinateFiltration
variable (A V : Type) [CommRing A] [Fintype V] [DecidableEq V] (x : V→A)
variable (r : ℕ)

def inclusion : (PrimeSchemeFiltration.stageOpen A x r).toScheme ⟶
    (PrimeSchemeFiltration.stageOpen A x (r+1)).toScheme :=
  (Spec (CommRingCat.of A)).homOfLE (stage_mono x (Nat.le_succ r))

instance inclusion_open : IsOpenImmersion (inclusion A V x r) :=
  inferInstanceAs (IsOpenImmersion ((Spec (CommRingCat.of A)).homOfLE (stage_mono x (Nat.le_succ r))))

theorem inclusion_fac : inclusion A V x r ≫ (PrimeSchemeFiltration.stageOpen A x (r+1)).ι =
    (PrimeSchemeFiltration.stageOpen A x r).ι := Scheme.homOfLE_ι _ _

theorem range_inclusion : Set.range (inclusion A V x r).base =
    (CoordinateClosedLayer.previous A V x r : Set (CoordinateClosedLayer.ambient A V x r).toScheme) := by
  have hf (z : (PrimeSchemeFiltration.stageOpen A x r).toScheme) :
      (PrimeSchemeFiltration.stageOpen A x (r+1)).ι.base ((inclusion A V x r).base z)=
        (PrimeSchemeFiltration.stageOpen A x r).ι.base z :=
    congrArg (fun f => f.base z) (inclusion_fac A V x r)
  ext p
  constructor
  · rintro ⟨z,rfl⟩
    change (PrimeSchemeFiltration.stageOpen A x (r+1)).ι.base ((inclusion A V x r).base z) ∈
      PrimeSchemeFiltration.stageOpen A x r
    rw [hf]
    exact z.property
  · intro hp
    change (PrimeSchemeFiltration.stageOpen A x (r+1)).ι.base p∈PrimeSchemeFiltration.stageOpen A x r at hp
    have hm : (PrimeSchemeFiltration.stageOpen A x (r+1)).ι.base p ∈
        Set.range (PrimeSchemeFiltration.stageOpen A x r).ι.base := by
      rw [Scheme.Opens.range_ι]
      exact hp
    obtain ⟨z,hz⟩ := hm
    exact ⟨z,(PrimeSchemeFiltration.stageOpen A x (r+1)).ι.isOpenEmbedding.injective ((hf z).trans hz)⟩

theorem complement (Allowed : Finset V→Prop) (hall : ∀ p : PrimeSpectrum A,Allowed (zeroSet x p)) :
    (⋃ i : PrimeLayerCover.Index Allowed r,Set.range (CoordinateClosedLayer.inclusion A V x Allowed r i).base)=
      (Set.range (inclusion A V x r).base)ᶜ := by
  rw [range_inclusion]
  exact CoordinateClosedLayer.complement A V x Allowed r hall

instance stage_noetherian [IsNoetherianRing A] :
    IsNoetherian (PrimeSchemeFiltration.stageOpen A x r).toScheme := by
  letI := isLocallyNoetherian_of_isOpenImmersion (PrimeSchemeFiltration.stageOpen A x r).ι
  letI := (PrimeSchemeFiltration.stageOpen A x r).ι.isOpenEmbedding.isInducing.noetherianSpace
  exact {}

#print axioms inclusion
#print axioms inclusion_open
#print axioms inclusion_fac
#print axioms range_inclusion
#print axioms complement
#print axioms stage_noetherian
end Verification.CoordinateLayerRestriction
