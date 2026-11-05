/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimeCoordinateFiltration
import Verification.GlobalNormalFrame

/-!
# Prime Stratum Presentation

The affine locally closed presentation has exactly the original
coordinate stratum as its image in the actual prime spectrum. This is
proved using the real quotient and localization spectrum maps.
-/
noncomputable section
namespace Verification.PrimeStratumPresentation
open scoped BigOperators
variable {A V : Type*} [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V → A) (I : Finset V)

abbrev OpenRing := Localization.Away (∏ i ∈ Iᶜ, x i)

def zeroIdeal : Ideal (OpenRing x I) :=
  Ideal.span (Set.range (fun i : I => algebraMap A (OpenRing x I) (x i.val)))

abbrev ClosedRing := OpenRing x I ⧸ zeroIdeal x I

def coordinateMap : A →+* ClosedRing x I :=
  (Ideal.Quotient.mk (zeroIdeal x I)).comp (algebraMap A (OpenRing x I))

theorem zeroLocus_preimage : PrimeSpectrum.zeroLocus (zeroIdeal x I) =
    PrimeSpectrum.comap (algebraMap A (OpenRing x I)) ⁻¹'
      PrimeSpectrum.zeroLocus (Set.range (fun i : I => x i.val)) := by
  rw [PrimeSpectrum.preimage_comap_zeroLocus,zeroIdeal,PrimeSpectrum.zeroLocus_span,← Set.range_comp]
  rfl

theorem range_coordinateMap : Set.range (PrimeSpectrum.comap (coordinateMap x I)) =
    PrimeStratumIncidence.stratum x I := by
  rw [coordinateMap,PrimeSpectrum.comap_comp]
  change Set.range ((PrimeSpectrum.comap (algebraMap A (OpenRing x I))) ∘
    (PrimeSpectrum.comap (Ideal.Quotient.mk (zeroIdeal x I)))) = _
  rw [Set.range_comp,
    PrimeSpectrum.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker,zeroLocus_preimage,Set.image_preimage_eq_inter_range,
    PrimeSpectrum.localization_away_comap_range (OpenRing x I) (∏ i ∈ Iᶜ, x i)]
  ext p
  change (p ∈ PrimeSpectrum.zeroLocus (Set.range (fun i : I => x i.val)) ∧
    p ∈ PrimeCoordinateFiltration.openBy x I) ↔ _
  rw [PrimeCoordinateFiltration.mem_openBy]
  constructor
  · rintro ⟨hz,ho⟩ i
    constructor
    · intro hi
      exact ho ((PrimeCoordinateFiltration.mem_zeroSet x p i).mpr hi)
    · intro hi
      exact (PrimeSpectrum.mem_zeroLocus p _).mp hz (Set.mem_range.mpr ⟨⟨i,hi⟩,rfl⟩)
  · intro hp
    refine ⟨(PrimeSpectrum.mem_zeroLocus p _).mpr ?_,?_⟩
    · rintro _ ⟨i,rfl⟩
      exact (hp i.val).mpr i.property
    · intro i hi
      exact (hp i).mp ((PrimeCoordinateFiltration.mem_zeroSet x p i).mp hi)

section Actual
open Verification.FrozenAcyclicCover
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (J : Finset (Fin n))

def actualMap : Global R κ n B →+* GlobalNormalFrame.ZeroLayer R κ n J B :=
  coordinateMap (fun i => initial R κ n B (Sum.inl i)) J

theorem actual_range : Set.range (PrimeSpectrum.comap (actualMap R κ n B J)) =
    PrimeStratumIncidence.actualStratum R κ n B J :=
  range_coordinateMap _ _

end Actual
#print axioms OpenRing
#print axioms zeroIdeal
#print axioms ClosedRing
#print axioms coordinateMap
#print axioms zeroLocus_preimage
#print axioms range_coordinateMap
#print axioms actualMap
#print axioms actual_range
end Verification.PrimeStratumPresentation
