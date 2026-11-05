/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualTransverseSmooth
import Verification.ActualTransverseClosed
import Verification.TameCharacterSmooth

/-!
# Actual Transverse Pair Smooth

All actual rings in the transverse smooth pair are smooth: the
character fiber, its affine-line slice, and the whole closed partner layer.
-/
noncomputable section
universe u
namespace Verification.ActualTransversePairSmooth
open Verification.ActualOpenChart Verification.ActualOpenGeometry
open Verification.ExchangeTransverseSlice Verification.ActualTransverseLocalization
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)

omit [Fintype ι] in
theorem fiberIdeal_eq : fiberIdeal (characters R ι κ τ B) =
    PrimitiveCharacters.prescribedIdeal (R := R) (columnMap ι κ τ B)
      Finsupp.basisSingleOne (fun _ => -1) := by
  rw [characters_eq]
  unfold fiberIdeal PrimitiveCharacters.prescribedIdeal
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  simp only [LocalExchangeSmooth.characterUnits,MonoidHom.coe_toHomUnits,
    Units.val_neg,Units.val_one,map_neg,map_one,sub_neg_eq_add,add_comm]
  rfl

variable (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0)
variable (hf : Function.Injective (columnMap ι κ τ B))
variable {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range (columnMap ι κ τ B)) κ n)
variable (he : ∀ i, IsUnit ((s.a i).natAbs : R))

include hf he in
omit [Fintype ι] in
theorem fiber_smooth_tame : Algebra.Smooth R (Fiber (characters R ι κ τ B)) := by
  change Algebra.Smooth R (_ ⧸ fiberIdeal (characters R ι κ τ B))
  rw [fiberIdeal_eq]
  exact TameCharacterSmooth.smith_prescribed_smooth (columnMap ι κ τ B) hf
    Finsupp.basisSingleOne s (fun _ => -1) he

include hf he in
omit [Fintype ι] in
theorem slice_smooth_tame : Algebra.Smooth R (Slice (characters R ι κ τ B)) := by
  letI := fiber_smooth_tame R ι κ τ B hf s he
  letI : Algebra.Smooth (Fiber (characters R ι κ τ B)) (Slice (characters R ι κ τ B)) := {}
  exact Algebra.Smooth.comp R (Fiber (characters R ι κ τ B)) (Slice (characters R ι κ τ B))

include hB hf he in
theorem closed_smooth_tame (v : ι) : Algebra.Smooth R (ClosedSource R ι κ τ j B v) := by
  letI := fiber_smooth_tame R ι κ τ B hf s he
  letI : Algebra.Smooth (Fiber (characters R ι κ τ B)) (MvPolynomial ι (Fiber (characters R ι κ τ B))) := {}
  letI : Algebra.Smooth R (MvPolynomial ι (Fiber (characters R ι κ τ B))) :=
    Algebra.Smooth.comp R (Fiber (characters R ι κ τ B)) _
  exact Algebra.Smooth.of_equiv (ActualTransverseClosed.affineEquiv R ι κ τ j B v hB).symm

include hB hf in
theorem pair_smooth_AS (hs : FreezingLattice.Saturated (LinearMap.range (columnMap ι κ τ B)))
    (v : ι) : Algebra.Smooth R (Fiber (characters R ι κ τ B)) ∧
      Algebra.Smooth R (Slice (characters R ι κ τ B)) ∧
      Algebra.Smooth R (ClosedSource R ι κ τ j B v) := by
  obtain ⟨n,s⟩ := (LinearMap.range (columnMap ι κ τ B)).smithNormalForm Finsupp.basisSingleOne
  have he : ∀ i, IsUnit ((s.a i).natAbs : R) := by
    intro i
    simp only [SaturatedSmith.coefficient_natAbs s hs,Nat.cast_one,isUnit_one]
  exact ⟨fiber_smooth_tame R ι κ τ B hf s he,slice_smooth_tame R ι κ τ B hf s he,
    closed_smooth_tame R ι κ τ j B hB hf s he v⟩

#print axioms fiberIdeal_eq
#print axioms fiber_smooth_tame
#print axioms slice_smooth_tame
#print axioms closed_smooth_tame
#print axioms pair_smooth_AS
end Verification.ActualTransversePairSmooth
