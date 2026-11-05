/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarActualOpenConormal
import Verification.ScalarLocalFlat
import Verification.ScalarLocalPoint

/-!
# Scalar Actual Open Regular

Full regularity of the original AS chart coordinates over any nonzero
coefficient ring. Both flatness and properness of the coordinate ideal
are proved, with no assumed nonempty zero layer.
-/
noncomputable section
universe u
namespace Verification.ScalarActualOpenRegular
open MvPolynomial Verification.ScalarActualOpenChart Verification.ScalarActualOpenGeometry
open Verification.ScalarActualOpenConormal
open Verification.ActualOpenGeometry (columnMap)
open RingTheory.Sequence
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]
variable (a b : (ι ⊕ τ) → Rˣ) (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
variable (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0)
variable (hf : Function.Injective (columnMap ι κ τ B))
variable (hs : FreezingLattice.Saturated (LinearMap.range (columnMap ι κ τ B)))
include hB hf hs

theorem parameter_flat : Module.Flat (MvPolynomial ι R) (GlobalOpen R ι κ τ a b j B) := by
  letI : Module.Flat (MvPolynomial ι R)
      (LocalExchangeSmooth.LocalAlgebra (characters R ι κ τ a b B)) := by
    rw [characters_eq]
    exact ScalarLocalFlat.parameters_flat (columnMap ι κ τ B)
      (fun i => a (Sum.inl i) * (b (Sum.inl i))⁻¹) Finsupp.basisSingleOne hf hs
  exact Module.Flat.of_linearEquiv (globalParameterEquiv R ι κ τ a b j B hB).toLinearEquiv

theorem zero_point : ∃ p : GlobalOpen R ι κ τ a b j B →ₐ[R] R,
    ∀ i, p (globalCoordinate R ι κ τ a b j B i) = 0 := by
  have hp : ∃ p : LocalExchangeSmooth.LocalAlgebra (characters R ι κ τ a b B) →ₐ[R] R,
      ∀ i, p (LocalExchangeSmooth.x (characters R ι κ τ a b B) i) = 0 := by
    rw [characters_eq]
    obtain ⟨p,hp,_⟩ := ScalarLocalPoint.zero_point (columnMap ι κ τ B)
      (fun i => a (Sum.inl i) * (b (Sum.inl i))⁻¹) hf hs
    exact ⟨p,hp⟩
  obtain ⟨p,hp⟩ := hp
  refine ⟨p.comp (globalOpenEquiv R ι κ τ a b j B hB).toAlgHom,fun i => ?_⟩
  change p (globalOpenEquiv R ι κ τ a b j B hB (globalCoordinate R ι κ τ a b j B i)) = 0
  rw [globalOpenEquiv_coordinate,hp]

theorem zeroLayer_nontrivial [Nontrivial R] : Nontrivial (ZeroLayer R ι κ τ a b j B) := by
  obtain ⟨p,hp⟩ := zero_point R ι κ τ a b j B hB hf hs
  let q : ZeroLayer R ι κ τ a b j B →+* R :=
    Ideal.Quotient.lift (zeroIdeal R ι κ τ a b j B) p.toRingHom (by
      change zeroIdeal R ι κ τ a b j B ≤ RingHom.ker p.toRingHom
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact hp i)
  exact q.domain_nontrivial

theorem coordinates_weaklyRegular (l : List ι) (hl : l.Nodup) :
    IsWeaklyRegular (GlobalOpen R ι κ τ a b j B) (l.map (globalCoordinate R ι κ τ a b j B)) := by
  letI := parameter_flat R ι κ τ a b j B hB hf hs
  simpa only [globalParameter_X] using
    PolynomialRegularSequence.flat_variables_weaklyRegular R ι (GlobalOpen R ι κ τ a b j B) l hl

theorem coordinates_regular [Nontrivial R] (l : List ι) (hl : l.Nodup) :
    IsRegular (GlobalOpen R ι κ τ a b j B) (l.map (globalCoordinate R ι κ τ a b j B)) := by
  letI := zeroLayer_nontrivial R ι κ τ a b j B hB hf hs
  have hproper : zeroIdeal R ι κ τ a b j B ≠ ⊤ :=
    Ideal.Quotient.zero_ne_one_iff.mp (zero_ne_one : (0 : ZeroLayer R ι κ τ a b j B) ≠ 1)
  have hlle : Ideal.ofList (l.map (globalCoordinate R ι κ τ a b j B)) ≤ zeroIdeal R ι κ τ a b j B := by
    apply Ideal.span_le.mpr
    rintro z hz
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz
    exact Ideal.subset_span (Set.mem_range_self i)
  have hlproper : Ideal.ofList (l.map (globalCoordinate R ι κ τ a b j B)) ≠ ⊤ := by
    intro ht
    exact hproper (top_unique (ht ▸ hlle))
  refine ⟨coordinates_weaklyRegular R ι κ τ a b j B hB hf hs l hl,?_⟩
  simpa only [Ideal.smul_eq_mul,Ideal.mul_top] using hlproper.symm

#print axioms parameter_flat
#print axioms zero_point
#print axioms zeroLayer_nontrivial
#print axioms coordinates_weaklyRegular
#print axioms coordinates_regular
end Verification.ScalarActualOpenRegular
