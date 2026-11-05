/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StandardLineThomContraction
import Verification.LocalizedTorusContraction

/-!
# Actual Standard Line Contraction

The actual transverse contraction is literally the standard line
construction over its proved smooth character fiber. This comparison is
proved from the definitions, not supplied as a compatibility hypothesis.
-/
noncomputable section
namespace Verification.ActualStandardLineContraction
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite CochainComplex
open Verification.ActualOpenChart Verification.ActualOpenGeometry Verification.ExchangeTransverseSlice
universe u w
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]
variable (inc : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
variable (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0) (v : ι)
variable (hf : Function.Injective (columnMap ι κ τ B))
variable (hs : FreezingLattice.Saturated (LinearMap.range (columnMap ι κ τ B)))
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
variable [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]
variable (L : DerivedCategory C ⥤ D) [L.CommShift ℤ] [L.IsTriangulated]
variable (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ CochainComplex C ℤ)
variable (T : (Under (CommRingCat.of R))ᵒᵖ ⥤ D)
variable (P : LocalizedPrincipalPurity.Standard L R F T)
local notation "Fib" => Fiber (characters R ι κ τ B)
variable [hline : IsIso (L.map (DerivedCategory.Q.map (ActualTransverseBasepoint.lineProjection R ι κ τ B F)))]

def standardIso : T.obj (op (CommRingCat.mkUnder (CommRingCat.of R) Fib)) ≅
    L.obj (DerivedCategory.Q.obj ((kernel (ActualTransverseBasepoint.projection R ι κ τ B F))⟦(1 : ℤ)⟧)) := by
  letI := (ActualTransversePairSmooth.pair_smooth_AS R ι κ τ inc B hB hf hs v).1
  letI : IsIso (L.map (DerivedCategory.Q.map (StandardLineThomContraction.lineProjection R Fib F))) := hline
  exact StandardLineThomContraction.thomIso R Fib L F T P

theorem actual_eq_standard :
    LocalizedTorusContraction.thomContractionIso R ι κ τ inc B hB v hf hs L F T P =
      standardIso R ι κ τ inc B hB v hf hs L F T P := by
  rfl

#print axioms standardIso
#print axioms actual_eq_standard
end Verification.ActualStandardLineContraction
