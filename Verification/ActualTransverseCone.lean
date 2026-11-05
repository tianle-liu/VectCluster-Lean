/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.TransverseConeBoundary
import Verification.ActualTransverseLocalization
import Mathlib.Algebra.Category.Ring.Under.Basic

/-!
# Actual Transverse Cone

The actual cluster transverse slice, including its actual principal-open
localization, induces a literal map of chain-level localization cones under
any contravariant chain realization. The square and boundary naturality are
proved from the original ring maps, not supplied as comparison hypotheses.
-/
namespace Verification.ActualTransverseCone
open CategoryTheory CategoryTheory.Limits Opposite CochainComplex
open Verification.ActualTransverseSlice Verification.ActualTransverseLocalization
open Verification.ExchangeTransverseSlice Verification.ActualOpenChart
universe u
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
variable (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0) (v : ι)
variable {D : Type*} [Category D] [Preadditive D] [HasBinaryBiproducts D]
variable (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ CochainComplex D ℤ)

noncomputable def ambientOpen :
    F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (OpenSource R ι κ τ j B v))) ⟶
      F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (Intermediate R ι κ τ j B v))) :=
  F.map (IsScalarTower.toAlgHom R (Intermediate R ι κ τ j B v) (OpenSource R ι κ τ j B v)).toUnder.op

noncomputable def sliceOpen :
    F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (OpenTarget R ι κ τ B))) ⟶
      F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (Slice (characters R ι κ τ B)))) :=
  F.map (IsScalarTower.toAlgHom R (Slice (characters R ι κ τ B)) (OpenTarget R ι κ τ B)).toUnder.op

noncomputable def openMap :
    F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (OpenTarget R ι κ τ B))) ⟶
      F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (OpenSource R ι κ τ j B v))) :=
  F.map (localizedSlice R ι κ τ j B hB v).toUnder.op

noncomputable def ambientMap :
    F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (Slice (characters R ι κ τ B)))) ⟶
      F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (Intermediate R ι κ τ j B v))) :=
  F.map (transverseSlice R ι κ τ j B hB v).toUnder.op

omit [HasBinaryBiproducts D] in
/-- The chain square is derived from the literal original localization square. -/
theorem chain_square :
    sliceOpen R ι κ τ B F ≫ ambientMap R ι κ τ j B hB v F =
      openMap R ι κ τ j B hB v F ≫ ambientOpen R ι κ τ j B v F := by
  have h := congrArg (fun f : Intermediate R ι κ τ j B v →ₐ[R] OpenTarget R ι κ τ B =>
    F.map f.toUnder.op) (open_square R ι κ τ j B hB v).symm
  unfold sliceOpen ambientMap openMap ambientOpen
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact h

/-- No cone-map or boundary relation is an external assumption. -/
noncomputable def sliceConeMap :
    mappingCone (sliceOpen R ι κ τ B F) ⟶ mappingCone (ambientOpen R ι κ τ j B v F) :=
  Verification.TransverseConeBoundary.coneMap _ _
    (openMap R ι κ τ j B hB v F) (ambientMap R ι κ τ j B hB v F)
    (chain_square R ι κ τ j B hB v F)

/-- Naturality of the actual localization boundary for the actual cluster slice. -/
theorem actual_boundary_naturality :
    sliceConeMap R ι κ τ j B hB v F ≫
        Verification.TransverseConeBoundary.boundary (ambientOpen R ι κ τ j B v F) =
      Verification.TransverseConeBoundary.boundary (sliceOpen R ι κ τ B F) ≫
        (openMap R ι κ τ j B hB v F)⟦(1 : ℤ)⟧' :=
  Verification.TransverseConeBoundary.boundary_naturality _ _ _ _ _

#print axioms ambientOpen
#print axioms sliceOpen
#print axioms openMap
#print axioms ambientMap
#print axioms chain_square
#print axioms sliceConeMap
#print axioms actual_boundary_naturality
end Verification.ActualTransverseCone
