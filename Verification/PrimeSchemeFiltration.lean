/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimeCoordinateFiltration
import Verification.FilteredConeComplex
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Prime Scheme Filtration

Actual open subschemes, rather than renamed formal cells, underlie the
cellular source. The coefficient chains functor is supplied independently;
the source is constructed from its values on the original zero-coordinate
filtration and literal successive mapping cones.
-/
noncomputable section
namespace Verification.PrimeSchemeFiltration
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
variable (A : Type*) [CommRing A] {V : Type*} [Fintype V] [DecidableEq V]
variable (x : V → A)

def stageOpen (r : ℕ) : (Spec (CommRingCat.of A)).Opens := PrimeCoordinateFiltration.stage x r

def stageScheme (r : ℕ) : Scheme := (stageOpen A x r).toScheme

def stages : ℕ ⥤ Scheme :=
  (PrimeCoordinateFiltration.stage_mono x).functor ⋙
    (Spec (CommRingCat.of A)).restrictFunctor ⋙ Over.forget (Spec (CommRingCat.of A))

theorem stages_obj (r : ℕ) : (stages A x).obj r = stageScheme A x r := rfl

theorem stageOpen_exhaustive : stageOpen A x (Fintype.card V + 1) = ⊤ :=
  PrimeCoordinateFiltration.stage_exhaustive x

def exhaustiveIso : (stages A x).obj (Fintype.card V + 1) ≅ Spec (CommRingCat.of A) :=
  eqToIso (congrArg Scheme.Opens.toScheme (stageOpen_exhaustive A x)) ≪≫
    (Spec (CommRingCat.of A)).topIso

variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C]
variable (F : Scheme ⥤ CochainComplex C ℤ)

def filteredChains : ℕ ⥤ CochainComplex C ℤ := stages A x ⋙ F

def cellular : ChainComplex C ℕ := FilteredConeComplex.complex (filteredChains A x F)

/-- The terms are actual homology of the actual adjacent open-scheme cones. -/
theorem cellular_term (p : ℕ) : (cellular A x F).X p =
    (CochainComplex.mappingCone
      ((filteredChains A x F).map (homOfLE (Nat.le_succ p)))).homology (-(p : ℤ)) := rfl

theorem cellular_boundary (p : ℕ) : (cellular A x F).d (p+1) p =
    FilteredConeComplex.differential (filteredChains A x F) p :=
  FilteredConeComplex.complex_d _ _

section Actual
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)

def actualCellular : ChainComplex C ℕ :=
  cellular (FrozenAcyclicCover.Global R κ n B)
    (fun i => FrozenAcyclicCover.initial R κ n B (Sum.inl i)) F

end Actual
#print axioms stageOpen
#print axioms stageScheme
#print axioms stages
#print axioms stages_obj
#print axioms stageOpen_exhaustive
#print axioms exhaustiveIso
#print axioms filteredChains
#print axioms cellular
#print axioms cellular_term
#print axioms cellular_boundary
#print axioms actualCellular
end Verification.PrimeSchemeFiltration
