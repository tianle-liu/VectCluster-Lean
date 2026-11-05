/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictProjectiveModel
import Verification.PrimeSchemeFiltration
import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Strict Finite Filtration

Finite induction on actual filtered cochain complexes. Each successor
uses its literal mapping-cone distinguished triangle and the proved strict
cone closure. The raw derived chains are mapped to a separate ambient triangulated category
by L. The endpoint is transported along the actual exhaustive
open-scheme isomorphism, not along an assumed ambient quasi-isomorphism.
-/
noncomputable section
namespace Verification.StrictFiniteFiltration
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Verification.StrictProjectiveModel
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasBinaryBiproducts A]
variable [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
variable [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ] [J.IsTriangulated]
variable (L : DerivedCategory C ⥤ D) [L.CommShift ℤ] [L.IsTriangulated]
variable (H : ChainRepresentability (A := A))
variable (F : ℕ ⥤ CochainComplex C ℤ)

def stepTriangle (p : ℕ) : Triangle D :=
  L.mapTriangle.obj (DerivedCategory.Q.mapTriangle.obj
    (CochainComplex.mappingCone.triangle (FilteredConeComplex.inclusion F p)))

theorem step_distinguished (p : ℕ) : stepTriangle L F p ∈ distTriang D :=
  L.map_distinguished _ ((DerivedCategory.mem_distTriang_iff _).mpr
    ⟨_,_,FilteredConeComplex.inclusion F p,⟨Iso.refl _⟩⟩)

def successor (p : ℕ) (M : Model J (L.obj (DerivedCategory.Q.obj (F.obj p))))
    (cell : Model J (L.obj (DerivedCategory.Q.obj (FilteredConeComplex.relative F p)))) :
    Model J (L.obj (DerivedCategory.Q.obj (F.obj (p+1)))) :=
  extension J H (step_distinguished L F p) M cell

include H in
theorem stages_exist (N : ℕ) (base : Nonempty (Model J (L.obj (DerivedCategory.Q.obj (F.obj 0)))))
    (cells : ∀ p < N, Nonempty (Model J (L.obj (DerivedCategory.Q.obj (FilteredConeComplex.relative F p))))) :
    ∀ p ≤ N, Nonempty (Model J (L.obj (DerivedCategory.Q.obj (F.obj p)))) := by
  intro p
  induction p with
  | zero => exact fun _ => base
  | succ p ih =>
      intro hp
      obtain ⟨M⟩ := ih (by omega)
      obtain ⟨cell⟩ := cells p (by omega)
      exact ⟨successor J L H F p M cell⟩

def endpoint (N : ℕ) (hzero : IsZero (L.obj (DerivedCategory.Q.obj (F.obj 0))))
    (cells : ∀ p < N, Model J (L.obj (DerivedCategory.Q.obj (FilteredConeComplex.relative F p)))) :
    Model J (L.obj (DerivedCategory.Q.obj (F.obj N))) :=
  (stages_exist J L H F N ⟨ofIsZero J _ hzero⟩ (fun p hp => ⟨cells p hp⟩) N le_rfl).some

open AlgebraicGeometry
variable (R : Type) [CommRing R] {V : Type} [Fintype V] [DecidableEq V] (x : V → R)
variable (G : Scheme ⥤ CochainComplex C ℤ)

def globalModel
    (hzero : IsZero (L.obj (DerivedCategory.Q.obj ((PrimeSchemeFiltration.filteredChains R x G).obj 0))))
    (cells : ∀ p < Fintype.card V + 1, Model J (L.obj (DerivedCategory.Q.obj
      (FilteredConeComplex.relative (PrimeSchemeFiltration.filteredChains R x G) p)))) :
    Model J (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of R))))) :=
  ofIso J (L.mapIso (DerivedCategory.Q.mapIso (G.mapIso (PrimeSchemeFiltration.exhaustiveIso R x)))).symm
    (endpoint J L H (PrimeSchemeFiltration.filteredChains R x G) (Fintype.card V + 1) hzero cells)

#print axioms stepTriangle
#print axioms step_distinguished
#print axioms successor
#print axioms stages_exist
#print axioms endpoint
#print axioms globalModel
end Verification.StrictFiniteFiltration
