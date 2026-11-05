/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalStrictBoundaryConjugacy
import Verification.ActualGlobalBoundary

/-!
# Original Strict Boundary Geometry

The blocks of the actual strict coefficient differential retain the
literal global cone blocks under the fixed purity/excision comparisons.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
namespace Verification.OriginalStrictBoundaryGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.ExchangeOpenCover Verification.IndependentBasicOpen
open Verification.IndependentOpenCoordinates Verification.GlobalExchangeSmooth
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D]
variable [HasZeroObject D] [HasShift D ℤ] [∀ q : ℤ, (CategoryTheory.shiftFunctor D q).Additive] [Pretriangulated D]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)
variable (R κ : Type) [CommRing R] [Nontrivial R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (P : LocalizedCoordinatePurity.Standard L R G)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hf : ∀ I, Independent (laterWeights κ n B) I → Function.Injective (selectedMap κ n B I))
variable (hs : ∀ I, Independent (laterWeights κ n B) I →
  FreezingLattice.Saturated (LinearMap.range (selectedMap κ n B I)))

local notation "A₀" => Global R κ n B
local notation "xs" => fun j : Fin n => initial R κ n B (Sum.inl j)
local notation "Allowed" => Independent (laterWeights κ n B)
local notation "Fil" => PrimeSchemeFiltration.filteredChains A₀ xs G

omit [HasZeroObject D] [HasShift D ℤ]
  [∀ q : ℤ, (CategoryTheory.shiftFunctor D q).Additive] [Pretriangulated D]
  [L.CommShift ℤ] [L.IsTriangulated] in
theorem source_transport (p : ℕ) (j : ActualCellThom.Index κ n B p) :
    biproduct.ι (fun i : ActualCellThom.Index κ n B p => L.obj (ActualCellThom.localThom G R κ n B p i)) j ≫
      (LocalizedActualCellThom.relativeIso L G E R κ n B P hpos hneg hsupport hf hs p).inv =
    (LocalizedActualCellThom.localIso L G R κ n B P hpos hneg hsupport hf hs p j).inv ≫
      L.map (biproduct.ι (PrimeLayerExcision.localRelative A₀ (Fin n) xs Allowed G p) j ≫
        (PrimeLayerExcision.actualRelativeIso G E R κ n B hpos hneg hsupport p).hom) := by
  simp only [LocalizedActualCellThom.relativeIso,Iso.trans_inv,Iso.symm_inv,
    Functor.mapIso_inv,biproduct.mapIso_inv,Category.assoc,biproduct.ι_map_assoc,
    Functor.mapBiproduct_inv,biproduct.ι_desc_assoc,← Functor.map_comp]

omit [HasZeroObject D] [HasShift D ℤ]
  [∀ q : ℤ, (CategoryTheory.shiftFunctor D q).Additive] [Pretriangulated D]
  [L.CommShift ℤ] [L.IsTriangulated] in
theorem target_transport (p : ℕ) (i : ActualCellThom.Index κ n B p) :
    (LocalizedActualCellThom.relativeIso L G E R κ n B P hpos hneg hsupport hf hs p).hom ≫
      biproduct.π (fun i : ActualCellThom.Index κ n B p => L.obj (ActualCellThom.localThom G R κ n B p i)) i =
    L.map ((PrimeLayerExcision.actualRelativeIso G E R κ n B hpos hneg hsupport p).inv ≫
      biproduct.π (PrimeLayerExcision.localRelative A₀ (Fin n) xs Allowed G p) i) ≫
        (LocalizedActualCellThom.localIso L G R κ n B P hpos hneg hsupport hf hs p i).hom := by
  simp only [LocalizedActualCellThom.relativeIso,Iso.trans_hom,Iso.symm_hom,
    Functor.mapIso_hom,biproduct.mapIso_hom,Category.assoc,biproduct.map_π,
    Functor.mapBiproduct_hom,biproduct.lift_π_assoc,← Functor.map_comp]
  have hp := biproduct.lift_π (fun j : ActualCellThom.Index κ n B p =>
    L.map (biproduct.π (PrimeLayerExcision.localRelative A₀ (Fin n) xs Allowed G p) j)) i
  simpa only [Category.assoc,Functor.map_comp] using
    congrArg (fun t => L.map (PrimeLayerExcision.actualRelativeIso G E R κ n B hpos hneg hsupport p).inv ≫
      t ≫ (LocalizedActualCellThom.localIso L G R κ n B P hpos hneg hsupport hf hs p i).hom) hp

omit [Preadditive D] [HasFiniteBiproducts D] [HasZeroObject D]
  [∀ q : ℤ, (CategoryTheory.shiftFunctor D q).Additive] [Pretriangulated D]
  [L.Additive] [L.IsTriangulated] [Nontrivial R] in
theorem boundary_global (p : ℕ) :
    StrictCellularBoundary.positiveBoundary L Fil p =
      L.map (PrimeGlobalBoundary.globalBoundary A₀ (Fin n) xs G p) ≫
        (L.commShiftIso (1 : ℤ)).hom.app
          (DerivedCategory.Q.obj (FilteredConeComplex.relative Fil p)) := by
  simp only [StrictCellularBoundary.positiveBoundary,PrimeGlobalBoundary.globalBoundary,
    Functor.comp_map,Functor.map_comp,Functor.commShiftIso_comp_hom_app,Category.assoc]

def positiveBlock (p : ℕ) (j : ActualCellThom.Index κ n B (p+1))
    (i : ActualCellThom.Index κ n B p) :
    L.obj (ActualCellThom.localThom G R κ n B (p+1) j) ⟶
      (L.obj (ActualCellThom.localThom G R κ n B p i))⟦(1 : ℤ)⟧ :=
  biproduct.ι (fun j : ActualCellThom.Index κ n B (p+1) =>
      L.obj (ActualCellThom.localThom G R κ n B (p+1) j)) j ≫
    (LocalizedActualCellThom.relativeIso L G E R κ n B P hpos hneg hsupport hf hs (p+1)).inv ≫
      StrictCellularBoundary.positiveBoundary L Fil p ≫
        ((LocalizedActualCellThom.relativeIso L G E R κ n B P hpos hneg hsupport hf hs p).hom ≫
          biproduct.π (fun i : ActualCellThom.Index κ n B p =>
            L.obj (ActualCellThom.localThom G R κ n B p i)) i)⟦(1 : ℤ)⟧'

omit [HasZeroObject D] [∀ q : ℤ, (CategoryTheory.shiftFunctor D q).Additive]
  [Pretriangulated D] [L.IsTriangulated] in
theorem positiveBlock_eq (p : ℕ) (j : ActualCellThom.Index κ n B (p+1))
    (i : ActualCellThom.Index κ n B p) :
    positiveBlock L G E R κ n B P hpos hneg hsupport hf hs p j i =
      (LocalizedActualCellThom.localIso L G R κ n B P hpos hneg hsupport hf hs (p+1) j).inv ≫
        L.map (ActualGlobalBoundary.block R κ n B G E hpos hneg hsupport p j i) ≫
          (L.commShiftIso (1 : ℤ)).hom.app
            (PrimeLayerExcision.localRelative A₀ (Fin n) xs Allowed G p i) ≫
          ((LocalizedActualCellThom.localIso L G R κ n B P hpos hneg hsupport hf hs p i).hom)⟦(1 : ℤ)⟧' := by
  unfold positiveBlock
  rw [← Category.assoc,source_transport,target_transport,boundary_global,
    ActualGlobalBoundary.block_eq]
  simp only [Functor.map_comp,Category.assoc]
  simp only [L.commShiftIso_hom_naturality_assoc]

omit [Preadditive D] [HasFiniteBiproducts D] [HasZeroObject D]
  [∀ q : ℤ, (CategoryTheory.shiftFunctor D q).Additive] [Pretriangulated D] in
theorem deshift_naturality {X Y : D} (f : X ⟶ Y) :
    (f⟦(1 : ℤ)⟧')⟦(-1 : ℤ)⟧' ≫ (shiftShiftNeg Y (1 : ℤ)).hom =
      (shiftShiftNeg X (1 : ℤ)).hom ≫ f := by
  have h := (shiftFunctorCompIsoId D (1 : ℤ) (-1) (by omega)).hom.naturality f
  simpa only [shiftShiftNeg,shiftEquiv,shiftEquiv',Iso.symm_hom,Iso.app_hom,
    Functor.comp_map,Functor.id_map] using h

omit [HasZeroObject D] [Pretriangulated D] [L.IsTriangulated] in
theorem block_positive (p : ℕ) (j : ActualCellThom.Index κ n B (p+1))
    (i : ActualCellThom.Index κ n B p) :
    OriginalStrictBoundaryConjugacy.block L G R κ n B hpos hneg hsupport hf hs E P p j i =
      (positiveBlock L G E R κ n B P hpos hneg hsupport hf hs p j i)⟦(-1 : ℤ)⟧' ≫
        (shiftShiftNeg (L.obj (ActualCellThom.localThom G R κ n B p i)) (1 : ℤ)).hom := by
  let s := biproduct.ι (fun j : ActualCellThom.Index κ n B (p+1) =>
      L.obj (ActualCellThom.localThom G R κ n B (p+1) j)) j ≫
    (LocalizedActualCellThom.relativeIso L G E R κ n B P hpos hneg hsupport hf hs (p+1)).inv
  let t := (LocalizedActualCellThom.relativeIso L G E R κ n B P hpos hneg hsupport hf hs p).hom ≫
    biproduct.π (fun i : ActualCellThom.Index κ n B p => L.obj (ActualCellThom.localThom G R κ n B p i)) i
  change s⟦(-1 : ℤ)⟧' ≫ StrictCellularBoundary.ambientBoundary L Fil p ≫ t = _
  have hp : positiveBlock L G E R κ n B P hpos hneg hsupport hf hs p j i =
      s ≫ StrictCellularBoundary.positiveBoundary L Fil p ≫ t⟦(1 : ℤ)⟧' := by
    dsimp only [s,t,positiveBlock]
    rw [Category.assoc]
  rw [hp]
  rw [StrictCellularBoundary.ambientBoundary_positive]
  simp only [Functor.map_comp,Category.assoc,deshift_naturality]

theorem positive_nonincident (p : ℕ) (j : ActualCellThom.Index κ n B (p+1))
    (i : ActualCellThom.Index κ n B p) (h : ¬ i.val ⊆ j.val) :
    positiveBlock L G E R κ n B P hpos hneg hsupport hf hs p j i = 0 := by
  rw [positiveBlock_eq,ActualGlobalBoundary.nonincident_zero R κ n B G E hpos hneg hsupport p j i h]
  simp only [Functor.map_zero,zero_comp,comp_zero]

theorem nonincident (p : ℕ) (j : ActualCellThom.Index κ n B (p+1))
    (i : ActualCellThom.Index κ n B p) (h : ¬ i.val ⊆ j.val) :
    OriginalStrictBoundaryConjugacy.block L G R κ n B hpos hneg hsupport hf hs E P p j i = 0 := by
  rw [block_positive,positive_nonincident L G E R κ n B P hpos hneg hsupport hf hs p j i h]
  simp only [Functor.map_zero,zero_comp]

#print axioms deshift_naturality
#print axioms block_positive
#print axioms positive_nonincident
#print axioms nonincident
#print axioms boundary_global
#print axioms positiveBlock
#print axioms positiveBlock_eq
#print axioms source_transport
#print axioms target_transport
end Verification.OriginalStrictBoundaryGeometry
