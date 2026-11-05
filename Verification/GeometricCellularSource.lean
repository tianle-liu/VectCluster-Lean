/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimeSchemeFiltration
import Verification.CellularSections
import Verification.ActualFramedContraction

/-!
# Geometric Cellular Source

A single genuine scheme-valued chains theory supplies both the global
cellular source and the local transverse calculations. In particular the
global source is not a renamed algebraic matrix complex. Any later comparison
with that matrix must identify these actual filtered-cone differentials.
-/
noncomputable section
namespace Verification.GeometricCellularSource
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
variable (R : Type) [CommRing R]

def affineSchemes : (Under (CommRingCat.of R))ᵒᵖ ⥤ Scheme :=
  (Under.forget (CommRingCat.of R)).op ⋙ Scheme.Spec

variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C]
variable (F : Scheme ⥤ CochainComplex C ℤ)

def affineChains : (Under (CommRingCat.of R))ᵒᵖ ⥤ CochainComplex C ℤ := affineSchemes R ⋙ F

variable (κ : Type) [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)

def source : ChainComplex C ℕ := PrimeSchemeFiltration.actualCellular F R κ n B

def sections (M : C) : CochainComplex AddCommGrp ℕ := CellularSections.complex (source R F κ n B) M

theorem sections_d (M : C) (p : ℕ) (a : (source R F κ n B).X p ⟶ M) :
    ((sections R F κ n B M).d p (p+1)).hom a =
      (source R F κ n B).d (p+1) p ≫ a := CellularSections.complex_d _ _ _ _

def coefficientMap {M N : C} (f : M ⟶ N) : sections R F κ n B M ⟶ sections R F κ n B N :=
  CellularSections.coefficientMap _ _ f

#print axioms affineSchemes
#print axioms affineChains
#print axioms source
#print axioms sections
#print axioms sections_d
#print axioms coefficientMap
end Verification.GeometricCellularSource
