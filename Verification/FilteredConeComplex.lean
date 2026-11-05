/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.TransverseDerivedBoundary

/-!
# Filtered Cone Complex

The cellular row of an actual filtered complex. Successive relative
objects are literal mapping cones, and the differential is their connecting
map followed by inclusion into the preceding cone. Its square is proved
zero before taking homology, so the resulting chain complex has no supplied
cellular differential or square-zero hypothesis.
-/
noncomputable section
namespace Verification.FilteredConeComplex
open CategoryTheory CategoryTheory.Limits CochainComplex
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C]

section Connecting
variable {A B E : CochainComplex C ℤ}

def connecting (f : A ⟶ B⟦(1 : ℤ)⟧) (a b : ℤ) (h : 1+a=b) :
    A.homology a ⟶ B.homology b :=
  (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) a).map f ≫
    (CochainComplex.ShiftSequence.shiftIso C 1 a b h).hom.app B

omit [HasBinaryBiproducts C] in
theorem connecting_squared (f : A ⟶ B⟦(1 : ℤ)⟧) (g : B ⟶ E⟦(1 : ℤ)⟧)
    (hfg : f ≫ g⟦(1 : ℤ)⟧' = 0) (a b c : ℤ) (hab : 1+a=b) (hbc : 1+b=c) :
    connecting f a b hab ≫ connecting g b c hbc = 0 := by
  simp only [connecting,Category.assoc]
  rw [← reassoc_of% (CochainComplex.ShiftSequence.shiftIso C 1 a b hab).hom.naturality g]
  change (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) a).map f ≫
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) a).map (g⟦(1 : ℤ)⟧') ≫ _ = 0
  rw [← Category.assoc,← CategoryTheory.Functor.map_comp,hfg,Functor.map_zero,zero_comp]

end Connecting

variable (F : ℕ ⥤ CochainComplex C ℤ)

def inclusion (p : ℕ) : F.obj p ⟶ F.obj (p+1) := F.map (homOfLE (Nat.le_succ p))

def relative (p : ℕ) : CochainComplex C ℤ := mappingCone (inclusion F p)

def boundary (p : ℕ) : relative F (p+1) ⟶ (relative F p)⟦(1 : ℤ)⟧ :=
  TransverseConeBoundary.boundary (inclusion F (p+1)) ≫
    (mappingCone.inr (inclusion F p))⟦(1 : ℤ)⟧'

theorem inr_boundary (p : ℕ) : mappingCone.inr (inclusion F p) ≫
    TransverseConeBoundary.boundary (inclusion F p) = 0 := by
  ext n
  exact TransverseConeBoundary.boundary_right (inclusion F p) n

theorem boundary_squared (p : ℕ) : boundary F (p+1) ≫ (boundary F p)⟦(1 : ℤ)⟧' = 0 := by
  simp only [boundary,CategoryTheory.Functor.map_comp,Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc,inr_boundary,Functor.map_zero,zero_comp,comp_zero]

def cell (p : ℕ) : C := (relative F p).homology (-(p : ℤ))

def differential (p : ℕ) : cell F (p+1) ⟶ cell F p :=
  connecting (boundary F p) (-((p+1 : ℕ) : ℤ)) (-(p : ℤ)) (by omega)

theorem differential_squared (p : ℕ) : differential F (p+1) ≫ differential F p = 0 :=
  connecting_squared _ _ (boundary_squared F p) _ _ _ _ _

/-- The actual cellular chain row associated to the supplied filtered chains. -/
def complex : ChainComplex C ℕ := ChainComplex.of (cell F) (differential F) (differential_squared F)

theorem complex_d (p : ℕ) : (complex F).d (p+1) p = differential F p := ChainComplex.of_d _ _ _ _

#print axioms connecting
#print axioms connecting_squared
#print axioms inclusion
#print axioms relative
#print axioms boundary
#print axioms inr_boundary
#print axioms boundary_squared
#print axioms cell
#print axioms differential
#print axioms differential_squared
#print axioms complex
#print axioms complex_d
end Verification.FilteredConeComplex
