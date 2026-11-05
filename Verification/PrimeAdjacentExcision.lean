/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimeAdjacentCharts
import Verification.PrimeLayerExcision
import Verification.OpenFlagBoundary

/-!
# Prime Adjacent Excision

Inside an original J-chart, the preceding relative layer splits by
which single original coordinate is nonzero. All cover and overlap
conditions are proved; uniform open excision supplies only its canonical
map, rather than an assumed matrix decomposition.
-/
noncomputable section
namespace Verification.PrimeAdjacentExcision
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.PrimeCoordinateFiltration Verification.PrimeAdjacentCharts
universe w
variable (A V : Type) [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V → A) (J : Finset V) (r : ℕ) (hr : J.card = r+1)

def previous : (Spec (CommRingCat.of A)).Opens := stage x r ⊓ openBy x J
def current : (Spec (CommRingCat.of A)).Opens := stage x (r+1) ⊓ openBy x J
def edgeChart (v : J) : (Spec (CommRingCat.of A)).Opens := openBy x (J.erase v.val)

theorem previous_le_current : previous A V x J r ≤ current A V x J r :=
  inf_le_inf_right _ (stage_mono x (Nat.le_succ r))

include hr in
theorem edgeChart_le_current (v : J) : edgeChart A V x J v ≤ current A V x J r := by
  change openBy x (J.erase v.val) ≤ stage x (r+1) ⊓ openBy x J
  rw [← hr,puncture_cover]
  exact le_iSup (fun w : J => openBy x (J.erase w.val)) v

include hr in
theorem cover : current A V x J r ≤ previous A V x J r ⊔ ⨆ v : J,edgeChart A V x J v := by
  change stage x (r+1) ⊓ openBy x J ≤ _
  rw [← hr,puncture_cover]
  exact le_sup_right

include hr in
theorem overlap (v w : J) (hvw : v ≠ w) :
    edgeChart A V x J v ⊓ edgeChart A V x J w ≤ previous A V x J r := by
  intro p hp
  refine ⟨?_,chart_erase_le x J v hp.1⟩
  have h := two_chart_overlap x J v w hvw hp
  have he : J.card-1=r := by omega
  simpa only [he] using h

variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)

def edgeCone (v : J) : DerivedCategory C :=
  OpenConeExcision.localCone (Spec (CommRingCat.of A)) (PrimeLayerExcision.openChains A G)
    (previous A V x J r) (edgeChart A V x J) v

def rowArrow := OpenConeExcision.globalArrow (Spec (CommRingCat.of A))
  (PrimeLayerExcision.openChains A G) (previous A V x J r) (current A V x J r)
    (previous_le_current A V x J r)

def assembly : (⨁ fun v : J => edgeCone A V x J r G v) ⟶
    DerivedCategory.Q.obj (mappingCone (rowArrow A V x J r G)) :=
  OpenConeExcision.assembly (Spec (CommRingCat.of A)) (PrimeLayerExcision.openChains A G)
    (previous A V x J r) (current A V x J r) (previous_le_current A V x J r)
      (edgeChart A V x J) (edgeChart_le_current A V x J r hr)

include E in
theorem assembly_isIso : IsIso (assembly A V x J r hr G) :=
  E.isIso_assembly _ _ _ _ J _ _ (cover A V x J r hr) (overlap A V x J r hr)

def relativeIso : (⨁ fun v : J => edgeCone A V x J r G v) ≅
    DerivedCategory.Q.obj (mappingCone (rowArrow A V x J r G)) := by
  letI := assembly_isIso A V x J r hr G E
  exact asIso (assembly A V x J r hr G)

#print axioms previous
#print axioms current
#print axioms edgeChart
#print axioms previous_le_current
#print axioms edgeChart_le_current
#print axioms cover
#print axioms overlap
#print axioms edgeCone
#print axioms rowArrow
#print axioms assembly
#print axioms assembly_isIso
#print axioms relativeIso
end Verification.PrimeAdjacentExcision
