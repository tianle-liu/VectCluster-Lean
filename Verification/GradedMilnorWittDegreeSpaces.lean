/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedMilnorWittHomogeneity

/-!
# Graded Milnor Witt Degree Spaces

Actual homogeneous sections as additive subgroups of the total ring,
with the ordinary degree changes of the three central MW coefficients.
-/
noncomputable section
namespace Verification.GradedMilnorWittDegreeSpaces
open CategoryTheory AlgebraicGeometry
open Verification.GradedSectionTotal Verification.SheafGradedLaurentResidue
open Verification.GradedMilnorWittHomogeneity
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : GradedMilnorWittSheaf.Standard site N)

def space (S : CommRingCat.{0}) (q : ℤ) : AddSubgroup (D.Total S) where
  carrier := Homogeneous site N D S q
  zero_mem' := GradedMilnorWittHomogeneity.zero S q
  add_mem' := GradedMilnorWittHomogeneity.add
  neg_mem' := GradedMilnorWittHomogeneity.neg

def equiv (S : CommRingCat.{0}) (q : ℤ) : Section site N S q ≃+ space site N D S q where
  toFun a := ⟨includeDegree (D.grading S) q a,⟨a,rfl⟩⟩
  invFun a := Classical.choose a.property
  left_inv a := includeDegree_injective (D.grading S) q (Classical.choose_spec (show Homogeneous site N D S q (includeDegree (D.grading S) q a) from ⟨a,rfl⟩))
  right_inv a := Subtype.ext (Classical.choose_spec a.property)
  map_add' a b := Subtype.ext (map_add _ a b)

def weighted {ι : Type*} (S : CommRingCat.{0}) (w : ι → ℤ) (q : ℤ) : AddSubgroup (ι → D.Total S) where
  carrier := fun a => ∀ i,Homogeneous site N D S (q-w i) (a i)
  zero_mem' := fun i => GradedMilnorWittHomogeneity.zero S (q-w i)
  add_mem' := fun ha hb i => GradedMilnorWittHomogeneity.add (ha i) (hb i)
  neg_mem' := fun ha i => GradedMilnorWittHomogeneity.neg (ha i)

variable {site N D}
variable (P : Standard site N D) (S : CommRingCat.{0})
include P

theorem g_mul {q : ℤ} {a : D.Total S} (ha : Homogeneous site N D S q a) :
    Homogeneous site N D S q ((D.symbols S).g*a) := by
  convert GradedMilnorWittHomogeneity.mul P (GradedMilnorWittHomogeneity.g P S) ha using 1
  omega

theorem rho_mul {q : ℤ} {a : D.Total S} (ha : Homogeneous site N D S q a) :
    Homogeneous site N D S (q+1) ((D.symbols S).rho*a) := by
  convert GradedMilnorWittHomogeneity.mul P (GradedMilnorWittHomogeneity.rho P S) ha using 1
  omega

theorem eta_mul {q : ℤ} {a : D.Total S} (ha : Homogeneous site N D S q a) :
    Homogeneous site N D S (q-1) ((D.symbols S).eta*a) := by
  have hη : Homogeneous site N D S (-1) (D.symbols S).eta := ⟨P.etaSection S,P.eta_value S⟩
  convert GradedMilnorWittHomogeneity.mul P hη ha using 1
  omega

#print axioms space
#print axioms equiv
#print axioms weighted
#print axioms g_mul
#print axioms rho_mul
#print axioms eta_mul
end Verification.GradedMilnorWittDegreeSpaces
