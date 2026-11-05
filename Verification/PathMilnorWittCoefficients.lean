/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathCoefficientRing
import Verification.MilnorWittSymbolRelations

/-!
# Path Milnor Witt Coefficients

The manuscript's literal coefficient ring acts on an ordinary (possibly
noncommutative) Milnor-Witt symbol ring through its center. Its defining
relations follow from the ordinary coefficient identities, not an additional
path coefficient realization assumption.
-/
noncomputable section
namespace Verification.PathMilnorWittCoefficients
open Verification.MilnorWittSymbolRelations
variable {A : Type*} [Ring A] (D : Coefficients A)

def centerG : Subring.center A :=
  ⟨D.g,Subring.mem_center_iff.mpr (fun x => (D.central_g x).eq.symm)⟩

def centerRho : Subring.center A :=
  ⟨D.rho,Subring.mem_center_iff.mpr (fun x => (D.central_rho x).eq.symm)⟩

theorem centerG_square : centerG D * centerG D = 1 := Subtype.ext D.g_square

theorem centerRho_relation : (1+centerG D)*centerRho D=0 := by
  apply Subtype.ext
  change (1+D.g)*D.rho=0
  rw [add_mul,one_mul,D.g_rho,add_neg_cancel]

def centralRealize : Verification.PathCoefficientRing.Coeff →+* Subring.center A :=
  Verification.PathCoefficientRing.realize (centerG D) (centerRho D)
    (centerG_square D) (centerRho_relation D)

def realize : Verification.PathCoefficientRing.Coeff →+* A :=
  (Subring.center A).subtype.comp (centralRealize D)

theorem realize_g : realize D Verification.PathCoefficientRing.g = D.g := by
  change (centralRealize D Verification.PathCoefficientRing.g : A)=D.g
  rw [centralRealize,Verification.PathCoefficientRing.realize_g]
  rfl

theorem realize_rho : realize D Verification.PathCoefficientRing.rho = D.rho := by
  change (centralRealize D Verification.PathCoefficientRing.rho : A)=D.rho
  rw [centralRealize,Verification.PathCoefficientRing.realize_rho]
  rfl

theorem central (c : Verification.PathCoefficientRing.Coeff) (a : A) :
    realize D c * a = a * realize D c :=
  (Subring.mem_center_iff.mp (centralRealize D c).property a).symm

def algebra : Algebra Verification.PathCoefficientRing.Coeff A :=
  (realize D).toAlgebra' (central D)

#print axioms centerG
#print axioms centerRho
#print axioms centerG_square
#print axioms centerRho_relation
#print axioms centralRealize
#print axioms realize
#print axioms realize_g
#print axioms realize_rho
#print axioms central
#print axioms algebra
end Verification.PathMilnorWittCoefficients
