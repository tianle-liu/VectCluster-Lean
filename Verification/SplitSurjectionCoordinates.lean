/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.EuclideanDomain.Int

/-!
# Split Surjection Coordinates

A surjection of finite integral coordinate lattices gives an actual
coordinate decomposition with its prescribed target coordinates first.
The complement basis and its size are constructed, not assumed.
-/

noncomputable section
namespace Verification.SplitSurjectionCoordinates
open Classical
variable {P Q : Type} [Fintype P] [Fintype Q]
variable (f : (P → ℤ) →ₗ[ℤ] (Q → ℤ)) (hf : Function.Surjective f)

def sectionMap : (Q → ℤ) →ₗ[ℤ] (P → ℤ) :=
  (f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)).choose

omit [Fintype P] in
theorem sectionMap_right : f.comp (sectionMap f hf)=LinearMap.id :=
  (f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)).choose_spec

omit [Fintype P] in
theorem sectionMap_apply (q : Q → ℤ) : f (sectionMap f hf q)=q :=
  LinearMap.congr_fun (sectionMap_right f hf) q

def kernelPart : (P → ℤ) →ₗ[ℤ] LinearMap.ker f :=
  (LinearMap.id-(sectionMap f hf).comp f).codRestrict (LinearMap.ker f) (by
    intro x
    change f (x-sectionMap f hf (f x))=0
    rw [map_sub,sectionMap_apply f hf,sub_self])

def coordinates : (P → ℤ) ≃ₗ[ℤ] ((Q → ℤ) × LinearMap.ker f) where
  toFun x := (f x,kernelPart f hf x)
  invFun y := sectionMap f hf y.1+y.2.val
  left_inv x := by change sectionMap f hf (f x)+(x-sectionMap f hf (f x))=x;abel
  right_inv y := by
    apply Prod.ext
    · change f (sectionMap f hf y.1+y.2.val)=y.1
      rw [map_add,sectionMap_apply f hf,y.2.property,add_zero]
    · apply Subtype.ext
      change sectionMap f hf y.1+y.2.val-sectionMap f hf (f (sectionMap f hf y.1+y.2.val))=y.2.val
      rw [map_add,sectionMap_apply f hf,y.2.property,add_zero]
      abel
  map_add' x y := by apply Prod.ext;exact map_add f x y;exact map_add (kernelPart f hf) x y
  map_smul' a x := by apply Prod.ext;exact f.map_smul a x;exact (kernelPart f hf).map_smul a x

omit [Fintype P] in
theorem first_coordinate (x : P → ℤ) : (coordinates f hf x).1=f x := rfl

include hf in
theorem dimension : Fintype.card Q+Module.finrank ℤ (LinearMap.ker f)=Fintype.card P := by
  have h:=(coordinates f hf).finrank_eq
  simpa only [Module.finrank_prod,Module.finrank_pi] using h.symm

include f hf in
theorem target_card_le : Fintype.card Q≤Fintype.card P := by
  have h:=dimension f hf
  omega

def kernelCoordinates : LinearMap.ker f ≃ₗ[ℤ] (Fin (Fintype.card P-Fintype.card Q) → ℤ) := by
  have hdim : Module.finrank ℤ (LinearMap.ker f)=Fintype.card P-Fintype.card Q := by
    have h:=dimension f hf
    omega
  exact ((Module.finBasis ℤ (LinearMap.ker f)).repr.trans
    (Finsupp.linearEquivFunOnFinite ℤ ℤ _)).trans
      (LinearEquiv.funCongrLeft ℤ ℤ (finCongr hdim).symm)

def standardCoordinates : (P → ℤ) ≃ₗ[ℤ] ((Q → ℤ) × (Fin (Fintype.card P-Fintype.card Q) → ℤ)) :=
  (coordinates f hf).trans ((LinearEquiv.refl ℤ _).prodCongr (kernelCoordinates f hf))

theorem standard_first (x : P → ℤ) : (standardCoordinates f hf x).1=f x := rfl

def standardBasis : Basis (Q ⊕ Fin (Fintype.card P-Fintype.card Q)) ℤ (P → ℤ) :=
  ((Pi.basisFun ℤ Q).prod (Pi.basisFun ℤ (Fin (Fintype.card P-Fintype.card Q)))).map
    (standardCoordinates f hf).symm

theorem standardBasis_quotient (i : Q ⊕ Fin (Fintype.card P-Fintype.card Q)) :
    f (standardBasis f hf i)=Sum.elim (fun q=>Pi.single q (1:ℤ)) (fun _=>0) i := by
  rw [← standard_first f hf]
  simp only [standardBasis,Basis.map_apply,LinearEquiv.apply_symm_apply]
  cases i <;> simp [Basis.prod_apply,Pi.basisFun_apply]

#print axioms sectionMap
#print axioms sectionMap_right
#print axioms sectionMap_apply
#print axioms kernelPart
#print axioms coordinates
#print axioms first_coordinate
#print axioms dimension
#print axioms target_card_le
#print axioms kernelCoordinates
#print axioms standardCoordinates
#print axioms standard_first
#print axioms standardBasis
#print axioms standardBasis_quotient

end Verification.SplitSurjectionCoordinates
