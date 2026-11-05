/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Product Torus Algebra

Separating a split character factor from its complementary torus,
as an algebra equivalence retaining both groups of monomials.
-/
noncomputable section
namespace Verification.ProductTorusAlgebra
open MonoidAlgebra
variable (R H K : Type) [CommRing R] [CommGroup H] [CommGroup K]

abbrev Source := MonoidAlgebra R (H × K)
abbrev Target := MonoidAlgebra (MonoidAlgebra R K) H

def forwardCharacter : (H × K) →* Target R H K where
  toFun a := algebraMap (MonoidAlgebra R K) (Target R H K) (of R K a.2)*
    of (MonoidAlgebra R K) H a.1
  map_one' := by simp; rfl
  map_mul' a b := by simp [mul_mul_mul_comm]

def forward : Source R H K →ₐ[R] Target R H K :=
  lift R (H × K) _ (forwardCharacter R H K)

def coefficientCharacter : K →* Source R H K where
  toFun k := of R (H × K) (1,k)
  map_one' := by simp; rfl
  map_mul' a b := by simp [← map_mul]

def coefficient : MonoidAlgebra R K →ₐ[R] Source R H K :=
  lift R K _ (coefficientCharacter R H K)

def firstCharacter : H →* Source R H K where
  toFun h := of R (H × K) (h,1)
  map_one' := by simp; rfl
  map_mul' a b := by simp [← map_mul]

def backward : Target R H K →ₐ[R] Source R H K :=
  liftNCAlgHom (coefficient R H K) (firstCharacter R H K) (fun _ _ => Commute.all _ _)

theorem forward_of (h : H) (k : K) :
    forward R H K (of R (H × K) (h,k))=
      algebraMap (MonoidAlgebra R K) (Target R H K) (of R K k)*of (MonoidAlgebra R K) H h :=
  lift_of _ _

theorem backward_single (h : H) (a : MonoidAlgebra R K) :
    backward R H K (Finsupp.single h a)=coefficient R H K a*of R (H × K) (h,1) := by
  simp [backward,liftNCAlgHom,liftNCRingHom,liftNC_single,firstCharacter]

theorem coefficient_of (k : K) : coefficient R H K (of R K k)=of R (H × K) (1,k) :=
  lift_of _ _

theorem backward_forward : (backward R H K).comp (forward R H K)=AlgHom.id R _ := by
  apply MonoidAlgebra.algHom_ext
  rintro ⟨h,k⟩
  change backward R H K (forward R H K (of R (H × K) (h,k)))=of R (H × K) (h,k)
  rw [forward_of,← single_eq_algebraMap_mul_of,backward_single,coefficient_of,← map_mul]
  simp

theorem forward_backward : (forward R H K).comp (backward R H K)=AlgHom.id R _ := by
  apply AlgHom.ext
  intro p
  induction p using Finsupp.induction with
  | zero => simp
  | @single_add h a f _ ha ih =>
    simp only [AlgHom.comp_apply,map_add,AlgHom.id_apply] at ih ⊢
    rw [ih]
    congr 1
    clear ha
    induction a using Finsupp.induction with
    | zero => simp
    | @single_add k r f _ _ ih =>
      simp only [Finsupp.single_add,map_add] at ih ⊢
      rw [ih]
      congr 1
      have hs : (Finsupp.single k r : MonoidAlgebra R K)=
          algebraMap R (MonoidAlgebra R K) r*of R K k := single_eq_algebraMap_mul_of k r
      have ht : (Finsupp.single h (Finsupp.single k r) : Target R H K)=
          algebraMap (MonoidAlgebra R K) (Target R H K) (Finsupp.single k r)*
            of (MonoidAlgebra R K) H h := single_eq_algebraMap_mul_of h _
      simp only [backward_single,ht,hs,map_mul,AlgHom.commutes,coefficient_of,forward_of]
      simp [mul_assoc]

def equiv : Source R H K ≃ₐ[R] Target R H K :=
  AlgEquiv.ofAlgHom (forward R H K) (backward R H K)
    (forward_backward R H K) (backward_forward R H K)

#print axioms Source
#print axioms Target
#print axioms forwardCharacter
#print axioms forward
#print axioms coefficientCharacter
#print axioms coefficient
#print axioms firstCharacter
#print axioms backward
#print axioms forward_of
#print axioms backward_single
#print axioms coefficient_of
#print axioms backward_forward
#print axioms forward_backward
#print axioms equiv
end Verification.ProductTorusAlgebra
