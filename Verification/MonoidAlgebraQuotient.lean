/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.MonoidAlgebraProducts
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Monoid Algebra Quotient

Coefficient quotients commute with adjoining free torus characters.
All maps retain the actual coefficients and monomials; this is the
algebraic step needed when an exchange constraint avoids selected variables.
-/
noncomputable section
namespace Verification.MonoidAlgebraQuotient
open MonoidAlgebra
variable (R H : Type) [CommRing R] [CommGroup H] (I : Ideal R)

abbrev extendedIdeal : Ideal (MonoidAlgebra R H) :=
  I.map (algebraMap R (MonoidAlgebra R H))

def coefficientMap : MonoidAlgebra R H →ₐ[R] MonoidAlgebra (R ⧸ I) H :=
  MonoidAlgebraProducts.coefficientMap (Ideal.Quotient.mkₐ R I)

theorem coefficientMap_single (h : H) (r : R) :
    coefficientMap R H I (Finsupp.single h r) =
      Finsupp.single h (Ideal.Quotient.mk I r) :=
  MonoidAlgebraProducts.coefficientMap_single _ h r

theorem ideal_le_kernel : extendedIdeal R H I ≤ RingHom.ker (coefficientMap R H I) := by
  rw [extendedIdeal,Ideal.map_le_iff_le_comap]
  intro r hr
  change coefficientMap R H I (algebraMap R _ r) = 0
  rw [AlgHom.commutes]
  change Finsupp.single 1 (Ideal.Quotient.mk I r) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr,Finsupp.single_zero]

def forward : (MonoidAlgebra R H ⧸ extendedIdeal R H I) →ₐ[R] MonoidAlgebra (R ⧸ I) H :=
  Ideal.Quotient.liftₐ _ (coefficientMap R H I) (ideal_le_kernel R H I)

def coefficientLift : (R ⧸ I) →ₐ[R] (MonoidAlgebra R H ⧸ extendedIdeal R H I) :=
  Ideal.Quotient.liftₐ I (Algebra.ofId R _) (by
    intro r hr
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_map_of_mem _ hr)

def character : H →* (MonoidAlgebra R H ⧸ extendedIdeal R H I) :=
  (Ideal.Quotient.mk _).toMonoidHom.comp (of R H)

def backward : MonoidAlgebra (R ⧸ I) H →ₐ[R]
    (MonoidAlgebra R H ⧸ extendedIdeal R H I) :=
  liftNCAlgHom (coefficientLift R H I) (character R H I) (fun _ _=>Commute.all _ _)

theorem backward_single (h : H) (r : R) :
    backward R H I (Finsupp.single h (Ideal.Quotient.mk I r)) =
      Ideal.Quotient.mk (extendedIdeal R H I) (Finsupp.single h r) := by
  change liftNC _ _ (Finsupp.single h (Ideal.Quotient.mk I r)) = _
  rw [liftNC_single]
  change Ideal.Quotient.mk _ (algebraMap R (MonoidAlgebra R H) r) *
    Ideal.Quotient.mk _ (of R H h) = _
  rw [← map_mul,← single_eq_algebraMap_mul_of]

theorem forward_backward : (forward R H I).comp (backward R H I)=AlgHom.id R _ := by
  apply AlgHom.ext
  intro p
  induction p using Finsupp.induction with
  | zero => simp
  | single_add h c p _ _ ih =>
    simp only [AlgHom.comp_apply,AlgHom.id_apply,map_add] at ih ⊢
    rw [ih]
    congr 1
    obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [backward_single]
    exact coefficientMap_single R H I h r

theorem backward_forward : (backward R H I).comp (forward R H I)=AlgHom.id R _ := by
  apply AlgHom.ext
  intro p
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective p
  change backward R H I (coefficientMap R H I p) = Ideal.Quotient.mk _ p
  induction p using Finsupp.induction with
  | zero => simp
  | single_add h r p _ _ ih =>
    rw [map_add,map_add,map_add,ih,coefficientMap_single,backward_single]

def equiv : (MonoidAlgebra R H ⧸ extendedIdeal R H I) ≃ₐ[R] MonoidAlgebra (R ⧸ I) H :=
  AlgEquiv.ofAlgHom (forward R H I) (backward R H I)
    (forward_backward R H I) (backward_forward R H I)

theorem equiv_monomial (h : H) (r : R) :
    equiv R H I (Ideal.Quotient.mk (extendedIdeal R H I) (Finsupp.single h r)) =
      Finsupp.single h (Ideal.Quotient.mk I r) := coefficientMap_single R H I h r

#print axioms extendedIdeal
#print axioms coefficientMap
#print axioms coefficientMap_single
#print axioms ideal_le_kernel
#print axioms forward
#print axioms coefficientLift
#print axioms character
#print axioms backward
#print axioms backward_single
#print axioms forward_backward
#print axioms backward_forward
#print axioms equiv
#print axioms equiv_monomial
end Verification.MonoidAlgebraQuotient
