/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ProductCharacterQuotient
import Verification.PrimitiveCharacters

/-!
# Free Character Factor

A coordinate-preserving quotient equivalence for a lattice splitting
on which all imposed character equations vanish in the free factor.
-/
noncomputable section
namespace Verification.FreeCharacterFactor
open MonoidAlgebra
variable (R M P Q ι : Type) [CommRing R] [AddCommGroup M] [AddCommGroup P] [AddCommGroup Q]
variable (e : M ≃ₗ[ℤ] P×Q) (c : ι → M) (u : ι → R)
variable (hc : ∀ i,(e (c i)).1=0)

def sourceIdeal : Ideal (MonoidAlgebra R (Multiplicative M)) :=
  Ideal.span (Set.range (fun i => of R _ (Multiplicative.ofAdd (c i))-algebraMap R _ (u i)))

def coefficientIdeal : Ideal (MonoidAlgebra R (Multiplicative Q)) :=
  ProductCharacterQuotient.coefficientIdeal R _ ι (fun i=>Multiplicative.ofAdd (e (c i)).2) u

include hc in
theorem map_sourceIdeal :
    (sourceIdeal R M ι c u).map (domCongr R R (PrimitiveCharacters.groupSplitting e)).toRingHom =
      ProductCharacterQuotient.sourceIdeal R (Multiplicative P) (Multiplicative Q) ι
        (fun i=>Multiplicative.ofAdd (e (c i)).2) u := by
  rw [sourceIdeal,ProductCharacterQuotient.sourceIdeal,Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  change domCongr R R (PrimitiveCharacters.groupSplitting e)
    (of R _ (Multiplicative.ofAdd (c i))-algebraMap R _ (u i)) = _
  rw [map_sub,AlgEquiv.commutes]
  congr 1
  change domCongr R R (PrimitiveCharacters.groupSplitting e) (Finsupp.single _ 1) = Finsupp.single _ 1
  rw [domCongr_single]
  congr 1
  change (Multiplicative.ofAdd (e (c i)).1,Multiplicative.ofAdd (e (c i)).2) = _
  rw [hc]
  rfl

def equiv : (MonoidAlgebra R (Multiplicative M) ⧸ sourceIdeal R M ι c u) ≃ₐ[R]
    MonoidAlgebra (MonoidAlgebra R (Multiplicative Q) ⧸ coefficientIdeal R M P Q ι e c u)
      (Multiplicative P) :=
  (Ideal.quotientEquivAlg _ _ (domCongr R R (PrimitiveCharacters.groupSplitting e))
    (map_sourceIdeal R M P Q ι e c u hc).symm).trans
      (ProductCharacterQuotient.equiv R (Multiplicative P) (Multiplicative Q) ι
        (fun i=>Multiplicative.ofAdd (e (c i)).2) u)

set_option maxHeartbeats 800000 in
theorem equiv_monomial (m : M) :
    equiv R M P Q ι e c u hc (Ideal.Quotient.mk _ (of R _ (Multiplicative.ofAdd m))) =
      Finsupp.single (Multiplicative.ofAdd (e m).1)
        (Ideal.Quotient.mk _ (of R _ (Multiplicative.ofAdd (e m).2))) := by
  change ProductCharacterQuotient.equiv R (Multiplicative P) (Multiplicative Q) ι
    (fun i=>Multiplicative.ofAdd (e (c i)).2) u
    (Ideal.Quotient.mk _ (domCongr R R (PrimitiveCharacters.groupSplitting e)
      (Finsupp.single (Multiplicative.ofAdd m) 1))) = _
  rw [domCongr_single]
  exact ProductCharacterQuotient.equiv_monomial R (Multiplicative P) (Multiplicative Q) ι _ u _ _

theorem equiv_free (p : P) :
    equiv R M P Q ι e c u hc
      (Ideal.Quotient.mk _ (of R _ (Multiplicative.ofAdd (e.symm (p,0))))) =
        of (MonoidAlgebra R (Multiplicative Q) ⧸ coefficientIdeal R M P Q ι e c u)
          (Multiplicative P) (Multiplicative.ofAdd p) := by
  rw [equiv_monomial,e.apply_symm_apply]
  change Finsupp.single (Multiplicative.ofAdd p) (Ideal.Quotient.mk _ (of R _ 1)) = _
  rw [map_one,map_one]
  rfl

#print axioms sourceIdeal
#print axioms coefficientIdeal
#print axioms map_sourceIdeal
#print axioms equiv
#print axioms equiv_monomial
#print axioms equiv_free
end Verification.FreeCharacterFactor
