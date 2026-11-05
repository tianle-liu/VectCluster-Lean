/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ProductTorusAlgebra
import Verification.MonoidAlgebraQuotient
import Mathlib.Algebra.Algebra.RestrictScalars

/-!
# Product Character Quotient

Character equations that involve only the second lattice factor
leave the first torus factor free. This equivalence tracks each surviving
monomial, rather than merely comparing dimensions or abstract rings.
-/
noncomputable section
namespace Verification.ProductCharacterQuotient
open MonoidAlgebra
variable (R H K ι : Type) [CommRing R] [CommGroup H] [CommGroup K]
variable (c : ι → K) (u : ι → R)

def coefficientIdeal : Ideal (MonoidAlgebra R K) :=
  Ideal.span (Set.range (fun i => of R K (c i)-algebraMap R _ (u i)))

def sourceIdeal : Ideal (MonoidAlgebra R (H×K)) :=
  Ideal.span (Set.range (fun i => of R (H×K) (1,c i)-algebraMap R _ (u i)))

theorem map_sourceIdeal :
    (sourceIdeal R H K ι c u).map (ProductTorusAlgebra.equiv R H K).toRingHom =
      MonoidAlgebraQuotient.extendedIdeal (MonoidAlgebra R K) H (coefficientIdeal R K ι c u) := by
  rw [sourceIdeal,coefficientIdeal,MonoidAlgebraQuotient.extendedIdeal,
    Ideal.map_span,Ideal.map_span,← Set.range_comp,← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  change ProductTorusAlgebra.forward R H K
    (of R (H×K) (1,c i)-algebraMap R _ (u i)) =
      algebraMap (MonoidAlgebra R K) (MonoidAlgebra (MonoidAlgebra R K) H)
        (of R K (c i)-algebraMap R _ (u i))
  rw [map_sub,ProductTorusAlgebra.forward_of,map_one,mul_one,AlgHom.commutes,map_sub]
  rfl

def equiv : (MonoidAlgebra R (H×K) ⧸ sourceIdeal R H K ι c u) ≃ₐ[R]
    MonoidAlgebra (MonoidAlgebra R K ⧸ coefficientIdeal R K ι c u) H :=
  (Ideal.quotientEquivAlg _ _ (ProductTorusAlgebra.equiv R H K)
    (map_sourceIdeal R H K ι c u).symm).trans
      ((MonoidAlgebraQuotient.equiv (MonoidAlgebra R K) H
        (coefficientIdeal R K ι c u)).restrictScalars R)

theorem equiv_monomial (h : H) (k : K) :
    equiv R H K ι c u (Ideal.Quotient.mk _ (of R (H×K) (h,k))) =
      Finsupp.single h (Ideal.Quotient.mk _ (of R K k)) := by
  change MonoidAlgebraQuotient.equiv (MonoidAlgebra R K) H _
    (Ideal.Quotient.mk _ (ProductTorusAlgebra.forward R H K (of R (H×K) (h,k)))) = _
  rw [ProductTorusAlgebra.forward_of,← single_eq_algebraMap_mul_of,
    MonoidAlgebraQuotient.equiv_monomial]

theorem equiv_free_character (h : H) :
    equiv R H K ι c u (Ideal.Quotient.mk _ (of R (H×K) (h,1))) =
      of (MonoidAlgebra R K ⧸ coefficientIdeal R K ι c u) H h := by
  rw [equiv_monomial,map_one,map_one]
  rfl

#print axioms coefficientIdeal
#print axioms sourceIdeal
#print axioms map_sourceIdeal
#print axioms equiv
#print axioms equiv_monomial
#print axioms equiv_free_character
end Verification.ProductCharacterQuotient
