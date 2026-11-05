/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathForestPartitionPresentation
import Verification.SingleLaurentGroupAlgebra
import Verification.TrivialGroupAlgebra
import Verification.SingleLaurentPolynomialEquiv

/-!
# Path Forest Factor Coefficients

The coefficient algebra of an even forest component is the ground ring;
that of an odd component is the actual one-variable principal localization,
with its endpoint character sent to the literal Laurent parameter.
-/
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 600000
namespace Verification.PathForestFactorCoefficients
open Classical Verification.PathForestFrozenPartition Verification.PathForestPartitionPresentation
variable {S F : Type} [Fintype S] [Fintype F] (o : S → Bool)
variable (R : Type) [CommRing R] (s : S)
def oneExponent : Lattice (F:=F) o (some s) := fun _=>1

def evenTrivial (ho : o s=false) : Subsingleton (Lattice (F:=F) o (some s)) := by
  constructor
  intro x y
  funext h
  have ht := h.down
  rw [ho] at ht
  contradiction

def evenCoefficient (ho : o s=false) : Coefficient (F:=F) o R (some s) ≃ₐ[R] R := by
  letI := evenTrivial (F:=F) o s ho
  exact TrivialGroupAlgebra.equiv R (Lattice (F:=F) o (some s))

theorem even_character (ho : o s=false) :
    evenCoefficient (F:=F) o R s ho (ExchangeCharacters.monomial (oneExponent (F:=F) o s))=1 := by
  letI := evenTrivial (F:=F) o s ho
  have he : oneExponent (F:=F) o s=0 := Subsingleton.elim _ _
  rw [he,ExchangeCharacters.monomial_zero,map_one]

def oddLattice (ho : o s=true) : Lattice (F:=F) o (some s) ≃ₗ[ℤ] ℤ where
  toFun x := x ⟨ho⟩
  invFun z := fun _=>z
  left_inv x := by funext h;congr 1
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def oddCoefficient (ho : o s=true) : Coefficient (F:=F) o R (some s) ≃ₐ[R]
    LaurentPolynomialUniversal.Laurent R :=
  (LaurentScalarModel.coefficientEquiv R (oddLattice (F:=F) o s ho)).trans
    ((SingleLaurentGroupAlgebra.equiv R).symm.trans (SingleLaurentPolynomialEquiv.equiv R))

theorem odd_character (ho : o s=true) :
    oddCoefficient (F:=F) o R s ho (ExchangeCharacters.monomial (oneExponent (F:=F) o s))=
      LaurentPolynomialUniversal.parameter R := by
  change SingleLaurentPolynomialEquiv.equiv R ((SingleLaurentGroupAlgebra.equiv R).symm
    (LaurentScalarModel.coefficientEquiv R (oddLattice (F:=F) o s ho) _))=_
  rw [LaurentScalarModel.coefficientEquiv_monomial]
  change SingleLaurentPolynomialEquiv.equiv R (SingleLaurentGroupAlgebra.backward R (MonoidAlgebra.of R (Multiplicative ℤ) (Multiplicative.ofAdd 1)))=_
  rw [SingleLaurentGroupAlgebra.backward_of,zpow_one,SingleLaurent.parameterUnit_val]
  exact SingleLaurentPolynomialEquiv.parameter R

#print axioms oneExponent
#print axioms evenTrivial
#print axioms evenCoefficient
#print axioms even_character
#print axioms oddLattice
#print axioms oddCoefficient
#print axioms odd_character
end Verification.PathForestFactorCoefficients
