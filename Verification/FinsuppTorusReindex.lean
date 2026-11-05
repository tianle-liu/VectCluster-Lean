/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FinsuppTorusUniversal
import Verification.LaurentTorusCharacterQuotient
import Verification.LaurentScalarModel

/-!
# Finsupp Torus Reindex

Actual Laurent-algebra reindexing and insertion of the normal coordinate.
-/
noncomputable section
namespace Verification.FinsuppTorusReindex
open Verification.OriginalTorus
variable (R : Type) [CommRing R] {κ τ : Type}

def equiv (e : κ ≃ τ) : Torus R κ ≃ₐ[R] Torus R τ :=
  LaurentScalarModel.coefficientEquiv R (Finsupp.domLCongr e)

theorem equiv_monomial (e : κ ≃ τ) (m : κ →₀ ℤ) :
    equiv R e (ExchangeCharacters.monomial m)=ExchangeCharacters.monomial ((Finsupp.domLCongr e : (κ →₀ ℤ) ≃ₗ[ℤ] (τ →₀ ℤ)) m) :=
  LaurentScalarModel.coefficientEquiv_monomial _ _ _

theorem equiv_coordinate (e : κ ≃ τ) (i : κ) :
    equiv R e (torusCoordinate R κ i)=torusCoordinate R τ (e i) := by
  change equiv R e (ExchangeCharacters.monomial (Finsupp.single i 1))=_
  rw [equiv_monomial,Finsupp.domLCongr_single]
  rfl

def map (f : κ → τ) : Torus R κ →ₐ[R] Torus R τ :=
  MonoidAlgebra.mapDomainAlgHom R R ((Finsupp.lmapDomain ℤ ℤ f).toAddMonoidHom.toMultiplicative)

theorem map_monomial (f : κ → τ) (m : κ →₀ ℤ) :
    map R f (ExchangeCharacters.monomial m)=ExchangeCharacters.monomial (Finsupp.lmapDomain ℤ ℤ f m) := by
  exact Finsupp.mapDomain_single

theorem map_coordinate (f : κ → τ) (i : κ) :
    map R f (torusCoordinate R κ i)=torusCoordinate R τ (f i) := by
  change map R f (ExchangeCharacters.monomial (Finsupp.single i 1))=_
  rw [map_monomial]
  simp only [Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
  rfl

theorem coefficient_eq : LaurentTorusCharacterQuotient.coefficient R κ=map R (some : κ → Option κ) := by
  apply FinsuppTorusUniversal.hom_ext
  intro i
  rw [LaurentTorusCharacterQuotient.coefficient_coordinate,map_coordinate]

#print axioms equiv
#print axioms equiv_monomial
#print axioms equiv_coordinate
#print axioms map
#print axioms map_monomial
#print axioms map_coordinate
#print axioms coefficient_eq
end Verification.FinsuppTorusReindex
