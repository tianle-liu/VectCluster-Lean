/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.IntegerTensorExtension
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Nat Complex Integer Extension

Extension by zero from natural to integer cochain degrees. The
comparison after an arbitrary additive functor is proved on the actual
three-term complexes, with no flatness assumption.
-/
noncomputable section
namespace Verification.NatComplexIntegerExtension
open CategoryTheory CategoryTheory.Limits
variable {R : Type} [CommRing R]
variable (C : CochainComplex (ModuleCat.{0} R) ℕ)

def extended : CochainComplex (ModuleCat.{0} R) ℤ :=
  C.extend ComplexShape.embeddingUpNat

def termIso (p : ℕ) : (extended C).X (p : ℤ) ≅ C.X p :=
  C.extendXIso ComplexShape.embeddingUpNat rfl

def shortIso (p : ℕ) :
    (extended C).sc' ((p-1 : ℕ) : ℤ) (p : ℤ) ((p+1 : ℕ) : ℤ) ≅ C.sc' (p-1) p (p+1) :=
  ShortComplex.isoMk (termIso C (p-1)) (termIso C p) (termIso C (p+1))
    (by
      change (termIso C (p-1)).hom ≫ C.d (p-1) p =
        (C.extend ComplexShape.embeddingUpNat).d _ _ ≫ _
      rw [HomologicalComplex.extend_d_eq C ComplexShape.embeddingUpNat
        (i := p-1) (j := p) (i' := ((p-1 : ℕ) : ℤ)) (j' := (p : ℤ)) rfl rfl]
      simp only [termIso,Category.assoc,Iso.inv_hom_id,Category.comp_id])
    (by
      change (termIso C p).hom ≫ C.d p (p+1) =
        (C.extend ComplexShape.embeddingUpNat).d _ _ ≫ _
      rw [HomologicalComplex.extend_d_eq C ComplexShape.embeddingUpNat
        (i := p) (j := p+1) (i' := (p : ℤ)) (j' := ((p+1 : ℕ) : ℤ)) rfl rfl]
      simp only [termIso,Category.assoc,Iso.inv_hom_id,Category.comp_id])

variable {D : Type*} [Category D] [Abelian D]
variable (F : ModuleCat.{0} R ⥤ D) [F.Additive]

def mappedHomologyIso (p : ℕ) (hp : 0 < p) :
    (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (extended C)).homology (p : ℤ)) ≅
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology p) :=
  (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (extended C)).homologyIsoSc'
    ((p-1 : ℕ) : ℤ) (p : ℤ) ((p+1 : ℕ) : ℤ) (by simp; omega) (by simp)).trans
      (((ShortComplex.homologyFunctor D).mapIso
        ((F.mapShortComplex).mapIso (shortIso C p))).trans
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homologyIsoSc'
        (p-1) p (p+1)
        ((ComplexShape.up ℕ).prev_eq' (show p-1+1=p by omega))
        ((ComplexShape.up ℕ).next_eq' rfl)).symm)

#print axioms extended
#print axioms termIso
#print axioms shortIso
#print axioms mappedHomologyIso
end Verification.NatComplexIntegerExtension
