/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FiniteTorusWordValues
import Verification.FinsuppTorusReindex
import Verification.GradedMilnorWittSheafEquiv
import Verification.GradedMilnorWittScalarNaturality
import Mathlib.Data.Fintype.Sort

/-!
# Torus Model Word Basis

Actual ordered MW word coordinates on a constructed torus model.
Ordering uses the increasing coordinate enumeration and all words keep
their genuine units and arbitrary coefficients on the right.
-/
noncomputable section
namespace Verification.TorusModelWordBasis
open CategoryTheory AlgebraicGeometry
open Verification.OriginalTorus Verification.BinaryWordCoordinates
variable (R S μ : Type) [CommRing R] [CommRing S] [Algebra R S]
variable [Fintype μ] [LinearOrder μ]
variable (e : S ≃ₐ[R] Torus R μ)

def ordering : Fin (Fintype.card μ) ≃o μ := Fintype.orderIsoFinOfCardEq μ rfl

def torusInput : Torus R (Fin (Fintype.card μ)) ≃ₐ[R] S :=
  (FinsuppTorusReindex.equiv R (ordering μ).toEquiv).trans e.symm

def unit (i : Fin (Fintype.card μ)) : Sˣ :=
  Units.map e.symm.toRingHom.toMonoidHom (FinsuppTorusUniversal.unit R μ (ordering μ i))

theorem torusInput_unit (i : Fin (Fintype.card μ)) :
    Units.map (torusInput R S μ e).toRingHom.toMonoidHom
      (FinsuppTorusUniversal.unit R (Fin (Fintype.card μ)) i)=unit R S μ e i := by
  apply Units.ext
  change e.symm (FinsuppTorusReindex.equiv R (ordering μ).toEquiv
    (torusCoordinate R _ i))=e.symm (torusCoordinate R μ (ordering μ i))
  rw [FinsuppTorusReindex.equiv_coordinate]
  rfl

variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : GradedMilnorWittSheaf.Standard site N)
variable (K : StandardThomContractionNormalization.Grading R site N)
local notation "C" => D.Total (CommRingCat.of R)
local notation "𝕊" => D.Total (CommRingCat.of S)
local notation "d" => Fintype.card μ

def input : D.Total (CommRingCat.of (Torus R (Fin d))) ≃+* 𝕊 :=
  GradedMilnorWittSheafEquiv.equiv site N D
    (S := CommRingCat.of (Torus R (Fin d))) (T := CommRingCat.of S)
    (torusInput R S μ e).toRingEquiv

def basis : (Index d → C) ≃+ 𝕊 :=
  (FiniteTorusWordBasis.basis R site N D K d).trans (input R S μ e site N D).toAddEquiv

def word (i : Index d) : 𝕊 :=
  OrderedBinaryWords.word d (fun k => (D.symbols (CommRingCat.of S)).symbol (unit R S μ e k)) i

theorem input_scalar (a : C) :
    input R S μ e site N D (FiniteTorusWordValues.scalar R site N D d a)=
      GradedMilnorWittScalarNaturality.scalar R S site N D a :=
  GradedMilnorWittScalarNaturality.naturality R (Torus R (Fin d)) S site N D
    (torusInput R S μ e).toAlgHom a

theorem input_word (i : Index d) :
    input R S μ e site N D (FiniteTorusWordValues.word R site N D d i)=word R S μ e site N D i := by
  change (input R S μ e site N D).toMonoidHom
    (OrderedBinaryWords.word d (FiniteTorusWordValues.symbol R site N D d) i)=_
  rw [OrderedBinaryWords.map_word]
  congr 1
  funext k
  change GradedMilnorWittSheaf.pullback site N D
    (S := CommRingCat.of (Torus R (Fin d))) (T := CommRingCat.of S)
    (torusInput R S μ e).toRingHom
    ((D.symbols (CommRingCat.of (Torus R (Fin d)))).symbol (FinsuppTorusUniversal.unit R (Fin d) k))=_
  rw [GradedMilnorWittSheaf.pullback_symbol,torusInput_unit]

variable (P : GradedMilnorWittLaurent.Standard R site N D K)
include P

theorem basis_single (i : Index d) (a : C) :
    basis R S μ e site N D K (Pi.single i a)=
      word R S μ e site N D i*GradedMilnorWittScalarNaturality.scalar R S site N D a := by
  change input R S μ e site N D (FiniteTorusWordBasis.basis R site N D K d (Pi.single i a))=_
  rw [FiniteTorusWordValues.basis_word R site N D K P,map_mul,input_word,input_scalar]

theorem basis_expansion (a : Index d → C) :
    basis R S μ e site N D K a=
      ∑ i,word R S μ e site N D i*GradedMilnorWittScalarNaturality.scalar R S site N D (a i) := by
  change input R S μ e site N D (FiniteTorusWordBasis.basis R site N D K d a)=_
  rw [FiniteTorusWordValues.basis_expansion R site N D K P,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul,input_word,input_scalar]

#print axioms ordering
#print axioms torusInput
#print axioms unit
#print axioms torusInput_unit
#print axioms input
#print axioms basis
#print axioms word
#print axioms input_scalar
#print axioms input_word
#print axioms basis_single
#print axioms basis_expansion
end Verification.TorusModelWordBasis
