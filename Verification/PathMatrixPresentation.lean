/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathEndpointMonomials

/-!
# Path Matrix Presentation

The standard consecutive path exchange matrix presentation is the actual
nearest-neighbour PathAlgebra, by an explicit ambient polynomial equivalence.
This supplies the literal Y/Z component identification used after normalization.
-/
noncomputable section
namespace Verification.PathMatrixPresentation
open MvPolynomial
variable (R : Type*) [CommRing R] (n : ℕ)

def ambient : MvPolynomial (Fin n ⊕ Fin n) R ≃ₐ[R] MvPolynomial (Fin n) (MvPolynomial (Fin n) R) :=
  (renameEquiv R (Equiv.sumComm (Fin n) (Fin n))).trans (sumAlgEquiv R (Fin n) (Fin n))

theorem ambient_original (i : Fin n) : ambient R n (X (Sum.inl i))=C (X i) := by
  change sumToIter R (Fin n) (Fin n) (rename _ (X (Sum.inl i)))=_
  rw [rename_X]
  exact sumToIter_Xr _ _ _ _

theorem ambient_partner (i : Fin n) : ambient R n (X (Sum.inr i))=X i := by
  change sumToIter R (Fin n) (Fin n) (rename _ (X (Sum.inr i)))=_
  rw [rename_X]
  exact sumToIter_Xl _ _ _ _

theorem ambient_constant (r : R) : ambient R n (C r)=C (C r) := (ambient R n).commutes r

theorem ambient_boundary (a b : R) (k : Fin (n+2)) :
    ambient R n (PathPresentation.boundary (C a) (C b) (fun i=>X (Sum.inl i)) k)=
      C (PathPresentation.boundary (C a) (C b) X k) := by
  rw [PathPresentation.boundary_map (ambient R n),ambient_constant,ambient_constant]
  simp only [ambient_original]
  exact (PathPresentation.boundary_map C (C a) (C b) X k).symm

variable (a b : Rˣ)
def leftCoefficient (i : Fin n) : Rˣ := if i.val=0 then a else 1
def rightCoefficient (i : Fin n) : Rˣ := if i.val+1=n then b else 1

def matrixRelations : Ideal (MvPolynomial (Fin n) (MvPolynomial (Fin n) R)) :=
  ScalarExchangeRelabel.relations R id (PathLattice.pathMatrix n) (leftCoefficient R n a) (rightCoefficient R n b)

theorem ambient_relation (i : Fin n) : ambient R n (PathPresentation.relation (a : R) (b : R) i)=
    ScalarExchangeRelabel.relation R id (PathLattice.pathMatrix n) (leftCoefficient R n a) (rightCoefficient R n b) i := by
  rw [PathPresentation.relation,map_sub,map_sub,map_mul,ambient_original,ambient_partner,
    ambient_boundary,ambient_boundary]
  simp only [ScalarExchangeRelabel.relation,leftCoefficient,rightCoefficient,id_eq,
    PathEndpointMonomials.powerSum,map_add]
  ring

theorem map_relations : (PathPresentation.relations n (a : R) (b : R)).map (ambient R n).toRingHom=
    matrixRelations R n a b := by
  rw [PathPresentation.relations,Ideal.map_span,← Set.range_comp]
  change Ideal.span (Set.range (fun i=>ambient R n (PathPresentation.relation (a : R) (b : R) i)))=_
  simp only [ambient_relation]
  rfl

def presentationEquiv : PathPresentation.PathAlgebra n (a : R) (b : R) ≃ₐ[R]
    (MvPolynomial (Fin n) (MvPolynomial (Fin n) R) ⧸ matrixRelations R n a b) :=
  Ideal.quotientEquivAlg _ _ (ambient R n) (map_relations R n a b).symm

theorem presentation_x (i : Fin n) : presentationEquiv R n a b (PathPresentation.x (a : R) (b : R) i)=
    Ideal.Quotient.mk (matrixRelations R n a b) (C (X i)) := by
  change Ideal.Quotient.mk _ (ambient R n (X (Sum.inl i)))=_
  rw [ambient_original]

theorem presentation_y (i : Fin n) : presentationEquiv R n a b (PathPresentation.y (a : R) (b : R) i)=
    Ideal.Quotient.mk (matrixRelations R n a b) (X i) := by
  change Ideal.Quotient.mk _ (ambient R n (X (Sum.inr i)))=_
  rw [ambient_partner]

#print axioms ambient
#print axioms ambient_original
#print axioms ambient_partner
#print axioms ambient_constant
#print axioms ambient_boundary
#print axioms leftCoefficient
#print axioms rightCoefficient
#print axioms matrixRelations
#print axioms ambient_relation
#print axioms map_relations
#print axioms presentationEquiv
#print axioms presentation_x
#print axioms presentation_y
end Verification.PathMatrixPresentation
