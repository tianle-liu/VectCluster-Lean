/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.TameCharacterSmooth

/-!
# Character Map Smooth

The actual map of split tori attached to an independent lattice map
is smooth with tame Smith coefficients. We identify its source algebra
over the target torus with the character graph quotient; no conclusion
about smoothness of a morphism is inferred merely from its fibers.
-/

noncomputable section
universe u v
namespace Verification.CharacterMapSmooth
open MonoidAlgebra Verification.PrimitiveCharacters Verification.SmithCharacters
variable {R M P ι : Type u} {κ : Type v}
  [CommRing R] [AddCommGroup M] [AddCommGroup P]

abbrev Torus (R P : Type u) [CommRing R] [AddCommGroup P] :=
  MonoidAlgebra R (Multiplicative P)

def characterMap (f : P →ₗ[ℤ] M) : Torus R P →ₐ[R] Torus R M :=
  MonoidAlgebra.lift R _ _ ((of R (Multiplicative M)).comp f.toAddMonoidHom.toMultiplicative)

theorem characterMap_monomial (f : P →ₗ[ℤ] M) (p : P) :
    characterMap (R := R) f (of R (Multiplicative P) (Multiplicative.ofAdd p)) =
      of R (Multiplicative M) (Multiplicative.ofAdd (f p)) := by
  simp [characterMap]

def universalCharacter (R P : Type u) [CommRing R] [AddCommGroup P] :
    Multiplicative P →* (Torus R P)ˣ := (of R (Multiplicative P)).toHomUnits

abbrev GraphAlgebra (R : Type u) [CommRing R] (f : P →ₗ[ℤ] M) (b : Basis κ ℤ P) :=
  MonoidAlgebra (Torus R P) (Multiplicative M) ⧸ columnIdeal f b (universalCharacter R P)

def graphMonomial (f : P →ₗ[ℤ] M) (b : Basis κ ℤ P) (m : M) : GraphAlgebra R f b :=
  Ideal.Quotient.mk (columnIdeal f b (universalCharacter R P))
    (of (Torus R P) (Multiplicative M) (Multiplicative.ofAdd m))

theorem graph_relation (f : P →ₗ[ℤ] M) (b : Basis κ ℤ P) (p : P) :
    graphMonomial (R := R) f b (f p) =
      algebraMap (Torus R P) (GraphAlgebra R f b)
        (of R (Multiplicative P) (Multiplicative.ofAdd p)) := by
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr
    (all_relations_mem f b (universalCharacter R P) p)
  simpa only [latticeRelation, map_sub, sub_eq_zero] using h

def fromSourceR (f : P →ₗ[ℤ] M) (b : Basis κ ℤ P) : Torus R M →ₐ[R] GraphAlgebra R f b :=
  MonoidAlgebra.lift R _ _
    ((Ideal.Quotient.mk (columnIdeal f b (universalCharacter R P))).toMonoidHom.comp
      (of (Torus R P) (Multiplicative M)))

theorem fromSourceR_monomial (f : P →ₗ[ℤ] M) (b : Basis κ ℤ P) (m : M) :
    fromSourceR (R := R) f b (of R (Multiplicative M) (Multiplicative.ofAdd m)) =
      graphMonomial (R := R) f b m := by
  exact MonoidAlgebra.lift_of _ _

section GraphPresentation
variable [Algebra (Torus R P) (Torus R M)] [IsScalarTower R (Torus R P) (Torus R M)]
variable (f : P →ₗ[ℤ] M) (b : Basis κ ℤ P)
variable (hchar : ∀ p, algebraMap (Torus R P) (Torus R M)
  (of R (Multiplicative P) (Multiplicative.ofAdd p)) =
    of R (Multiplicative M) (Multiplicative.ofAdd (f p)))
include hchar

def evaluation : MonoidAlgebra (Torus R P) (Multiplicative M) →ₐ[Torus R P] Torus R M :=
  MonoidAlgebra.lift (Torus R P) _ _ (of R (Multiplicative M))

def toSource : GraphAlgebra R f b →ₐ[Torus R P] Torus R M :=
  Ideal.Quotient.liftₐ (columnIdeal f b (universalCharacter R P))
    (evaluation (R := R)) (by
      change columnIdeal f b (universalCharacter R P) ≤ RingHom.ker (evaluation (R := R)).toRingHom
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change evaluation (R := R)
        (of (Torus R P) (Multiplicative M) (Multiplicative.ofAdd (f (b i))) -
          algebraMap (Torus R P) _ (of R (Multiplicative P) (Multiplicative.ofAdd (b i)))) = 0
      rw [map_sub, AlgHom.commutes, hchar]
      simp [evaluation])

omit [IsScalarTower R (Torus R P) (Torus R M)] in
theorem toSource_monomial (m : M) : toSource f b hchar (graphMonomial (R := R) f b m) =
    of R (Multiplicative M) (Multiplicative.ofAdd m) := by
  exact MonoidAlgebra.lift_of _ _

theorem fromSourceR_commutes (t : Torus R P) :
    fromSourceR (R := R) f b (algebraMap (Torus R P) (Torus R M) t) =
      algebraMap (Torus R P) (GraphAlgebra R f b) t := by
  have h : (fromSourceR (R := R) f b).comp (IsScalarTower.toAlgHom R (Torus R P) (Torus R M)) =
      IsScalarTower.toAlgHom R (Torus R P) (GraphAlgebra R f b) := by
    apply MonoidAlgebra.algHom_ext
    intro p
    change fromSourceR (R := R) f b
      (algebraMap (Torus R P) (Torus R M) (of R (Multiplicative P) p)) = _
    rw [show p = Multiplicative.ofAdd p.toAdd from rfl, hchar, fromSourceR_monomial]
    exact graph_relation f b p.toAdd
  exact AlgHom.congr_fun h t

def fromSource : Torus R M →ₐ[Torus R P] GraphAlgebra R f b where
  toRingHom := (fromSourceR f b).toRingHom
  commutes' := fromSourceR_commutes f b hchar

theorem fromSource_monomial (m : M) :
    fromSource f b hchar (of R (Multiplicative M) (Multiplicative.ofAdd m)) =
      graphMonomial (R := R) f b m := by
  change fromSourceR (R := R) f b (of R (Multiplicative M) (Multiplicative.ofAdd m)) = _
  exact fromSourceR_monomial f b m

theorem toSource_fromSource :
    (toSource f b hchar).comp (fromSource f b hchar) = AlgHom.id (Torus R P) _ := by
  have h : ((toSource f b hchar).comp (fromSource f b hchar)).restrictScalars R =
      (AlgHom.id (Torus R P) (Torus R M)).restrictScalars R := by
    apply MonoidAlgebra.algHom_ext
    intro m
    change toSource f b hchar (fromSource f b hchar
      (of R (Multiplicative M) (Multiplicative.ofAdd m.toAdd))) = _
    rw [fromSource_monomial, toSource_monomial]
    rfl
  exact AlgHom.ext (fun x => AlgHom.congr_fun h x)

theorem fromSource_toSource :
    (fromSource f b hchar).comp (toSource f b hchar) = AlgHom.id (Torus R P) _ := by
  apply Ideal.Quotient.algHom_ext
  apply MonoidAlgebra.algHom_ext
  intro m
  change fromSource f b hchar (toSource f b hchar
    (graphMonomial (R := R) f b m.toAdd)) = graphMonomial (R := R) f b m.toAdd
  rw [toSource_monomial, fromSource_monomial]

def graphEquiv : GraphAlgebra R f b ≃ₐ[Torus R P] Torus R M :=
  AlgEquiv.ofAlgHom (toSource f b hchar) (fromSource f b hchar)
    (toSource_fromSource f b hchar) (fromSource_toSource f b hchar)

include b in
theorem smooth_of_character [Fintype ι]
    (hf : Function.Injective f) {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) ι n)
    (he : ∀ i, IsUnit ((s.a i).natAbs : R)) : Algebra.Smooth (Torus R P) (Torus R M) := by
  have he' (i : Fin n) : IsUnit ((s.a i).natAbs : Torus R P) := by
    simpa only [map_natCast] using (he i).map (algebraMap R (Torus R P))
  letI := TameCharacterSmooth.smith_character_smooth f hf b s (universalCharacter R P) he'
  exact Algebra.Smooth.of_equiv (graphEquiv f b hchar)

end GraphPresentation

theorem characterMap_smooth [Fintype ι]
    (f : P →ₗ[ℤ] M) (hf : Function.Injective f) (b : Basis κ ℤ P)
    {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) ι n)
    (he : ∀ i, IsUnit ((s.a i).natAbs : R)) :
    letI := (characterMap (R := R) f).toRingHom.toAlgebra
    Algebra.Smooth (Torus R P) (Torus R M) := by
  letI := (characterMap (R := R) f).toRingHom.toAlgebra
  exact smooth_of_character f b (characterMap_monomial f) hf s he

theorem characterMap_smooth_charZero {k : Type u} [Field k] [CharZero k] [Fintype ι]
    (bM : Basis ι ℤ M) (f : P →ₗ[ℤ] M) (hf : Function.Injective f) (b : Basis κ ℤ P) :
    letI := (characterMap (R := k) f).toRingHom.toAlgebra
    Algebra.Smooth (Torus k P) (Torus k M) := by
  obtain ⟨n,s⟩ := (LinearMap.range f).smithNormalForm bM
  apply characterMap_smooth f hf b s
  intro i
  exact isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr
    (Int.natAbs_ne_zero.mpr (smith_coefficient_ne_zero s i)))

#print axioms Torus
#print axioms characterMap
#print axioms characterMap_monomial
#print axioms universalCharacter
#print axioms GraphAlgebra
#print axioms graphMonomial
#print axioms graph_relation
#print axioms fromSourceR
#print axioms fromSourceR_monomial
#print axioms evaluation
#print axioms toSource
#print axioms toSource_monomial
#print axioms fromSourceR_commutes
#print axioms fromSource
#print axioms fromSource_monomial
#print axioms toSource_fromSource
#print axioms fromSource_toSource
#print axioms graphEquiv
#print axioms smooth_of_character
#print axioms characterMap_smooth
#print axioms characterMap_smooth_charZero
end Verification.CharacterMapSmooth
