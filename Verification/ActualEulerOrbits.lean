/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualOrientations
import Verification.OrbitQuotientClassification

/-!
# Actual Euler Orbits

For actual oriented finite projective modules, an equivariant Euler
classification induces the claimed classification after forgetting
orientations. The Euler bijection itself is supplied separately by the
Postnikov argument; it is not proved or assumed by this quotient lemma.
-/
noncomputable section
namespace Verification.ActualEulerOrbits
open CategoryTheory Verification.ActualOrientations
variable (R : Type) [CommRing R] (r : ℕ)

def underlyingSetoid : Setoid (Oriented R r) where
  r P Q := Nonempty (P.bundle.object ≅ Q.bundle.object)
  iseqv := ⟨fun _ => ⟨Iso.refl _⟩,
    fun ⟨e⟩ => ⟨e.symm⟩,fun ⟨e⟩ ⟨f⟩ => ⟨e ≪≫ f⟩⟩

/-- Isomorphism classes of orientable rank-r projective modules. -/
def OrientableClasses := Quotient (underlyingSetoid R r)

variable {R r} {H : Type*} [MulAction Rˣ H]
variable (E : Classes (R := R) (r := r) ≃ H)
variable (hE : ∀ (u : Rˣ) (P : Oriented R r),
  E (Quotient.mk _ (changeOrientation u P))=u • E (Quotient.mk _ P))

def classifier (P : Oriented R r) : H := E (Quotient.mk _ P)

omit [MulAction Rˣ H] in
theorem classifier_surjective : Function.Surjective (classifier E) := by
  intro h
  refine ⟨(E.symm h).out,?_⟩
  change E (Quotient.mk _ (E.symm h).out)=h
  rw [Quotient.out_eq,E.apply_symm_apply]

include hE in
theorem classifier_relation (P Q : Oriented R r) :
    underlyingSetoid R r P Q ↔ MulAction.orbitRel Rˣ H (classifier E P) (classifier E Q) := by
  change Nonempty (P.bundle.object ≅ Q.bundle.object) ↔ _
  rw [underlying_iff_unit,MulAction.orbitRel_apply,MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨u,hu⟩
    have he : u • classifier E P=classifier E Q := by
      unfold classifier
      rw [← hE u P]
      exact congrArg E (Quotient.sound hu)
    refine ⟨u⁻¹,?_⟩
    rw [← he,inv_smul_smul]
  · rintro ⟨u,hu⟩
    refine ⟨u⁻¹,Quotient.exact (E.injective ?_)⟩
    rw [hE]
    change u⁻¹ • classifier E P=classifier E Q
    rw [← hu,inv_smul_smul]

def unorientedEquiv : OrientableClasses R r ≃ Quotient (MulAction.orbitRel Rˣ H) :=
  OrbitQuotientClassification.equiv (underlyingSetoid R r) (classifier E)
    (classifier_surjective E) (classifier_relation E hE)

#print axioms underlyingSetoid
#print axioms OrientableClasses
#print axioms classifier
#print axioms classifier_surjective
#print axioms classifier_relation
#print axioms unorientedEquiv
end Verification.ActualEulerOrbits
