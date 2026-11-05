/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Projective Cone Terms

Projectivity and genuine finite degree bounds of the actual mapping
cone, derived from its biproduct terms rather than assumed for the cone.
-/
noncomputable section
namespace Verification.ProjectiveConeTerms
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
variable {P Q : CochainComplex C ℤ} (f : P ⟶ Q)

def termIso (i : ℤ) : (mappingCone f).X i ≅ P.X (i+1) ⊞ Q.X i :=
  homotopyCofiber.XIsoBiprod f i (i+1) rfl

theorem term_projective (hP : ∀ i, Projective (P.X i)) (hQ : ∀ i, Projective (Q.X i))
    (i : ℤ) : Projective ((mappingCone f).X i) := by
  letI := hP (i+1)
  letI := hQ i
  exact Projective.of_iso (termIso f i).symm inferInstance

omit [HasBinaryBiproducts C] in
theorem shift_projective (K : CochainComplex C ℤ) (hK : ∀ i, Projective (K.X i)) (n i : ℤ) :
    Projective ((K⟦n⟧).X i) :=
  Projective.of_iso (K.shiftFunctorObjXIso n i (i+n) rfl).symm (hK (i+n))


theorem strictlyGE (a c : ℤ) [P.IsStrictlyGE a] [Q.IsStrictlyGE c] :
    CochainComplex.IsStrictlyGE (mappingCone f) (min (a-1) c) := by
  apply (CochainComplex.isStrictlyGE_iff (mappingCone f) _).mpr
  intro i hi
  apply IsZero.of_iso _ (termIso f i)
  apply (biprod_isZero_iff _ _).mpr
  exact ⟨P.isZero_of_isStrictlyGE a (i+1) (by omega), Q.isZero_of_isStrictlyGE c i (by omega)⟩

theorem strictlyLE (b d : ℤ) [P.IsStrictlyLE b] [Q.IsStrictlyLE d] :
    CochainComplex.IsStrictlyLE (mappingCone f) (max (b-1) d) := by
  apply (CochainComplex.isStrictlyLE_iff (mappingCone f) _).mpr
  intro i hi
  apply IsZero.of_iso _ (termIso f i)
  apply (biprod_isZero_iff _ _).mpr
  exact ⟨P.isZero_of_isStrictlyLE b (i+1) (by omega), Q.isZero_of_isStrictlyLE d i (by omega)⟩

/-- Bounded means actual terms vanish outside an integer interval. -/
def Bounded (K : CochainComplex C ℤ) : Prop :=
  ∃ a b : ℤ, K.IsStrictlyGE a ∧ K.IsStrictlyLE b

omit [HasBinaryBiproducts C] in
theorem bounded_shift (K : CochainComplex C ℤ) (hK : Bounded K) (n : ℤ) : Bounded (K⟦n⟧) := by
  obtain ⟨a,b,ha,hb⟩ := hK
  letI := ha
  letI := hb
  exact ⟨a-n,b-n,K.isStrictlyGE_shift a n (a-n) (by omega),
    K.isStrictlyLE_shift b n (b-n) (by omega)⟩

theorem bounded (hP : Bounded P) (hQ : Bounded Q) : Bounded (mappingCone f) := by
  obtain ⟨a,b,ha,hb⟩ := hP
  obtain ⟨c,d,hc,hd⟩ := hQ
  letI := ha
  letI := hb
  letI := hc
  letI := hd
  exact ⟨min (a-1) c,max (b-1) d,strictlyGE f a c,strictlyLE f b d⟩

#print axioms termIso
#print axioms term_projective
#print axioms shift_projective
#print axioms strictlyGE
#print axioms strictlyLE
#print axioms Bounded
#print axioms bounded_shift
#print axioms bounded
end Verification.ProjectiveConeTerms
