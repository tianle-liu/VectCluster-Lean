/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualStrictCone

/-!
# Strict Projective Model

Bounded projective strict models, with their actual cross-category Hom
universal property. Closure under isomorphisms and distinguished extensions
is proved from the strict cone theorem, never from ambient quasi-isomorphisms.
-/
noncomputable section
namespace Verification.StrictProjectiveModel
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject
open Verification.StrictTriangleHom Verification.ActualStrictCone
universe w v u v' u'
variable {A : Type u} [Category.{v} A] [Abelian A] [HasBinaryBiproducts A]
variable [HasDerivedCategory.{w} A]
variable {D : Type u'} [Category.{v'} D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]

structure Model (X : D) where
  complex : CochainComplex A ℤ
  bounded : ProjectiveConeTerms.Bounded complex
  projective : ∀ i, Projective (complex.X i)
  comparison : X ⟶ J.obj (DerivedCategory.Q.obj complex)
  universal : Universal J comparison

def ofIso {X Y : D} (e : X ≅ Y) (M : Model J Y) : Model J X where
  complex := M.complex
  bounded := M.bounded
  projective := M.projective
  comparison := e.hom ≫ M.comparison
  universal := by
    intro E
    constructor
    · intro f g h
      apply (M.universal E).injective
      apply (cancel_epi e.hom).mp
      simpa only [comparison, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Category.assoc] using h
    · intro u
      obtain ⟨f,hf⟩ := (M.universal E).surjective (e.inv ≫ u)
      refine ⟨f,?_⟩
      change (e.hom ≫ M.comparison) ≫ J.map f = u
      rw [Category.assoc]
      change e.hom ≫ comparison J M.comparison E f = u
      rw [hf,Iso.hom_inv_id_assoc]

def ofIsZero (X : D) (hX : IsZero X) : Model J X where
  complex := HomologicalComplex.zero
  bounded := by
    refine ⟨0,0,?_,?_⟩
    · rw [CochainComplex.isStrictlyGE_iff]
      intro i _
      exact isZero_zero A
    · rw [CochainComplex.isStrictlyLE_iff]
      intro i _
      exact isZero_zero A
  projective := fun _ => inferInstanceAs (Projective (0 : A))
  comparison := 0
  universal := by
    intro E
    constructor
    · intro f g _
      exact (Functor.map_isZero DerivedCategory.Q HomologicalComplex.isZero_zero).eq_of_src f g
    · intro f
      exact ⟨0,hX.eq_of_src _ _⟩

/-- Standard chain-map representability for bounded projective complexes.
This only refers to Q for the strict abelian category; it is no fullness
condition on the realization functor J. -/
def ChainRepresentability : Prop := ∀ (P Q : CochainComplex A ℤ),
  ProjectiveConeTerms.Bounded P → ProjectiveConeTerms.Bounded Q →
  (∀ i, Projective (P.X i)) → (∀ i, Projective (Q.X i)) →
  Function.Surjective (DerivedCategory.Q.map : (P ⟶ Q) →
    (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj Q))

variable [HasZeroObject D] [HasShift D ℤ]
variable [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
variable [J.CommShift ℤ] [J.IsTriangulated]

theorem extension_exists (H : ChainRepresentability (A := A)) {T : Triangle D}
    (hT : T ∈ distTriang D) (MA : Model J T.obj₁) (MC : Model J T.obj₃) :
    Nonempty (Model J T.obj₂) := by
  obtain ⟨u,_,hb,hp,φ,hφ⟩ := bounded_projective_cone J hT MA.complex MC.complex
    MA.comparison MC.comparison MA.universal MC.universal
    (H (MC.complex⟦(-1 : ℤ)⟧) MA.complex
      (ProjectiveConeTerms.bounded_shift MC.complex MC.bounded (-1)) MA.bounded
      (ProjectiveConeTerms.shift_projective MC.complex MC.projective (-1)) MA.projective)
    MA.bounded MC.bounded MA.projective MC.projective
  exact ⟨⟨CochainComplex.mappingCone u,hb,hp,φ,hφ.2⟩⟩

def extension (H : ChainRepresentability (A := A)) {T : Triangle D}
    (hT : T ∈ distTriang D) (MA : Model J T.obj₁) (MC : Model J T.obj₃) : Model J T.obj₂ :=
  (extension_exists J H hT MA MC).some

#print axioms Model
#print axioms ofIso
#print axioms ofIsZero
#print axioms ChainRepresentability
#print axioms extension_exists
#print axioms extension
end Verification.StrictProjectiveModel
