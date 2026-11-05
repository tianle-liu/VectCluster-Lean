/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Separated Homology

Actual homology of separated incoming and outgoing blocks.  The middle
module is B × C; the first map only hits B and the second only reads C.
The resulting quotient is a direct product, with no extension assumption.
-/

noncomputable section
namespace Verification.SeparatedHomology
open CategoryTheory

variable {R : Type} [CommRing R]
variable {A B C D : Type} [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C] [AddCommGroup D]
  [Module R A] [Module R B] [Module R C] [Module R D]
variable (f : A →ₗ[R] B) (g : C →ₗ[R] D)

def incoming : A →ₗ[R] B × C := f.prod 0

def outgoing : B × C →ₗ[R] D := g.comp (LinearMap.snd R B C)

def shortComplex : ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk (incoming (C := C) f) (outgoing (B := B) g) (by
    ext a
    simp [incoming, outgoing])

def cycleProjection : LinearMap.ker (outgoing (B := B) g) →ₗ[R]
    (B ⧸ LinearMap.range f) × LinearMap.ker g where
  toFun z := ((LinearMap.range f).mkQ z.val.1, ⟨z.val.2, z.property⟩)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

theorem cycleProjection_surjective : Function.Surjective (cycleProjection f g) := by
  rintro ⟨b,c⟩
  obtain ⟨b,hb⟩ := (LinearMap.range f).mkQ_surjective b
  refine ⟨⟨(b,c.val),c.property⟩, ?_⟩
  exact Prod.ext hb rfl

theorem cycleProjection_kernel :
    LinearMap.ker (cycleProjection f g) =
      LinearMap.range (shortComplex f g).moduleCatToCycles := by
  ext z
  constructor
  · intro hz
    have h1 : (LinearMap.range f).mkQ z.val.1 = 0 := congrArg Prod.fst hz
    have h2 : z.val.2 = 0 := congrArg (fun x => x.2.val) hz
    obtain ⟨a,ha⟩ := (Submodule.Quotient.mk_eq_zero _).mp h1
    refine ⟨a, ?_⟩
    apply Subtype.ext
    exact Prod.ext ha h2.symm
  · rintro ⟨a,rfl⟩
    apply Prod.ext
    · exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨a,rfl⟩
    · apply Subtype.ext
      rfl

/-- The literal kernel/image quotient, before categorical homology transport. -/
def quotientEquiv : (shortComplex f g).moduleCatHomology ≃ₗ[R]
    (B ⧸ LinearMap.range f) × LinearMap.ker g :=
  (Submodule.quotEquivOfEq _ _ (cycleProjection_kernel f g).symm).trans
    ((cycleProjection f g).quotKerEquivOfSurjective (cycleProjection_surjective f g))

/-- Actual categorical homology is the independent cokernel and kernel sum. -/
def homologyIso : (shortComplex f g).homology ≅
    ModuleCat.of R ((B ⧸ LinearMap.range f) × LinearMap.ker g) :=
  (shortComplex f g).moduleCatHomologyIso ≪≫ (quotientEquiv f g).toModuleIso

#print axioms incoming
#print axioms outgoing
#print axioms shortComplex
#print axioms cycleProjection
#print axioms cycleProjection_surjective
#print axioms cycleProjection_kernel
#print axioms quotientEquiv
#print axioms homologyIso

end Verification.SeparatedHomology
