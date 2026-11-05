/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FinsuppTorusUniversal

/-!
# Finsupp Torus Tower

The Laurent coordinate universal property over a smaller scalar ring,
allowing the coefficient homomorphism itself to change.
-/
noncomputable section
namespace Verification.FinsuppTorusTower
open Verification.OriginalTorus Verification.FinsuppTorusUniversal
variable (R S κ : Type) [CommRing R] [CommRing S] [Algebra R S]
variable {T : Type} [CommRing T] [Algebra R T]

def lift (f : S →ₐ[R] T) (u : κ → Tˣ) : Torus S κ →ₐ[R] T :=
  MonoidAlgebra.liftNCAlgHom f ((Units.coeHom _).comp
    (Verification.PrimitiveCharacters.basisCharacter
      (Finsupp.basisSingleOne : Basis κ ℤ (OriginalTorus.Lattice κ)) u))
    (fun _ _ => Commute.all _ _)

theorem lift_coordinate (f : S →ₐ[R] T) (u : κ → Tˣ) (i : κ) :
    lift R S κ f u (torusCoordinate S κ i)=(u i : T) := by
  change MonoidAlgebra.liftNC _ _ (MonoidAlgebra.single _ 1)=_
  rw [MonoidAlgebra.liftNC_single]
  change f 1 * _ = (u i : T)
  rw [map_one,one_mul]
  change (Verification.PrimitiveCharacters.basisCharacter
    (Finsupp.basisSingleOne : Basis κ ℤ (OriginalTorus.Lattice κ)) u
      (Multiplicative.ofAdd (Finsupp.basisSingleOne i)) : T)=_
  rw [Verification.PrimitiveCharacters.basisCharacter_apply]

theorem lift_coefficient (f : S →ₐ[R] T) (u : κ → Tˣ) (s : S) :
    lift R S κ f u (algebraMap S (Torus S κ) s)=f s := by
  change MonoidAlgebra.liftNC _ _ (MonoidAlgebra.single 1 s)=_
  rw [MonoidAlgebra.liftNC_single]
  change f s*((Units.coeHom _).comp
    (Verification.PrimitiveCharacters.basisCharacter
      (Finsupp.basisSingleOne : Basis κ ℤ (OriginalTorus.Lattice κ)) u)) 1=_
  rw [map_one,mul_one]

theorem hom_ext (f g : Torus S κ →ₐ[R] T)
    (hc : ∀ s, f (algebraMap S _ s)=g (algebraMap S _ s))
    (hx : ∀ i, f (torusCoordinate S κ i)=g (torusCoordinate S κ i)) : f=g := by
  apply AlgHom.coe_ringHom_injective
  apply MonoidAlgebra.ringHom_ext'
  · exact RingHom.ext hc
  · apply MonoidHom.eq_of_eqOn_dense (Verification.PrimitiveCharacters.basis_generates
      (Finsupp.basisSingleOne : Basis κ ℤ (OriginalTorus.Lattice κ)))
    rintro _ ⟨i,rfl⟩
    exact hx i

#print axioms lift
#print axioms lift_coordinate
#print axioms lift_coefficient
#print axioms hom_ext
end Verification.FinsuppTorusTower
