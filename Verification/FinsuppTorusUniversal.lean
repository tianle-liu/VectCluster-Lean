/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalTorus

/-!
# Finsupp Torus Universal

Unit-generator universal maps of the same finitely supported lattice
Laurent algebra used for the actual original-coordinate torus.
-/
noncomputable section
namespace Verification.FinsuppTorusUniversal
open Verification.OriginalTorus
variable (R κ : Type) [CommRing R]

def unit (i : κ) : (Torus R κ)ˣ :=
  (MonoidAlgebra.of R (Multiplicative (OriginalTorus.Lattice κ))).toHomUnits
    (Multiplicative.ofAdd (Finsupp.single i 1))

theorem unit_val (i : κ) : (unit R κ i : Torus R κ)=torusCoordinate R κ i := rfl

variable {T : Type} [CommRing T] [Algebra R T]

def lift (u : κ → Tˣ) : Torus R κ →ₐ[R] T :=
  MonoidAlgebra.lift R _ _ ((Units.coeHom _).comp
    (Verification.PrimitiveCharacters.basisCharacter
      (Finsupp.basisSingleOne : Basis κ ℤ (OriginalTorus.Lattice κ)) u))

theorem lift_coordinate (u : κ → Tˣ) (i : κ) : lift R κ u (torusCoordinate R κ i)=(u i : T) := by
  rw [torusCoordinate,lift,MonoidAlgebra.lift_of]
  change ((Verification.PrimitiveCharacters.basisCharacter
    (Finsupp.basisSingleOne : Basis κ ℤ (OriginalTorus.Lattice κ)) u)
      (Multiplicative.ofAdd (Finsupp.basisSingleOne i)) : T)=_
  rw [Verification.PrimitiveCharacters.basisCharacter_apply]

theorem lift_unit (u : κ → Tˣ) (i : κ) : Units.map (lift R κ u).toMonoidHom (unit R κ i)=u i := by
  apply Units.ext
  exact lift_coordinate R κ u i

theorem hom_ext (f g : Torus R κ →ₐ[R] T)
    (h : ∀ i,f (torusCoordinate R κ i)=g (torusCoordinate R κ i)) : f=g := by
  apply MonoidAlgebra.algHom_ext'
  apply MonoidHom.eq_of_eqOn_dense (Verification.PrimitiveCharacters.basis_generates
    (Finsupp.basisSingleOne : Basis κ ℤ (OriginalTorus.Lattice κ)))
  rintro _ ⟨i,rfl⟩
  exact h i

#print axioms unit
#print axioms unit_val
#print axioms lift
#print axioms lift_coordinate
#print axioms lift_unit
#print axioms hom_ext
end Verification.FinsuppTorusUniversal
