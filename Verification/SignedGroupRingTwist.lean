/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.BinarySignedFiber

/-!
# Signed Group Ring Twist

Multiplying each group character by an integral sign character is a
literal involutive algebra automorphism of the group ring.
-/
noncomputable section
namespace Verification.SignedGroupRingTwist
variable {G : Type*} [CommGroup G] (χ : G →* ℤˣ)

def character : G →* MonoidAlgebra ℤ G :=
  ((algebraMap ℤ (MonoidAlgebra ℤ G)).toMonoidHom.comp ((Units.coeHom ℤ).comp χ)) *
    MonoidAlgebra.of ℤ G

def hom : MonoidAlgebra ℤ G →ₐ[ℤ] MonoidAlgebra ℤ G :=
  MonoidAlgebra.lift ℤ G (MonoidAlgebra ℤ G) (character χ)

theorem monomial (g : G) : hom χ (MonoidAlgebra.of ℤ G g) =
    algebraMap ℤ _ (χ g : ℤ) * MonoidAlgebra.of ℤ G g :=
  MonoidAlgebra.lift_of _ _

theorem involutive : Function.Involutive (hom χ) := by
  have hh : (hom χ).comp (hom χ) = AlgHom.id ℤ (MonoidAlgebra ℤ G) := by
    apply MonoidAlgebra.algHom_ext
    intro g
    change hom χ (hom χ (MonoidAlgebra.of ℤ G g)) = MonoidAlgebra.of ℤ G g
    rw [monomial,map_mul,AlgHom.commutes,monomial,← mul_assoc,← map_mul]
    simp [Int.units_coe_mul_self]
  intro x
  exact DFunLike.congr_fun hh x

def equiv : MonoidAlgebra ℤ G ≃ₐ[ℤ] MonoidAlgebra ℤ G :=
  AlgEquiv.ofBijective (hom χ) (involutive χ).bijective

#print axioms character
#print axioms hom
#print axioms monomial
#print axioms involutive
#print axioms equiv
end Verification.SignedGroupRingTwist
