/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SmithComponents
import Verification.OriginalTorus

/-!
# Affine Torus Coefficient Product

Explicit coefficient and Laurent-variable formulas for the actual
finite product decomposition of polynomial Laurent algebras. These bind
the unit decomposition to the named coefficients and variables.
-/
noncomputable section
namespace Verification.AffineTorusCoefficientProduct
variable {R S J : Type} [CommRing R] [CommRing S] [Algebra R S] [Fintype J]
variable (D : J → Type) [∀ j, CommRing (D j)] [∀ j, Algebra R (D j)]
variable (E : S ≃ₐ[R] ∀ j, D j) (ι κ : Type)

def torusEquiv : OriginalTorus.Torus S κ ≃ₐ[R] ∀ j, OriginalTorus.Torus (D j) κ :=
  (MonoidAlgebraProducts.coefficientEquiv E).trans
    (MonoidAlgebraProducts.productEquiv R (Multiplicative (κ →₀ ℤ)) D)

theorem torus_single (m : Multiplicative (κ →₀ ℤ)) (s : S) (j : J) :
    torusEquiv D E κ (Finsupp.single m s) j = Finsupp.single m (E s j) := by
  change MonoidAlgebraProducts.coefficientMap (Pi.evalAlgHom R D j)
    (MonoidAlgebraProducts.coefficientMap E.toAlgHom (Finsupp.single m s)) = _
  rw [MonoidAlgebraProducts.coefficientMap_single, MonoidAlgebraProducts.coefficientMap_single]
  rfl

def affineEquiv : MvPolynomial ι (OriginalTorus.Torus S κ) ≃ₐ[R]
    ∀ j, MvPolynomial ι (OriginalTorus.Torus (D j) κ) :=
  (MvPolynomial.mapAlgEquiv (R := R) ι (torusEquiv D E κ)).trans
    (SmithComponents.polynomialProductEquiv (R := R) (I := ι)
      (fun j => OriginalTorus.Torus (D j) κ))

theorem polynomial_monomial (m : ι →₀ ℕ) (c : ∀ j, OriginalTorus.Torus (D j) κ) (j : J) :
    SmithComponents.polynomialProductEquiv (R := R) (I := ι)
      (fun j => OriginalTorus.Torus (D j) κ) (MvPolynomial.monomial m c) j =
        MvPolynomial.monomial m (c j) := by
  let L := fun j => OriginalTorus.Torus (D j) κ
  change (AddMonoidAlgebra.toMultiplicativeAlgEquiv (R := R) (L j) (ι →₀ ℕ)).symm
    (MonoidAlgebraProducts.productEquiv R (Multiplicative (ι →₀ ℕ)) L
      (AddMonoidAlgebra.toMultiplicativeAlgEquiv (R := R) (∀ j, L j) (ι →₀ ℕ)
        (MvPolynomial.monomial m c)) j) = _
  apply (AddMonoidAlgebra.toMultiplicativeAlgEquiv (R := R) (L j) (ι →₀ ℕ)).injective
  rw [AlgEquiv.apply_symm_apply]
  have h₁ : AddMonoidAlgebra.toMultiplicativeAlgEquiv (R := R) (∀ j, L j) (ι →₀ ℕ)
      (MvPolynomial.monomial m c) = Finsupp.single (Multiplicative.ofAdd m) c :=
    Finsupp.equivMapDomain_single _ _ _
  have h₂ : AddMonoidAlgebra.toMultiplicativeAlgEquiv (R := R) (L j) (ι →₀ ℕ)
      (MvPolynomial.monomial m (c j)) = Finsupp.single (Multiplicative.ofAdd m) (c j) :=
    Finsupp.equivMapDomain_single _ _ _
  rw [h₁, h₂]
  exact MonoidAlgebraProducts.coefficientMap_single (Pi.evalAlgHom R L j) _ _

theorem affine_C (s : OriginalTorus.Torus S κ) (j : J) :
    affineEquiv D E ι κ (MvPolynomial.C s) j = MvPolynomial.C (torusEquiv D E κ s j) := by
  change SmithComponents.polynomialProductEquiv (R := R) (I := ι)
    (fun j => OriginalTorus.Torus (D j) κ)
    (MvPolynomial.map (torusEquiv D E κ).toRingHom (MvPolynomial.C s)) j = _
  rw [MvPolynomial.map_C]
  exact polynomial_monomial D ι κ 0 _ j

theorem coefficient (s : S) (j : J) :
    affineEquiv D E ι κ
      (algebraMap S (MvPolynomial ι (OriginalTorus.Torus S κ)) s) j =
      MvPolynomial.C (algebraMap (D j) (OriginalTorus.Torus (D j) κ) (E s j)) := by
  rw [show algebraMap S (MvPolynomial ι (OriginalTorus.Torus S κ)) s =
    MvPolynomial.C (algebraMap S (OriginalTorus.Torus S κ) s) from rfl, affine_C]
  change MvPolynomial.C (torusEquiv D E κ (Finsupp.single 1 s) j) = _
  rw [torus_single]
  rfl

theorem torus_variable (k : κ) (j : J) :
    affineEquiv D E ι κ (MvPolynomial.C (OriginalTorus.torusCoordinate S κ k)) j =
      MvPolynomial.C (OriginalTorus.torusCoordinate (D j) κ k) := by
  rw [affine_C]
  change MvPolynomial.C (torusEquiv D E κ
    (Finsupp.single (Multiplicative.ofAdd (Finsupp.single k 1)) 1) j) = _
  rw [torus_single, map_one]
  rfl

#print axioms torusEquiv
#print axioms torus_single
#print axioms affineEquiv
#print axioms polynomial_monomial
#print axioms affine_C
#print axioms coefficient
#print axioms torus_variable
end Verification.AffineTorusCoefficientProduct
