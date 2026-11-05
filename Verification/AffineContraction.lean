/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Affine Contraction

Explicit affine-space contraction to its zero section: the polynomial
homotopy sends every coordinate y_i to t*y_i and fixes the coefficient ring.
Both endpoint identities hold as algebra homomorphisms.
-/
noncomputable section
universe u
namespace Verification.AffineContraction
open MvPolynomial
variable (S ι : Type u) [CommRing S]
abbrev Affine := MvPolynomial ι S

def zeroSection : Affine S ι →ₐ[S] S := aeval (fun _ => 0)
def projection : S →ₐ[S] Affine S ι := Algebra.ofId S (Affine S ι)
def homotopy : Affine S ι →ₐ[S] Polynomial (Affine S ι) :=
  aeval (fun i => Polynomial.C (X i) * Polynomial.X)
def atZero : Polynomial (Affine S ι) →ₐ[S] Affine S ι :=
  (Polynomial.aeval (0 : Affine S ι)).restrictScalars S
def atOne : Polynomial (Affine S ι) →ₐ[S] Affine S ι :=
  (Polynomial.aeval (1 : Affine S ι)).restrictScalars S

theorem homotopy_X (i : ι) : homotopy S ι (X i) = Polynomial.C (X i) * Polynomial.X := aeval_X _ _

theorem zeroSection_projection : (zeroSection S ι).comp (projection S ι) = AlgHom.id S S := by
  apply AlgHom.ext
  intro s
  exact (zeroSection S ι).commutes s

theorem atZero_homotopy : (atZero S ι).comp (homotopy S ι) = (projection S ι).comp (zeroSection S ι) := by
  apply MvPolynomial.algHom_ext
  intro i
  change atZero S ι (homotopy S ι (X i)) = projection S ι (zeroSection S ι (X i))
  rw [homotopy_X]
  change Polynomial.aeval (0 : Affine S ι) (Polynomial.C (X i) * Polynomial.X) =
    projection S ι (aeval (fun _ : ι => (0 : S)) (X i))
  rw [map_mul,Polynomial.aeval_C,Polynomial.aeval_X,aeval_X,map_zero,mul_zero]

theorem atOne_homotopy : (atOne S ι).comp (homotopy S ι) = AlgHom.id S (Affine S ι) := by
  apply MvPolynomial.algHom_ext
  intro i
  change atOne S ι (homotopy S ι (X i)) = X i
  rw [homotopy_X]
  change Polynomial.aeval (1 : Affine S ι) (Polynomial.C (X i) * Polynomial.X) = X i
  rw [map_mul,Polynomial.aeval_C,Polynomial.aeval_X,mul_one]
  rfl

#print axioms Affine
#print axioms zeroSection
#print axioms projection
#print axioms homotopy
#print axioms atZero
#print axioms atOne
#print axioms homotopy_X
#print axioms zeroSection_projection
#print axioms atZero_homotopy
#print axioms atOne_homotopy
end Verification.AffineContraction
