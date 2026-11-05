/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphChainMatrix
import Verification.MatrixKernelEnumeration

/-!
# Graph Chain Kernel Coordinates

The actual graph-chain differential kernel in arbitrary finite
coordinate enumerations, preserving the originally defined chain complex.
-/
noncomputable section
namespace Verification.GraphChainKernelCoordinates
open Classical
open Verification.GraphCover Verification.GraphCoverGrading Verification.GraphChainMatrix
open Verification.GradedPerturbation
variable {R V : Type} [CommRing R] [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) (T : Finset V)
def enumeration : Fintype (Simplex G T) := inferInstance
def equality : DecidableEq (Simplex G T) := inferInstance

variable (f₂ : Fintype (Simplex G T)) (d₂ : DecidableEq (Simplex G T))

def equiv (p q : ℤ) (h : p+1=q) :
    LinearMap.ker ((chainComplex (R := R) G T).d p q).hom ≃ₗ[R]
      LinearMap.ker (@matrixDegreeMap R _ (Simplex G T) f₂ d₂
        (degree G T) (chainMatrix G T) 1 (chainMatrix_degree G T) p q h.symm) :=
  MatrixKernelEnumeration.kernelEquiv (f₁ := enumeration G T) (d₁ := equality G T) f₂ d₂ (degree G T) (chainMatrix G T)
    (chainMatrix_degree G T) (chainMatrix_square G T) p q h

#print axioms enumeration
#print axioms equality
#print axioms equiv
end Verification.GraphChainKernelCoordinates
