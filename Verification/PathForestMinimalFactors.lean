/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathForestFactorCoefficients
import Verification.EndpointLaurentPathPresentation
import Verification.PathCoefficientAlgebraEquiv

/-!
# Path Forest Minimal Factors

Every actual path-forest tensor factor is the literal Y or Z coordinate
algebra, with its exact endpoint, dimension and ground algebra.
-/
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.PathForestMinimalFactors
open Classical Verification.PathForestFrozenPartition Verification.PathForestPartitionPresentation
open Verification.PathForestFactorCoefficients
variable {S F : Type} [Fintype S] [Fintype F] (m : S → ℕ) (o : S → Bool)
variable (R : Type) [CommRing R] (s : S)

theorem column_eq : endpointColumn (F:=F) o m s=
    EndpointLaurentPathPresentation.exponent (PathOrientationBlocks.length (m s) (o s))
      (oneExponent (F:=F) o s) := by
  funext i
  change (fun _ : PLift (o s=true)=>if i.val=0 then (1:ℤ) else 0)=
    (if i.val=0 then oneExponent (F:=F) o s else 0)
  split_ifs <;> rfl

def pathEquiv : Factor (F:=F) m o R (some s) ≃ₐ[R]
    PathPresentation.PathAlgebra (PathOrientationBlocks.length (m s) (o s))
      (ExchangeCharacters.monomial (R:=R) (oneExponent (F:=F) o s)) 1 := by
  change LaurentScalarModel.Presentation R
    (PathLattice.pathMatrix (PathOrientationBlocks.length (m s) (o s)))
      (endpointColumn (F:=F) o m s) (fun _=>1) ≃ₐ[R] _
  rw [column_eq]
  exact EndpointLaurentPathPresentation.equiv R (PathOrientationBlocks.length (m s) (o s))
    (oneExponent (F:=F) o s)

def evenEquiv (ho : o s=false) : Factor (F:=F) m o R (some s) ≃ₐ[R]
    PathPresentation.PathAlgebra (2*m s) (1:R) 1 := by
  have e := (pathEquiv (F:=F) m o R s).trans
    (PathCoefficientAlgebraEquiv.endpointEquiv R (evenCoefficient (F:=F) o R s ho)
      (PathOrientationBlocks.length (m s) (o s))
      (ExchangeCharacters.monomial (R:=R) (oneExponent (F:=F) o s)) 1 1 1
      (even_character (F:=F) o R s ho) (map_one _))
  have hl : PathOrientationBlocks.length (m s) (o s)=2*m s := by rw [ho];rfl
  rw [hl] at e
  exact e

def oddEquiv (ho : o s=true) : Factor (F:=F) m o R (some s) ≃ₐ[R]
    PathPresentation.PathAlgebra (2*m s+1) (LaurentPolynomialUniversal.parameter R) 1 := by
  have e := (pathEquiv (F:=F) m o R s).trans
    (PathCoefficientAlgebraEquiv.endpointEquiv R (oddCoefficient (F:=F) o R s ho)
      (PathOrientationBlocks.length (m s) (o s))
      (ExchangeCharacters.monomial (R:=R) (oneExponent (F:=F) o s)) 1
      (LaurentPolynomialUniversal.parameter R) 1
      (odd_character (F:=F) o R s ho) (map_one _))
  have hl : PathOrientationBlocks.length (m s) (o s)=2*m s+1 := by rw [ho];rfl
  rw [hl] at e
  exact e

#print axioms column_eq
#print axioms pathEquiv
#print axioms evenEquiv
#print axioms oddEquiv
end Verification.PathForestMinimalFactors
