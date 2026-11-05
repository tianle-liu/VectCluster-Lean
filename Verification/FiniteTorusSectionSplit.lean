/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FiniteTorusLaurent
import Verification.GradedMilnorWittLaurentWords
import Verification.GradedMilnorWittSheafEquiv
import Verification.TorusSmooth
import Verification.TorusZero

/-!
# Finite Torus Section Split

The actual section ring of each ordered split torus has the ordinary
Laurent decomposition, with explicit constant and first-symbol summands.
-/
noncomputable section
namespace Verification.FiniteTorusSectionSplit
open CategoryTheory AlgebraicGeometry
open Verification.OriginalTorus
variable (R : Type) [CommRing R]
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : GradedMilnorWittSheaf.Standard site N)
variable (K : StandardThomContractionNormalization.Grading R site N)
local notation "𝕋" n => CommRingCat.of (Torus R (Fin n))
local notation "𝕃" n => CommRingCat.of (FiniteTorusLaurent.Laurent R n)

def coefficient (n : ℕ) : D.Total (𝕋 n) →+* D.Total (𝕋 (n+1)) :=
  GradedMilnorWittSheaf.pullback site N D (FiniteTorusLaurent.coefficient R n).toRingHom

def firstSymbol (n : ℕ) : D.Total (𝕋 (n+1)) :=
  (D.symbols (𝕋 (n+1))).symbol (FinsuppTorusUniversal.unit R (Fin (n+1)) 0)

def equiv (n : ℕ) : D.Total (𝕋 (n+1)) ≃+ D.Total (𝕋 n) × D.Total (𝕋 n) :=
  (GradedMilnorWittSheafEquiv.equiv site N D
    (S := 𝕋 (n+1)) (T := 𝕃 n) (FiniteTorusLaurent.equiv R n).symm.toRingEquiv).toAddEquiv.trans
      (GradedMilnorWittLaurentSplit.equiv R (Torus R (Fin n)) site N D K
        (TorusSmooth.torus_smooth R (Fin n)))

def zeroEquiv : D.Total (CommRingCat.of R) ≃+ D.Total (𝕋 0) :=
  (GradedMilnorWittSheafEquiv.equiv site N D
    (S := CommRingCat.of R) (T := 𝕋 0) (TorusZero.algebraEquiv R).toRingEquiv).toAddEquiv

theorem forward_coefficient (n : ℕ) (a : D.Total (𝕋 n)) :
    GradedMilnorWittSheaf.pullback site N D (S := 𝕃 n) (T := 𝕋 (n+1))
      (FiniteTorusLaurent.equiv R n).toRingHom
      (GradedMilnorWittLaurent.coefficient R site N D (Torus R (Fin n)) a)=
        coefficient R site N D n a := by
  have h : (GradedMilnorWittSheaf.pullback site N D (S := 𝕃 n) (T := 𝕋 (n+1))
      (FiniteTorusLaurent.equiv R n).toRingHom).comp
      (GradedMilnorWittLaurent.coefficient R site N D (Torus R (Fin n)))=
      coefficient R site N D n := by
    unfold GradedMilnorWittLaurent.coefficient coefficient
    rw [← GradedMilnorWittSheaf.pullback_comp]
    congr 1
    apply RingHom.ext
    exact FiniteTorusLaurent.forward_coefficient R n
  exact RingHom.congr_fun h a

theorem forward_symbol (n : ℕ) :
    GradedMilnorWittSheaf.pullback site N D (S := 𝕃 n) (T := 𝕋 (n+1))
      (FiniteTorusLaurent.equiv R n).toRingHom
      (GradedMilnorWittLaurentWords.parameterSymbol (Torus R (Fin n)) site N D)=
        firstSymbol R site N D n := by
  unfold GradedMilnorWittLaurentWords.parameterSymbol firstSymbol
  rw [GradedMilnorWittSheaf.pullback_symbol]
  congr 1
  apply Units.ext
  change FiniteTorusLaurent.forward R n
    (LaurentPolynomialUniversal.parameterUnit (Torus R (Fin n)) : FiniteTorusLaurent.Laurent R n)=_
  rw [LaurentPolynomialUniversal.parameterUnit_val,FiniteTorusLaurent.forward_parameter]
  rfl

variable (P : GradedMilnorWittLaurent.Standard R site N D K)
include P

theorem inverse_words (n : ℕ) (a b : D.Total (𝕋 n)) :
    (equiv R site N D K n).symm (a,b)=
      coefficient R site N D n a+firstSymbol R site N D n*coefficient R site N D n b := by
  change GradedMilnorWittSheaf.pullback site N D (S := 𝕃 n) (T := 𝕋 (n+1))
    (FiniteTorusLaurent.equiv R n).toRingHom
    ((GradedMilnorWittLaurentSplit.equiv R (Torus R (Fin n)) site N D K
      (TorusSmooth.torus_smooth R (Fin n))).symm (a,b))=_
  rw [GradedMilnorWittLaurentWords.inverse_words R (Torus R (Fin n)) site N D K
    (TorusSmooth.torus_smooth R (Fin n)) P,map_add,map_mul,forward_coefficient,forward_coefficient,forward_symbol]

#print axioms coefficient
#print axioms firstSymbol
#print axioms equiv
#print axioms zeroEquiv
#print axioms forward_coefficient
#print axioms forward_symbol
#print axioms inverse_words
end Verification.FiniteTorusSectionSplit
