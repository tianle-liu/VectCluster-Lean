/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathMilnorWittWordFace
import Verification.MilnorWittParameterSign

/-!
# Path Milnor Witt Signed Word Face

The literal original-normal sign multiplies the full rho path column by
its precise power of g, including arbitrary ordered words on both sides.
-/
noncomputable section
namespace Verification.PathMilnorWittSignedWordFace
open Verification.MilnorWittSymbolRelations Verification.MilnorWittSymbolNaturality
open Verification.PathMilnorWittTriple Verification.PathMilnorWittWords
open Verification.PathMilnorWittWordFace
variable {S T A B : Type*} [CommRing S] [CommRing T] [Ring A] [Ring B]
variable (D₀ : Symbols S B) (D₁ : Symbols T A) (f : S →+* T) (F : B →+* A)
variable (h : Compatible D₀ D₁ f F) (u : Tˣ)

include h in
theorem signed_column (r : A →+ B) (r_constant : ∀ b,r (F b)=0)
    (r_parameter : ∀ b,r (D₁.symbol u * F b)=b) (w : ℕ)
    (xs ys : List (Sˣ × Bool)) (a : Sˣ) (l m t : Bool) :
    r (monomial D₁ ((selected xs).map (Units.map f.toMonoidHom)) *
      word (D₁.symbol (Units.map f.toMonoidHom a)) (D₁.symbol ((-1:Tˣ)^w*u))
        (D₁.symbol (Units.map f.toMonoidHom a)) (l,m,t) *
      monomial D₁ ((selected ys).map (Units.map f.toMonoidHom))) =
    D₀.g^w * evaluate D₀ (xs.map Prod.fst ++ a::ys.map Prod.fst)
      (Verification.PathRhoWords.faceColumn (-Verification.PathCoefficientRing.g)
        Verification.PathCoefficientRing.rho (xs.map Prod.snd).length
        (xs.map Prod.snd ++ l::m::t::ys.map Prod.snd)) := by
  have hs : D₀.g^w*D₀.g^w=1 := by rw [← pow_add,show w+w=2*w by omega,pow_mul,pow_two,D₀.g_square,one_pow]
  let r' : A →+ B := (AddMonoidHom.mulLeft (D₀.g^w)).comp r
  have hc : ∀ b,r' (F b)=0 := by intro b;change D₀.g^w*r (F b)=0;rw [r_constant,mul_zero]
  have hp : ∀ b,r' (D₁.symbol ((-1:Tˣ)^w*u)*F b)=b := by
    intro b
    change D₀.g^w*r (D₁.symbol ((-1:Tˣ)^w*u)*F b)=b
    rw [MilnorWittParameterSign.signed_parameter D₀ D₁ f F h u r r_constant r_parameter,
      ← mul_assoc,hs,one_mul]
  have hh := column_contraction D₀ D₁ f F h ((-1:Tˣ)^w*u) r' hc hp xs ys a l m t
  have hh' := congrArg (fun b => D₀.g^w*b) hh
  change D₀.g^w*(D₀.g^w*r _)=_ at hh'
  simpa only [← mul_assoc,hs,one_mul] using hh'

#print axioms signed_column
end Verification.PathMilnorWittSignedWordFace
