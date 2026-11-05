/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimeProductTopology
import Verification.ComponentHomeomorph
import Verification.SigmaComponents

/-!
# Domain Product Components

The finite labels in a product of domains are exactly the genuine
connected-component type of its prime spectrum. The equivalence uses
the actual spectrum homeomorphism and is transported along ring maps.
-/
noncomputable section
namespace Verification.DomainProductComponents
variable {J : Type} (R : J→Type) [∀ j,CommRing (R j)] [∀ j,IsDomain (R j)]

def collapse : (Σ j,ConnectedComponents (PrimeSpectrum (R j))) ≃ J where
  toFun := Sigma.fst
  invFun j := ⟨j,ConnectedComponents.mk ⟨⊥,Ideal.bot_prime⟩⟩
  left_inv p := by
    rcases p with ⟨j,p⟩
    obtain ⟨p,rfl⟩ := ConnectedComponents.surjective_coe p
    have h : ConnectedComponents.mk (⟨⊥,Ideal.bot_prime⟩ : PrimeSpectrum (R j))=
        ConnectedComponents.mk p := by
      apply ConnectedComponents.coe_eq_coe'.mpr
      rw [PreconnectedSpace.connectedComponent_eq_univ]
      exact Set.mem_univ _
    exact congrArg (Sigma.mk j) h
  right_inv _ := rfl

def components [Finite J] : ConnectedComponents (PrimeSpectrum (∀ j,R j)) ≃ J :=
  (ComponentHomeomorph.components (PrimeProductTopology.spectrumProductHomeomorph R).symm).trans
    ((SigmaComponents.components (fun j => PrimeSpectrum (R j))).trans (collapse R))

theorem components_mk [Finite J] (j : J) (p : PrimeSpectrum (R j)) :
    components R (ConnectedComponents.mk (PrimeSpectrum.comap (Pi.evalRingHom R j) p))=j := by
  change ((PrimeProductTopology.spectrumProductHomeomorph R).symm
    ((PrimeProductTopology.spectrumProductHomeomorph R) ⟨j,p⟩)).1=j
  rw [Homeomorph.symm_apply_apply]

def transport {A : Type} [CommRing A] [Finite J] (e : A≃+*∀ j,R j) :
    ConnectedComponents (PrimeSpectrum A) ≃ J :=
  (ComponentHomeomorph.components (PrimeSpectrum.homeomorphOfRingEquiv e)).trans (components R)

#print axioms collapse
#print axioms components
#print axioms components_mk
#print axioms transport
end Verification.DomainProductComponents
