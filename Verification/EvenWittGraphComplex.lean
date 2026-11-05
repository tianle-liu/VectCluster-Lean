/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.EvenWittGraphCoefficients
import Verification.GraphBlockComplex

/-!
# Even Witt Graph Complex

The literal even-colored Witt quotient complex is chain-isomorphic
to the graph monomial complex, with the original degree |I|.
-/
noncomputable section
set_option maxRecDepth 4000
open scoped Classical
namespace Verification.EvenWittGraphComplex
open CategoryTheory Verification.OriginalWittIntegerDifferential
open Verification.EvenWittGraphRealization Verification.GraphBlocks
variable {V C : Type} [Fintype V] [Fintype C] [LinearOrder V]
variable (G : SimpleGraph V) (c : V → C)
variable (hc : ∀ I : Finset V, G.IsIndepSet (I : Set V) → Function.Injective (fun i : I => c i.val))

def degreeEquiv (p : ℕ) :
    OriginalWittIntegerComplex.degree (EvenWittColumns.frozenMatrix c) (Allowed G) p ≃ₗ[ℤ]
      GraphBlockComplex.degreeModule ℤ (GraphBlockComplex.monomialDegree G c) p where
  toFun f := ⟨EvenWittGraphCoefficients.equiv G c hc f.val,by
    apply (GraphBlockComplex.mem_degreeModule _ _ _ _).mpr
    intro x hx
    rw [EvenWittGraphCoefficients.apply_value,f.property ⟨x.I,x.independent⟩ hx,map_zero]
    rfl⟩
  invFun g := ⟨(EvenWittGraphCoefficients.equiv G c hc).symm g.val,by
    intro I hI
    apply (EvenWittWordBasis.basis c I.val (hc I.val I.property)).repr.injective
    ext AF
    rw [map_zero]
    change _ = 0
    let x : MonomialIndex G c := ⟨I.val,AF.val.1,AF.val.2,I.property,AF.property.1,AF.property.2⟩
    have he := EvenWittGraphCoefficients.apply_value G c hc
      ((EvenWittGraphCoefficients.equiv G c hc).symm g.val) x
    rw [LinearEquiv.apply_symm_apply] at he
    exact he.symm.trans ((GraphBlockComplex.mem_degreeModule _ _ _ _).mp g.property x hI)⟩
  left_inv f := by apply Subtype.ext; exact (EvenWittGraphCoefficients.equiv G c hc).symm_apply_apply f.val
  right_inv g := by apply Subtype.ext; exact (EvenWittGraphCoefficients.equiv G c hc).apply_symm_apply g.val
  map_add' f g := by apply Subtype.ext; exact map_add (EvenWittGraphCoefficients.equiv G c hc) f.val g.val
  map_smul' r f := by apply Subtype.ext; exact map_smul (EvenWittGraphCoefficients.equiv G c hc) r f.val

def complex : CochainComplex (ModuleCat ℤ) ℕ :=
  OriginalWittIntegerComplex.complex (EvenWittColumns.frozenMatrix c) (Allowed G)
    (hereditary G) (independentEntries G c)

def iso : complex G c ≅ GraphBlockComplex.monomialComplex ℤ G c :=
  HomologicalComplex.Hom.isoOfComponents (fun p => (degreeEquiv G c hc p).toModuleIso) (by
    intro p q hpq
    have hq : p+1=q := hpq
    subst q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    simp only [complex,OriginalWittIntegerComplex.complex,GraphBlockComplex.monomialComplex,
      GraphBlockComplex.gradedComplex,CochainComplex.of_d,ModuleCat.hom_comp,
      LinearMap.comp_apply,LinearEquiv.toModuleIso_hom,ModuleCat.hom_ofHom]
    apply Subtype.ext
    exact (EvenWittGraphCoefficients.differential G c hc f.val).symm)

#print axioms degreeEquiv
#print axioms complex
#print axioms iso
end Verification.EvenWittGraphComplex
