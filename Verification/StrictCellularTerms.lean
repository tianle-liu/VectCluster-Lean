/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictCellularTower

/-!
# Strict Cellular Terms

Each degree of the retained strict cone tower is canonically the
projective term of the corresponding actual layer. These are isomorphisms
of strict-heart objects, not identifications with raw ambient homology.
-/
noncomputable section
namespace Verification.StrictCellularTerms
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Verification.StrictProjectiveModel Verification.StrictSingleModel Verification.StrictCellularTower
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasBinaryBiproducts A]
variable [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
variable [∀ n : ℤ,(shiftFunctor D n).Additive] [Pretriangulated D]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ] [J.IsTriangulated]
variable (L : DerivedCategory C ⥤ D) [L.CommShift ℤ] [L.IsTriangulated]
variable (H : ChainRepresentability (A := A)) (F : ℕ ⥤ CochainComplex C ℤ)

variable (cells : ∀ p : ℕ,Cell J (-(p : ℤ))
  (L.obj (DerivedCategory.Q.obj (FilteredConeComplex.relative F p))))

variable (hzero : IsZero (L.obj (DerivedCategory.Q.obj (F.obj 0))))

def termIso : (p q : ℕ) → (hq : q<p) →
    ((tower J L H F cells hzero p).model.complex).X (-(q : ℤ)) ≅ (cells q).term
  | 0,q,hq => (Nat.not_lt_zero q hq).elim
  | p+1,q,hq => by
      let M := tower J L H F cells hzero p
      letI : M.model.complex.IsStrictlyGE (-(p : ℤ)+1) := by
        convert M.lower using 1; omega
      by_cases h : q=p
      · subst q
        exact StrictCellAttachment.newTermIso J M.model (cells p)
          (StrictFiniteFiltration.step_distinguished L F p) (attachment J L H F cells p M)
      · exact StrictCellAttachment.oldTermIso J M.model (cells p)
          (StrictFiniteFiltration.step_distinguished L F p) (attachment J L H F cells p M)
          (-(q : ℤ)) (by omega) ≪≫ termIso p q (by omega)

theorem termIso_succ_of_lt (p q : ℕ) (hq : q<p) :
    termIso J L H F cells hzero (p+1) q (by omega) =
      StrictCellAttachment.oldTermIso J (tower J L H F cells hzero p).model (cells p)
        (StrictFiniteFiltration.step_distinguished L F p)
        (attachment J L H F cells p (tower J L H F cells hzero p))
        (-(q : ℤ)) (by omega) ≪≫ termIso J L H F cells hzero p q hq := by
  simp only [termIso, dif_neg (show q ≠ p by omega)]

def differential (p q : ℕ) (hq : q+1<p) : (cells (q+1)).term ⟶ (cells q).term :=
  (termIso J L H F cells hzero p (q+1) hq).inv ≫
    (tower J L H F cells hzero p).model.complex.d (-((q+1 : ℕ) : ℤ)) (-(q : ℤ)) ≫
      (termIso J L H F cells hzero p q (by omega)).hom

theorem differential_succ (p q : ℕ) (hq : q+1<p) :
    differential J L H F cells hzero (p+1) q (by omega) =
      differential J L H F cells hzero p q hq := by
  unfold differential
  rw [termIso_succ_of_lt J L H F cells hzero p (q+1) hq,
    termIso_succ_of_lt J L H F cells hzero p q (by omega)]
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc]
  have h := StrictCellAttachment.old_differential J
    (tower J L H F cells hzero p).model (cells p)
    (StrictFiniteFiltration.step_distinguished L F p)
    (attachment J L H F cells p (tower J L H F cells hzero p))
    (-((q+1 : ℕ) : ℤ)) (-(q : ℤ)) (by omega) (by omega)
  dsimp only [tower, successor]
  rw [← Category.assoc _ _ (termIso J L H F cells hzero p q (by omega)).hom,
    ← Category.assoc _ _ (termIso J L H F cells hzero p q (by omega)).hom]
  rw [h]

theorem differential_stable (p q : ℕ) (hq : q+1<p) :
    differential J L H F cells hzero p q hq =
      differential J L H F cells hzero (q+2) q (by omega) := by
  have hp : q+2 ≤ p := by omega
  induction p,hp using Nat.le_induction with
  | base => rfl
  | succ p hp ih =>
      rw [differential_succ J L H F cells hzero p q (by omega),ih]

def d (q : ℕ) : (cells (q+1)).term ⟶ (cells q).term :=
  differential J L H F cells hzero (q+2) q (by omega)

theorem d_squared (q : ℕ) : d J L H F cells hzero (q+1) ≫ d J L H F cells hzero q = 0 := by
  unfold d
  rw [← differential_stable J L H F cells hzero (q+3) q (by omega)]
  unfold differential
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc _ _ (termIso J L H F cells hzero (q+3) q (by omega)).hom,
    HomologicalComplex.d_comp_d, zero_comp, comp_zero]

def complex : ChainComplex A ℕ := ChainComplex.of
  (fun q => (cells q).term) (d J L H F cells hzero) (d_squared J L H F cells hzero)

theorem complex_d (q : ℕ) :
    (complex J L H F cells hzero).d (q+1) q = d J L H F cells hzero q :=
  ChainComplex.of_d _ _ _ q

#print axioms termIso
#print axioms termIso_succ_of_lt
#print axioms differential
#print axioms differential_succ
#print axioms differential_stable
#print axioms d
#print axioms d_squared
#print axioms complex
#print axioms complex_d
end Verification.StrictCellularTerms
