/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SplitSurjectionCoordinates

/-!
# Frozen Quotient Coordinates

If the full extended rows generate and the mutable-row quotient is
known, the frozen rows generate that quotient. This constructs a frozen
basis with its odd-component coordinates first, and actual mutable-row
corrections for the remaining difference from a chosen endpoint section.
-/

noncomputable section
namespace Verification.FrozenQuotientCoordinates
open Classical
variable {V F Q : Type} [Fintype V] [Fintype F] [Fintype Q]
variable (B : (V → ℤ) →ₗ[ℤ] (V → ℤ)) (C : (F → ℤ) →ₗ[ℤ] (V → ℤ))
variable (π : (V → ℤ) →ₗ[ℤ] (Q → ℤ)) (hπ : Function.Surjective π)
variable (hB : π.comp B=0) (hfull : Function.Surjective (B.coprod C))

include hπ hB hfull in
omit [Fintype V] [Fintype F] [Fintype Q] in
theorem frozen_surjective : Function.Surjective (π.comp C) := by
  intro q
  obtain ⟨v,hv⟩:=hπ q
  obtain ⟨⟨b,c⟩,hbc⟩:=hfull v
  refine ⟨c,?_⟩
  have h:=congrArg π hbc
  change π (B b+C c)=π v at h
  have hb : π (B b)=0 := LinearMap.congr_fun hB b
  rw [map_add,hb,zero_add,hv] at h
  exact h

def coordinates : (F → ℤ) ≃ₗ[ℤ] ((Q → ℤ) × (Fin (Fintype.card F-Fintype.card Q) → ℤ)) :=
  SplitSurjectionCoordinates.standardCoordinates (π.comp C) (frozen_surjective B C π hπ hB hfull)

def basis : Basis (Q ⊕ Fin (Fintype.card F-Fintype.card Q)) ℤ (F → ℤ) :=
  SplitSurjectionCoordinates.standardBasis (π.comp C) (frozen_surjective B C π hπ hB hfull)

include hπ hB hfull in
omit [Fintype V] in
theorem enough_frozen : Fintype.card Q≤Fintype.card F :=
  SplitSurjectionCoordinates.target_card_le (π.comp C) (frozen_surjective B C π hπ hB hfull)

omit [Fintype V] in
theorem basis_quotient (i : Q ⊕ Fin (Fintype.card F-Fintype.card Q)) :
    π (C (basis B C π hπ hB hfull i))=Sum.elim (fun q=>Pi.single q (1:ℤ)) (fun _=>0) i :=
  SplitSurjectionCoordinates.standardBasis_quotient (π.comp C) (frozen_surjective B C π hπ hB hfull) i

variable (hker : LinearMap.range B=LinearMap.ker π)
variable (s : (Q → ℤ) →ₗ[ℤ] (V → ℤ)) (hs : π.comp s=LinearMap.id)

def standardRow (i : Q ⊕ Fin (Fintype.card F-Fintype.card Q)) : V → ℤ :=
  s (Sum.elim (fun q=>Pi.single q (1:ℤ)) (fun _=>0) i)

include hker hs in
omit [Fintype V] in
theorem difference_in_mutable_rows (i : Q ⊕ Fin (Fintype.card F-Fintype.card Q)) :
    C (basis B C π hπ hB hfull i)-standardRow s i ∈ LinearMap.range B := by
  rw [hker]
  change π (_-_)=0
  have hs' (q : Q → ℤ) : π (s q)=q := LinearMap.congr_fun hs q
  rw [map_sub,basis_quotient,standardRow,hs',sub_self]

def mutableCorrection (i : Q ⊕ Fin (Fintype.card F-Fintype.card Q)) : V → ℤ :=
  (difference_in_mutable_rows B C π hπ hB hfull hker s hs i).choose

omit [Fintype V] in
theorem corrected_row (i : Q ⊕ Fin (Fintype.card F-Fintype.card Q)) :
    C (basis B C π hπ hB hfull i)=standardRow s i+B (mutableCorrection B C π hπ hB hfull hker s hs i) := by
  have h:=(difference_in_mutable_rows B C π hπ hB hfull hker s hs i).choose_spec
  change B (mutableCorrection B C π hπ hB hfull hker s hs i)=_ at h
  rw [h]
  abel

#print axioms frozen_surjective
#print axioms coordinates
#print axioms basis
#print axioms enough_frozen
#print axioms basis_quotient
#print axioms standardRow
#print axioms difference_in_mutable_rows
#print axioms mutableCorrection
#print axioms corrected_row

end Verification.FrozenQuotientCoordinates
