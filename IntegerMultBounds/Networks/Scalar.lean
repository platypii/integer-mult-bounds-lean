import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Algebraic components of the scalar motif and common-frame argument.
Residual spaces, sparse wire counts, and network-to-tape compilation are not
established by this file. -/

namespace IntegerMultBounds.Networks

section Restoration
variable {X A C : Type*} [AddCommGroup X] [AddCommGroup A] [AddCommGroup C]

/-- The eight scheduled updates, retaining arbitrary original scratch. -/
def dirtySchedule (V : X →+ A) (G : X →+ C) (J : A →+ X) (R : C →+ X)
    (x y : X) (a : A) (c : C) : X × X × A × C :=
  let y₀ := y - J a
  let y₁ := y₀ - R c
  let a₁ := a + V x
  let c₁ := c + G x
  let y₂ := y₁ + R c₁
  let y₃ := y₂ + J a₁
  let c₂ := c₁ - G x
  let a₂ := a₁ - V x
  (x, y₃, a₂, c₂)

theorem dirtySchedule_eq (V : X →+ A) (G : X →+ C) (J : A →+ X) (R : C →+ X)
    (x y : X) (a : A) (c : C) :
    dirtySchedule V G J R x y a c = (x, y + (J (V x) + R (G x)), a, c) := by
  simp only [dirtySchedule, map_add, add_sub_cancel_right]
  congr 2
  abel

theorem dirtySchedule_shear (V : X →+ A) (G : X →+ C) (J : A →+ X) (R : C →+ X)
    (identity : ∀ x, J (V x) + R (G x) = x) (x y : X) (a : A) (c : C) :
    dirtySchedule V G J R x y a c = (x, y + x, a, c) := by
  rw [dirtySchedule_eq, identity]

def signedExchange (x y : X) : X × X :=
  let y₁ := y + x
  let x₁ := x - y₁
  let y₂ := y₁ + x₁
  (x₁, y₂)

theorem signedExchange_eq (x y : X) : signedExchange x y = (-y, x) := by
  dsimp [signedExchange]
  congr 1 <;> abel
end Restoration

section TripleCoefficients
variable {α : Type*} [DecidableEq α]

theorem triple_inter_card (S T : Finset α) (hS : S.card = 3) (hT : T.card = 3) :
    (S ∩ T).card ≤ 3 ∧ ((S ∩ T).card = 3 ↔ S = T) := by
  constructor
  · simpa [hS] using Finset.card_le_card (Finset.inter_subset_left (s₁ := S) (s₂ := T))
  · constructor
    · intro h
      have hs : S ∩ T = S := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
      have ht : S ∩ T = T := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
      exact hs.symm.trans ht
    · rintro rfl
      simpa using hS

/-- Complex center coefficient plus the prescribed sparse side correction. -/
def complexCoefficient (S T : Finset α) : ℚ :=
  let j := (S ∩ T).card
  let center := ((j : ℚ) - 1) / 2
  center + if S ≠ T ∧ Even j then -center else 0

theorem complexCoefficient_eq (S T : Finset α) (hS : S.card = 3) (hT : T.card = 3) :
    complexCoefficient S T = if S = T then 1 else 0 := by
  obtain ⟨hle, heq⟩ := triple_inter_card S T hS hT
  by_cases h : S = T
  · subst T
    norm_num [complexCoefficient, hS]
  · have hne : (S ∩ T).card ≠ 3 := fun hh => h (heq.mp hh)
    have hlt : (S ∩ T).card < 3 := by omega
    have hj : (S ∩ T).card = 0 ∨ (S ∩ T).card = 1 ∨ (S ∩ T).card = 2 := by omega
    rcases hj with hj | hj | hj <;> norm_num [complexCoefficient, h, hj]

def bitCoefficient (S T : Finset α) : ℕ :=
  let j := (S ∩ T).card
  (j + if j = 1 then 1 else 0) % 2

theorem bitCoefficient_eq (S T : Finset α) (hS : S.card = 3) (hT : T.card = 3) :
    bitCoefficient S T = if S = T then 1 else 0 := by
  obtain ⟨hle, heq⟩ := triple_inter_card S T hS hT
  by_cases h : S = T
  · subst T
    norm_num [bitCoefficient, hS]
  · have hne : (S ∩ T).card ≠ 3 := fun hh => h (heq.mp hh)
    have hj : (S ∩ T).card = 0 ∨ (S ∩ T).card = 1 ∨ (S ∩ T).card = 2 := by omega
    rcases hj with hj | hj | hj <;> norm_num [bitCoefficient, h, hj]

/-- Summing the proved complex coefficients over all triples gives the identity
on the whole bank, at any finite ground size. -/
theorem complex_bank_identity [Fintype α] (S : {s : Finset α // s.card = 3})
    (x : {s : Finset α // s.card = 3} → ℚ) :
    ∑ T, complexCoefficient S.val T.val * x T = x S := by
  classical
  have hcoeff (T : {s : Finset α // s.card = 3}) :
      complexCoefficient S.val T.val = if S = T then 1 else 0 := by
    rw [complexCoefficient_eq _ _ S.property T.property]
    simp only [Subtype.ext_iff]
  simp [hcoeff]
end TripleCoefficients

section Frames
variable {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]

theorem frame_change (D E' : E ≃ₗ[R] E) (x : E) : E' (D.symm (D x)) = E' x := by simp

/-- All incidences of a gate use the same frame; this is the exact algebraic
condition needed to commute that frame through a pointwise linear gate. -/
theorem gate_frame {ι : Type*} (s : Finset ι) (coeff : ι → R) (x : ι → E)
    (D : E ≃ₗ[R] E) :
    ∑ i ∈ s, coeff i • D (x i) = D (∑ i ∈ s, coeff i • x i) := by
  simp
end Frames

end IntegerMultBounds.Networks
