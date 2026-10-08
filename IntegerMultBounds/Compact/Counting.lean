import IntegerMultBounds.Compact.ExactRepair
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.BigOperators

/-! Exact finite counts for the actual packed-address predicates used by
exceptional repair. The radix bijection transfers independent digit counts
to complete packed fields. No probabilistic independence is assumed. -/

namespace IntegerMultBounds.Compact
open Radix

instance fieldFintype (M : ℤ) : Fintype (Field M) :=
  inferInstanceAs (Fintype (Set.Ico 0 M))

theorem card_field (M : ℤ) : Nat.card (Field M) = M.toNat := by
  change Nat.card (Set.Ico 0 M) = _
  simp [Nat.card_eq_fintype_card]

/-- Restricting every decoded digit is equivalent to choosing a restricted
digit independently at each position. -/
def restrictedRadixEquiv (B : ℤ) (hB : 0 < B) (n : ℕ) (P : ℤ → Prop) :
    {x : Field (B ^ n) // ∀ d ∈ digits B n x.val, P d} ≃
      (Fin n → {d : Field B // P d.val}) where
  toFun := fun x i =>
    let ds := digits B n x.val.val
    have hi : i.val < ds.length := by simp [ds, digits_length]
    ⟨⟨ds[i.val], digits_bounded B hB n x.val.val _ (List.getElem_mem hi)⟩,
      x.property _ (List.getElem_mem hi)⟩
  invFun := fun f =>
    let ds := List.ofFn (fun i => (f i).val.val)
    have hb : Bounded B ds := by
      intro d hd
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
      exact (f i).val.property
    ⟨⟨pack B ds, by simpa [ds] using pack_bounds B hB ds hb⟩, by
      have he : digits B n (pack B ds) = ds := by
        simpa [ds] using digits_pack B hB ds hb
      rw [he]
      intro d hd
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
      exact (f i).property⟩
  left_inv := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    dsimp
    have he : (List.ofFn fun i : Fin n =>
        (digits B n x.val.val)[i.val]'(by simp [digits_length])) =
        digits B n x.val.val := by
      apply List.ext_getElem
      · simp [digits_length]
      · intro i hi hj
        simp
    rw [he]
    exact pack_digits B hB n x.val.val x.val.property
  right_inv := by
    intro f
    funext i
    apply Subtype.ext
    apply Subtype.ext
    dsimp
    have hb : Bounded B (List.ofFn fun j => (f j).val.val) := by
      intro d hd
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hd
      exact (f j).val.property
    have he := digits_pack B hB _ hb
    simp only [List.length_ofFn] at he
    simp [he]

theorem card_restricted_field (B : ℤ) (hB : 0 < B) (n : ℕ) (P : ℤ → Prop) :
    Nat.card {x : Field (B ^ n) // ∀ d ∈ digits B n x.val, P d} =
      Nat.card {d : Field B // P d.val} ^ n := by
  rw [Nat.card_congr (restrictedRadixEquiv B hB n P), Nat.card_fun]
  simp

/-- The guard on the quotient by two is an ordinary half-open digit interval. -/
theorem guard_interval (B L v : ℤ) :
    Guard B L v ↔ 4 * B ≤ v ∧ v < 2 * L - 4 * B := by
  unfold Guard
  omega

def guardedDigitEquiv (B L : ℤ) (hB : 0 ≤ B) :
    {v : Field (2 * L) // Guard B L v.val} ≃ Set.Ico (4 * B) (2 * L - 4 * B) where
  toFun := fun v => ⟨v.val.val, (guard_interval B L v.val.val).mp v.property⟩
  invFun := fun v => ⟨⟨v.val, by
    have hv : 4 * B ≤ v.val ∧ v.val < 2 * L - 4 * B := v.property
    constructor <;> omega⟩,
    (guard_interval B L v.val).mpr v.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

theorem card_guarded_digit (B L : ℤ) (hB : 0 ≤ B) :
    Nat.card {v : Field (2 * L) // Guard B L v.val} = (2 * L - 8 * B).toNat := by
  rw [Nat.card_congr (guardedDigitEquiv B L hB)]
  simp only [Nat.card_eq_fintype_card]
  rw [Fintype.card_ofFinset (Finset.Ico (4 * B) (2 * L - 4 * B)) (by simp), Int.card_Ico]
  congr 1
  ring

def unsaturatedDigitEquiv (B : ℤ) :
    {w : Field B // w.val < B - 1} ≃ Field (B - 1) where
  toFun := fun w => ⟨w.val.val, w.val.property.1, w.property⟩
  invFun := fun w => ⟨⟨w.val, w.property.1, by have := w.property.2; omega⟩, w.property.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

theorem card_unsaturated_digit (B : ℤ) :
    Nat.card {w : Field B // w.val < B - 1} = (B - 1).toNat := by
  rw [Nat.card_congr (unsaturatedDigitEquiv B), card_field]

def earlyGoodEquiv (B L : ℤ) (n : ℕ) :
    {x : EarlyAddress B L n // earlyGood B L n x} ≃
      {v : Field ((2 * L) ^ n) // ∀ d ∈ digits (2 * L) n v.val, Guard B L d} ×
      {w : Field (B ^ n) // ∀ d ∈ digits B n w.val, d < B - 1} :=
  Equiv.subtypeProdEquivProd
    (p := fun v : Field ((2 * L) ^ n) => ∀ d ∈ digits (2 * L) n v.val, Guard B L d)
    (q := fun w : Field (B ^ n) => ∀ d ∈ digits B n w.val, d < B - 1)

theorem card_earlyGood (B L : ℤ) (hB : 0 < B) (hL : 0 < L) (n : ℕ) :
    Nat.card {x : EarlyAddress B L n // earlyGood B L n x} =
      (2 * L - 8 * B).toNat ^ n * (B - 1).toNat ^ n := by
  rw [Nat.card_congr (earlyGoodEquiv B L n), Nat.card_prod,
    card_restricted_field (2 * L) (by omega), card_restricted_field B hB,
    card_guarded_digit B L hB.le, card_unsaturated_digit]

def lateGoodEquiv (B L : ℤ) (n : ℕ) :
    {x : LateAddress B L n // lateGood B L n x} ≃
      {u : Field (B ^ n) // ∀ d ∈ digits B n u.val, d < B - 1} ×
      {x : EarlyAddress B L n // earlyGood B L n x} :=
  (Equiv.subtypeEquiv (Equiv.refl (LateAddress B L n))
    (fun _ => and_comm)).trans Equiv.subtypeProdEquivProd

theorem card_lateGood (B L : ℤ) (hB : 0 < B) (hL : 0 < L) (n : ℕ) :
    Nat.card {x : LateAddress B L n // lateGood B L n x} =
      (B - 1).toNat ^ n * ((2 * L - 8 * B).toNat ^ n * (B - 1).toNat ^ n) := by
  rw [Nat.card_congr (lateGoodEquiv B L n), Nat.card_prod,
    card_restricted_field B hB, card_unsaturated_digit, card_earlyGood B L hB hL]

theorem card_earlyAddress (B L : ℤ) (n : ℕ) :
    Nat.card (EarlyAddress B L n) = ((2 * L) ^ n).toNat * (B ^ n).toNat := by
  rw [Nat.card_prod, card_field, card_field]

theorem card_lateAddress (B L : ℤ) (n : ℕ) :
    Nat.card (LateAddress B L n) =
      (B ^ n).toNat * (((2 * L) ^ n).toNat * (B ^ n).toNat) := by
  rw [Nat.card_prod, card_field, card_earlyAddress]

/-- These are counts of the predicates actually inspected by destination repair. -/
theorem card_earlyBad (B L : ℤ) (hB : 0 < B) (hL : 0 < L) (n : ℕ) :
    Nat.card {x : EarlyAddress B L n // ¬earlyGood B L n x} =
      ((2 * L) ^ n).toNat * (B ^ n).toNat -
        (2 * L - 8 * B).toNat ^ n * (B - 1).toNat ^ n := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    card_earlyAddress, card_earlyGood B L hB hL]

theorem card_lateBad (B L : ℤ) (hB : 0 < B) (hL : 0 < L) (n : ℕ) :
    Nat.card {x : LateAddress B L n // ¬lateGood B L n x} =
      (B ^ n).toNat * (((2 * L) ^ n).toNat * (B ^ n).toNat) -
        (B - 1).toNat ^ n * ((2 * L - 8 * B).toNat ^ n * (B - 1).toNat ^ n) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    card_lateAddress, card_lateGood B L hB hL]

end IntegerMultBounds.Compact
