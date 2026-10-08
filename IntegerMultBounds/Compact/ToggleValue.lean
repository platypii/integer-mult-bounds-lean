import IntegerMultBounds.Compact.PackedArithValue
import IntegerMultBounds.Compact.Ideal

/-! The ideal selected-parity toggle on bit words: exclusive or with the
control mask, the control bits at stride `q`, flips the lowest bit of each
`q`-bit block exactly when its control is set, and packs as `toggleList` of
the block digits. -/

namespace IntegerMultBounds.Compact.PowerTwo

open IntegerMultBounds.Counter (value)
open IntegerMultBounds.Machine.PackedArith (controlsAt)
open IntegerMultBounds.Machine.Gather (field gather digitWord)
open IntegerMultBounds.Machine.ColumnTransducer (value_append)
open Radix

/-- The control mask: each control bit followed by `q - 1` zeros. -/
def toggleMask (q : ℕ) (zs : List Bool) : List Bool :=
  (zs.map fun z => z :: List.replicate (q - 1) false).flatten

theorem toggleMask_nil (q : ℕ) : toggleMask q [] = [] := rfl

theorem toggleMask_cons (q : ℕ) (z : Bool) (zs : List Bool) :
    toggleMask q (z :: zs) = (z :: List.replicate (q - 1) false) ++ toggleMask q zs := by
  simp [toggleMask]

theorem toggleMask_length (q : ℕ) (hq : 1 ≤ q) (zs : List Bool) :
    (toggleMask q zs).length = zs.length * q := by
  induction zs with
  | nil => simp [toggleMask]
  | cons z zs ih =>
    simp only [toggleMask_cons, List.length_append, List.length_cons, List.length_replicate, ih,
      Nat.succ_mul]
    omega

/-- The controls gather is the control mask. -/
theorem gather_controls (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) (X zs : List Bool) :
    gather (fun _ z => z) (controlsAt q b hb hbq) X zs zs.length = toggleMask q zs := by
  rw [gather_flatten, toggleMask]
  conv_rhs => rw [list_eq_range zs, List.map_map]
  congr 1

theorem zipWith_append_eq {α β γ : Type*} (f : α → β → γ) (A R : List α) (D P : List β)
    (h : A.length = D.length) :
    List.zipWith f (A ++ R) (D ++ P) = List.zipWith f A D ++ List.zipWith f R P := by
  induction A generalizing D with
  | nil => cases D <;> simp_all
  | cons a A ih =>
    cases D with
    | nil => simp at h
    | cons d D => simp [ih D (by simpa using h)]

theorem zipWith_xor_zeros (A : List Bool) :
    List.zipWith xor A (List.replicate A.length false) = A := by
  induction A with
  | nil => rfl
  | cons a A ih => simp [List.replicate_succ, ih]

/-- Toggling one block. -/
theorem value_block_toggle (A : List Bool) (q : ℕ) (hA : A.length = q) (hq : 1 ≤ q) (z : Bool) :
    (value (List.zipWith xor A (z :: List.replicate (q - 1) false)) : ℤ) =
      toggle (value A) (ctrl z) := by
  obtain ⟨a, A', rfl⟩ : ∃ a A', A = a :: A' := by
    cases A with
    | nil => simp at hA; omega
    | cons a A' => exact ⟨a, A', rfl⟩
  have hl : A'.length = q - 1 := by simp at hA; omega
  rw [List.zipWith_cons_cons, ← hl, zipWith_xor_zeros]
  simp only [value, toggle]
  push_cast
  have h2 : ((if a then 1 else 0 : ℕ) + 2 * value A' : ℤ) % 2 = if a then 1 else 0 := by
    cases a <;> simp [Int.add_mul_emod_self_left]
  cases a <;> cases z <;> simp [ctrl]
  all_goals ring

/-- The exclusive or with the control mask packs as the toggled digits. -/
theorem toggle_word_value (q : ℕ) (hq : 1 ≤ q) (V zs : List Bool) (hV : V.length = zs.length * q) :
    (value (List.zipWith xor V (toggleMask q zs)) : ℤ) =
      pack ((2 : ℤ) ^ q) (toggleList (digits ((2 : ℤ) ^ q) zs.length (value V)) (zs.map ctrl)) := by
  rw [digits_blocks V q zs.length hV]
  induction zs generalizing V with
  | nil =>
    have : V = [] := List.eq_nil_of_length_eq_zero (by simp [hV])
    subst this
    simp [toggleMask, blockValues, toggleList, pack, value]
  | cons z zs ih =>
    simp only [List.length_cons] at hV ⊢
    have hq' : q ≤ V.length := by rw [hV]; nlinarith
    have hdrop : (V.drop q).length = zs.length * q := by
      rw [List.length_drop, hV]; simp [Nat.succ_mul]
    have htake : (V.take q).length = q := by rw [List.length_take, min_eq_left hq']
    rw [blockValues_succ V q zs.length hq', toggleMask_cons, List.map_cons, toggleList,
      List.zipWith_cons_cons, pack, ← toggleList, ← ih (V.drop q) hdrop]
    conv_lhs => rw [← List.take_append_drop q V]
    rw [zipWith_append_eq _ _ _ _ _ (by simp [htake]; omega), value_append, List.length_zipWith, htake,
      List.length_cons, List.length_replicate, show q - 1 + 1 = q by omega, min_self]
    push_cast
    rw [value_block_toggle (V.take q) q htake hq z]

end IntegerMultBounds.Compact.PowerTwo
