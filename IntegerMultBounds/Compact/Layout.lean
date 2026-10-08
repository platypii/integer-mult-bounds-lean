import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

/-!
The complete-field part of the reservation invariant. A role split changes
only the row coordinate; the entire suffix (including arbitrary temporary
fields and payloads) is retained. No fixed-tape implementation is asserted here.
-/

namespace IntegerMultBounds.Compact.Layout

/-- Reindex complete rows into roles, retaining every within-row coordinate. -/
def splitRows (rows roles : ℕ) (Suffix : Type*) :
    (Fin (rows * roles) × Suffix) ≃ (Fin roles × (Fin rows × Suffix)) :=
  (Equiv.prodCongr finProdFinEquiv.symm (Equiv.refl Suffix)).trans {
    toFun := fun ((g, w), a) => (w, (g, a))
    invFun := fun (w, (g, a)) => ((g, w), a)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem split_preserves_suffix (rows roles : ℕ) {Suffix : Type*}
    (x : Fin (rows * roles) × Suffix) :
    (splitRows rows roles Suffix x).2.2 = x.2 := rfl

theorem merge_preserves_suffix (rows roles : ℕ) {Suffix : Type*}
    (x : Fin roles × (Fin rows × Suffix)) :
    ((splitRows rows roles Suffix).symm x).2 = x.2.2 := rfl

/-- Every role has every suffix value for every one of its row indices. -/
theorem complete_role (rows roles : ℕ) {Suffix : Type*}
    (w : Fin roles) (g : Fin rows) (a : Suffix) :
    ∃ x, splitRows rows roles Suffix x = (w, (g, a)) :=
  ⟨(splitRows rows roles Suffix).symm (w, (g, a)),
    (splitRows rows roles Suffix).apply_symm_apply _⟩

theorem role_volume (rows roles : ℕ) (Suffix : Type*) [Fintype Suffix] :
    Fintype.card (Fin (rows * roles) × Suffix) =
      roles * Fintype.card (Fin rows × Suffix) := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

/-- Padding adds whole rows to the next multiple, never individual suffixes. -/
def paddedRows (rows unit : ℕ) : ℕ := rows + (unit - rows % unit) % unit

theorem padding_bounds (rows unit : ℕ) (hu : 0 < unit) (hur : unit ≤ rows) :
    rows ≤ paddedRows rows unit ∧ paddedRows rows unit < rows + unit ∧
    paddedRows rows unit ≤ 2 * rows ∧ unit ∣ paddedRows rows unit := by
  have hr := Nat.mod_lt rows hu
  have hp := Nat.mod_lt (unit - rows % unit) hu
  have hd : (paddedRows rows unit) % unit = 0 := by
    unfold paddedRows
    rw [Nat.add_mod, Nat.mod_mod]
    by_cases hzero : rows % unit = 0
    · simp [hzero]
    · have hsmall : unit - rows % unit < unit := by omega
      rw [Nat.mod_eq_of_lt hsmall]
      have : rows % unit + (unit - rows % unit) = unit := by omega
      rw [this, Nat.mod_self]
  exact ⟨by unfold paddedRows; omega, by unfold paddedRows; omega,
    by unfold paddedRows; omega, Nat.dvd_of_mod_eq_zero hd⟩

/-- Reservation counts allocate enough actual bits, with less than one chunk
of waste per range. -/
theorem ceiling_chunks (bits width : ℕ) (hw : 0 < width) :
    bits ≤ ((bits + width - 1) / width) * width ∧
    ((bits + width - 1) / width) * width < bits + width := by
  have hr := Nat.mod_lt (bits + width - 1) hw
  have heq := Nat.mod_add_div (bits + width - 1) width
  have hm := Nat.div_mul_le_self (bits + width - 1) width
  rw [Nat.mul_comm width] at heq
  omega

end IntegerMultBounds.Compact.Layout
