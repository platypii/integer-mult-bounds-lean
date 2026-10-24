module

public import IntegerMultBounds.MathlibTM2.Routing.SelectiveIdeal

/-! Row-local destination keys for exact selective repair. These identities justify
omitting the row identifier when repair is executed separately within each row;
they do not supply the block driver or its execution bound. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable {p : Par} {X : ℕ}
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

/-- A selective update never crosses an outer row boundary. -/
theorem selectiveIdealIdx_row (i : ℕ) :
    selectiveIdealIdx p X active s i / 2 ^ fieldsLen (selectiveLen p X) =
      i / 2 ^ fieldsLen (selectiveLen p X) := by
  exact setDigit_div_total (selectiveLen p X) 1 _ i

private theorem selectiveDigit_mod (f : Fin 5) (i : ℕ) :
    digit (selectiveLen p X) f (i % 2 ^ fieldsLen (selectiveLen p X)) =
      digit (selectiveLen p X) f i := by
  rw [digit_eq_window, digit_eq_window,
    window_mod (fieldOff_add_le_total (selectiveLen p X) f)]

/-- The source observation is identical in every outer row. -/
theorem selectiveView_mod_row (i : ℕ) :
    selectiveView p X (i % 2 ^ fieldsLen (selectiveLen p X)) = selectiveView p X i := by
  simp only [selectiveView, selectiveDigit_mod]

/-- Routing a local address gives exactly the local part of the global destination. -/
theorem selectiveIdealIdx_mod_row (i : ℕ) :
    selectiveIdealIdx p X active s (i % 2 ^ fieldsLen (selectiveLen p X)) =
      selectiveIdealIdx p X active s i % 2 ^ fieldsLen (selectiveLen p X) := by
  apply eq_of_digit_eq (selectiveLen p X)
  · intro f
    rw [selectiveDigit_mod]
    simp only [selectiveIdealIdx, digit_setDigit, selectiveView_mod_row, selectiveDigit_mod]
  · rw [selectiveIdealIdx_row]
    simp

/-- Each outer row runs the same local permutation, with its original offset. -/
theorem selectiveIdealIdx_row_offset (row i : ℕ)
    (hi : i < 2 ^ fieldsLen (selectiveLen p X)) :
    selectiveIdealIdx p X active s (row * 2 ^ fieldsLen (selectiveLen p X) + i) =
      row * 2 ^ fieldsLen (selectiveLen p X) + selectiveIdealIdx p X active s i := by
  let N := 2 ^ fieldsLen (selectiveLen p X)
  have hN : 0 < N := by dsimp only [N]; positivity
  change i < N at hi
  have hm : (row * N + i) % N = i := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hi]
  have hd : (row * N + i) / N = row := by
    rw [Nat.add_comm, Nat.add_mul_div_right i row hN, Nat.div_eq_of_lt hi]
    simp
  have hlocal := selectiveIdealIdx_mod_row active s (row * N + i)
  change selectiveIdealIdx p X active s ((row * N + i) % N) =
    selectiveIdealIdx p X active s (row * N + i) % N at hlocal
  rw [hm] at hlocal
  have hrow := selectiveIdealIdx_row active s (row * N + i)
  change selectiveIdealIdx p X active s (row * N + i) / N = (row * N + i) / N at hrow
  rw [hd] at hrow
  have hsplit := Nat.mod_add_div (selectiveIdealIdx p X active s (row * N + i)) N
  rw [← hlocal, hrow] at hsplit
  change selectiveIdealIdx p X active s (row * N + i) = row * N + selectiveIdealIdx p X active s i
  simpa only [Nat.mul_comm, Nat.add_comm] using hsplit.symm

/-- Within a fixed row, destination keys need only the address bits. -/
theorem selectiveIdealIdx_row_key_injective (hK : 0 < p.K)
    (hs : ∀ c, (s c).Allowed active) (row : ℕ) :
    Set.InjOn (fun i => selectiveIdealIdx p X active s i %
      2 ^ fieldsLen (selectiveLen p X))
      {i | i / 2 ^ fieldsLen (selectiveLen p X) = row} := by
  intro i hi j hj hkey
  dsimp only at hkey
  have hrow : selectiveIdealIdx p X active s i / 2 ^ fieldsLen (selectiveLen p X) =
      selectiveIdealIdx p X active s j / 2 ^ fieldsLen (selectiveLen p X) := by
    rw [selectiveIdealIdx_row, selectiveIdealIdx_row]
    exact hi.trans hj.symm
  have he : selectiveIdealIdx p X active s i = selectiveIdealIdx p X active s j := by
    have hi' := Nat.mod_add_div (selectiveIdealIdx p X active s i)
      (2 ^ fieldsLen (selectiveLen p X))
    have hj' := Nat.mod_add_div (selectiveIdealIdx p X active s j)
      (2 ^ fieldsLen (selectiveLen p X))
    rw [hkey, hrow] at hi'
    exact hi'.symm.trans hj'
  exact (selectiveIdealIdx_involutive hK active s hs).injective he

/-- Restrict the all-address ideal to one row, without changing its action. -/
def selectiveRowPerm (hK : 0 < p.K) (hs : ∀ c, (s c).Allowed active) (row : ℕ) :
    Equiv.Perm {i : ℕ // i / 2 ^ fieldsLen (selectiveLen p X) = row} where
  toFun i := ⟨selectiveIdealIdx p X active s i,
    (selectiveIdealIdx_row active s i).trans i.property⟩
  invFun i := ⟨selectiveIdealIdx p X active s i,
    (selectiveIdealIdx_row active s i).trans i.property⟩
  left_inv i := Subtype.ext (selectiveIdealIdx_involutive hK active s hs i)
  right_inv i := Subtype.ext (selectiveIdealIdx_involutive hK active s hs i)

end IntegerMultBounds.MathlibTM2.Routing
