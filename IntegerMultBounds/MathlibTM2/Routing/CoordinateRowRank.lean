module

public import IntegerMultBounds.MathlibTM2.Routing.ShiftedElementarySchedule
public import IntegerMultBounds.MathlibTM2.Node.Rect

/-! A coordinate permutation that preserves outer rows is the same local
permutation in every row. The argument is structural in the coordinate count. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

theorem coordinateRowRank_offset (R n : ℕ)
    (π : Equiv.Perm (Fin (R * 2 ^ n))) (σ : Equiv.Perm (Fin (2 ^ n)))
    (f : Fin n → Fin n)
    (hπ : ∀ i q, (π i).val.testBit q.val = i.val.testBit (f q).val)
    (hσ : ∀ i q, (σ i).val.testBit q.val = i.val.testBit (f q).val)
    (hrow : ∀ i, (π i).val / 2 ^ n = i.val / 2 ^ n)
    (row : Fin R) (i : Fin (2 ^ n)) :
    (π ⟨row.val * 2 ^ n + i.val, by
      have hm := Nat.mul_le_mul_right (2 ^ n) (Nat.succ_le_of_lt row.isLt)
      simp only [Nat.succ_mul] at hm
      omega⟩).val = row.val * 2 ^ n + (σ i).val := by
  let j : Fin (R * 2 ^ n) := ⟨row.val * 2 ^ n + i.val, by
    have hm := Nat.mul_le_mul_right (2 ^ n) (Nat.succ_le_of_lt row.isLt)
    simp only [Nat.succ_mul] at hm
    omega⟩
  have hi : j.val % 2 ^ n = i.val := by simp [j, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
  have ho : (row.val * 2 ^ n + (σ i).val) % 2 ^ n = (σ i).val := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt (σ i).isLt]
  apply eq_of_shifted_bits 0 n
  · intro q; exact Fin.elim0 q
  · funext q
    simp only [Nat.zero_add]
    have hin := congrArg (fun x : ℕ => x.testBit (f q).val) hi
    have hout := congrArg (fun x : ℕ => x.testBit q.val) ho
    simp only [Nat.testBit_mod_two_pow, (f q).isLt, q.isLt, decide_true, Bool.true_and] at hin hout
    exact (hπ j q).trans (hin.trans ((hσ i q).symm.trans hout.symm))
  · simp only [Nat.zero_add]
    rw [hrow]
    change (row.val * 2 ^ n + i.val) / 2 ^ n =
      (row.val * 2 ^ n + (σ i).val) / 2 ^ n
    rw [Nat.add_comm (row.val * 2 ^ n), Nat.add_mul_div_right _ _ (Nat.two_pow_pos n),
      Nat.add_comm (row.val * 2 ^ n), Nat.add_mul_div_right _ _ (Nat.two_pow_pos n),
      Nat.div_eq_of_lt i.isLt, Nat.div_eq_of_lt (σ i).isLt]

theorem coordinateRowRank_symm_offset (R n : ℕ)
    (π : Equiv.Perm (Fin (R * 2 ^ n))) (σ : Equiv.Perm (Fin (2 ^ n)))
    (f : Equiv.Perm (Fin n))
    (hπ : ∀ i q, (π i).val.testBit q.val = i.val.testBit (f q).val)
    (hσ : ∀ i q, (σ i).val.testBit q.val = i.val.testBit (f q).val)
    (hrow : ∀ i, (π i).val / 2 ^ n = i.val / 2 ^ n)
    (row : Fin R) (i : Fin (2 ^ n)) :
    (π.symm ⟨row.val * 2 ^ n + i.val, by
      have hm := Nat.mul_le_mul_right (2 ^ n) (Nat.succ_le_of_lt row.isLt)
      simp only [Nat.succ_mul] at hm
      omega⟩).val = row.val * 2 ^ n + (σ.symm i).val := by
  apply coordinateRowRank_offset R n π.symm σ.symm f.symm
  · intro j q
    simpa only [Equiv.apply_symm_apply] using (hπ (π.symm j) (f.symm q)).symm
  · intro j q
    simpa only [Equiv.apply_symm_apply] using (hσ (σ.symm j) (f.symm q)).symm
  · intro j
    simpa only [Equiv.apply_symm_apply] using (hrow (π.symm j)).symm

/-- Global record movement is the concatenation of the same local movement in
all outer rows, including for the inverse ranks used to read output records. -/
theorem moveRecs_coordinate_rows {α : Type*} (R n : ℕ)
    (π : Equiv.Perm (Fin (R * 2 ^ n))) (σ : Equiv.Perm (Fin (2 ^ n)))
    (f : Equiv.Perm (Fin n))
    (hπ : ∀ i q, (π i).val.testBit q.val = i.val.testBit (f q).val)
    (hσ : ∀ i q, (σ i).val.testBit q.val = i.val.testBit (f q).val)
    (hrow : ∀ i, (π i).val / 2 ^ n = i.val / 2 ^ n) (l : List (List α)) :
    IntegerMultBounds.MathlibTM2.Node.moveRecs π l =
      (List.ofFn fun row : Fin R => List.ofFn fun i : Fin (2 ^ n) =>
        l.getD (row.val * 2 ^ n + (σ.symm i).val) []).flatten := by
  unfold IntegerMultBounds.MathlibTM2.Node.moveRecs
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext row
  apply congrArg List.ofFn
  funext i
  rw [coordinateRowRank_symm_offset R n π σ f hπ hσ hrow row i]

end IntegerMultBounds.MathlibTM2.Routing
