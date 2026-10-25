module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStageValues
import Mathlib.Data.List.GetD

/-! # Ambient row coordinates of reversed compact streams

Output weights use exactly the compact row order produced by the interior
kernel. The index identities are structural and do not alter phase coordinates.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem cellIndex_row {M L : ℕ} (n : Fin M) (i : Fin L) :
    (cellIndex n i).val / L = n.val := by
  have hL : 0 < L := Nat.zero_lt_of_lt i.isLt
  have hr : L - 1 - i.val < L := by omega
  change (n.val * L + (L - 1 - i.val)) / L = n.val
  rw [Nat.add_comm, Nat.mul_comm n.val L, Nat.add_mul_div_left _ _ hL, Nat.div_eq_of_lt hr, Nat.zero_add]

theorem cellIndex_coordinate {M L : ℕ} (n : Fin M) (i : Fin L) :
    L - 1 - (cellIndex n i).val % L = i.val := by
  have hr : L - 1 - i.val < L := by omega
  change L - 1 - (n.val * L + (L - 1 - i.val)) % L = i.val
  rw [Nat.add_comm, Nat.mul_comm n.val L, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  omega

/-- A table stored in the actual reversed order of each compact row. -/
def reversedRowTable {K : Type*} (M L : ℕ) (f : ℕ → ℕ → K) : List K :=
  List.ofFn (fun i : Fin (M * L) => f (i.val / L) (L - 1 - i.val % L))

@[simp] theorem reversedRowTable_length {K : Type*} (M L : ℕ) (f : ℕ → ℕ → K) :
    (reversedRowTable M L f).length = M * L := by simp [reversedRowTable]

/-- Cropping a compact coordinate selects its actual row and cell coordinate. -/
theorem reversedRowTable_getD {K : Type*} (f : ℕ → ℕ → K) (default : K)
    {M L : ℕ} (n : Fin M) (i : Fin L) :
    (reversedRowTable M L f).getD (cellIndex n i).val default = f n i := by
  have hi : (cellIndex n i).val < (reversedRowTable M L f).length := by
    simpa only [reversedRowTable_length] using (cellIndex n i).isLt
  rw [List.getD_eq_getElem _ _ hi]
  simp only [reversedRowTable, List.getElem_ofFn, cellIndex_row, cellIndex_coordinate]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
