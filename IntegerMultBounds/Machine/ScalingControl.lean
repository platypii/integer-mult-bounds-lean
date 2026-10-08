import IntegerMultBounds.Machine.ScalingPieces
import Mathlib.Data.ZMod.Basic

/-! Fixed-multiplier finite control for piece selection in unit scaling. The
lookup has c possible modulus residues and c control states, independently of
the array length Q. Advancing an output address advances just one finite
residue state. Source pieces are contiguous clipped ceiling intervals. These
are arithmetic and control semantics, without a tape-transition cost claim. -/

namespace IntegerMultBounds.Machine.ScalingControl

open ScalingPieces

/-- The finite residue stored by the streaming control. -/
def residue {c : ℕ} (hc : 0 < c) (z : ℕ) : Fin c := ⟨z % c,Nat.mod_lt _ hc⟩

/-- Finite table indexed only by Q modulo c and the current output residue. -/
def table {c : ℕ} (hc : 0 < c) (modulus current : Fin c) : Fin c := by
  letI : NeZero c := ⟨by omega⟩
  exact ⟨(-(current.val : ZMod c) * (modulus.val : ZMod c)⁻¹).val,ZMod.val_lt _⟩

/-- The unique stream index is obtained from the same fixed c-by-c table. -/
def select {c : ℕ} (hc : 0 < c) (Q z : ℕ) : Fin c := table hc (residue hc Q) (residue hc z)

/-- One fixed finite-state increment, with no scan of the representation of Q. -/
def advance {c : ℕ} (hc : 0 < c) (current : Fin c) : Fin c := residue hc (current.val + 1)

theorem advance_residue {c : ℕ} (hc : 0 < c) (z : ℕ) :
    advance hc (residue hc z) = residue hc (z + 1) := by
  apply Fin.ext
  change (z % c + 1) % c = (z + 1) % c
  simp [Nat.add_mod]

/-- Iterating the finite-state transition tracks the increasing output cursor. -/
theorem iterate_advance {c : ℕ} (hc : 0 < c) (start n : ℕ) :
    (advance hc)^[n] (residue hc start) = residue hc (start + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,advance_residue]
    congr 1

theorem select_residues {c : ℕ} (hc : 0 < c) {Q Q' z z' : ℕ}
    (hQ : Q % c = Q' % c) (hz : z % c = z' % c) : select hc Q z = select hc Q' z' := by
  have hmod : residue hc Q = residue hc Q' := Fin.ext hQ
  have hcur : residue hc z = residue hc z' := Fin.ext hz
  rw [select,select,hmod,hcur]

private theorem select_cast {c : ℕ} (hc : 0 < c) (Q z : ℕ) :
    ((select hc Q z).val : ZMod c) = -(z : ZMod c) * (Q : ZMod c)⁻¹ := by
  let : NeZero c := ⟨by omega⟩
  dsimp only [select,table]
  rw [ZMod.natCast_zmod_val]
  simp only [residue,ZMod.natCast_mod]

/-- The table really chooses an integral source reconstruction. -/
theorem select_admissible {Q c : ℕ} (hc : 0 < c) (hcop : c.Coprime Q) (z : ℕ) :
    AdmissiblePiece Q c z (select hc Q z).val := by
  refine ⟨(select hc Q z).isLt,?_⟩
  apply (ZMod.natCast_eq_zero_iff _ c).mp
  push_cast
  rw [select_cast,mul_assoc,mul_comm ((Q : ZMod c)⁻¹),ZMod.coe_mul_inv_eq_one Q hcop.symm]
  ring

/-- The finite lookup agrees with the uniquely admissible piece of every output. -/
theorem select_unique {Q c z j : ℕ} (hQ : 0 < Q) (hc : 0 < c)
    (hcop : c.Coprime Q) (hz : z < Q) (hj : AdmissiblePiece Q c z j) :
    j = (select hc Q z).val := by
  obtain ⟨k,_,hunique⟩ := existsUnique_piece hQ hc hcop hz
  exact (hunique j hj).trans (hunique _ (select_admissible hc hcop z)).symm

/-- Every table-selected source is in range and maps back to the requested output. -/
theorem selected_source {Q c z : ℕ} (hQ : 0 < Q) (hc : 0 < c)
    (hcop : c.Coprime Q) (hz : z < Q) :
    let j := (select hc Q z).val
    restore Q c z j < Q ∧ output Q c (restore Q c z j) = z ∧
      piece Q c (restore Q c z j) = j := by
  have hj := select_admissible hc hcop z
  exact ⟨restore_lt hc hz hj,output_restore hz hj,piece_restore hQ hz hj⟩

/-- During an increasing output sweep the selected source stream is read from
one finite state; the state set and transition never depend on Q. -/
theorem sweep_select {Q c : ℕ} (hc : 0 < c) (z : ℕ) :
    table hc (residue hc Q) ((advance hc)^[z] (residue hc 0)) = select hc Q z := by
  rw [iterate_advance,zero_add]
  rfl

/-- Natural ceiling division for a positive fixed divisor. -/
def ceiling (x c : ℕ) : ℕ := (x + c - 1) / c

theorem ceiling_le_iff {c x y : ℕ} (hc : 0 < c) : ceiling x c ≤ y ↔ x ≤ c * y := by
  have hh := Nat.div_lt_iff_lt_mul (k := c) (x := x + c - 1) (y := y + 1) hc
  simp only [Nat.add_mul,Nat.one_mul,Nat.mul_comm y c] at hh
  change (x + c - 1) / c ≤ y ↔ x ≤ c * y
  omega

/-- Endpoints are clipped because some pieces can be empty when c exceeds Q. -/
def boundary (Q c j : ℕ) : ℕ := min Q (ceiling (j * Q) c)

theorem boundary_le (Q c j : ℕ) : boundary Q c j ≤ Q := Nat.min_le_left _ _

/-- The complete source stream for piece j is the half-open interval between
successive clipped ceiling endpoints. -/
theorem piece_interval {Q c y j : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hy : y < Q) :
    piece Q c y = j ↔ boundary Q c j ≤ y ∧ y < boundary Q c (j + 1) := by
  have hl := ceiling_le_iff (x := j * Q) (y := y) hc
  have hu := ceiling_le_iff (x := (j + 1) * Q) (y := y) hc
  have hdl := Nat.le_div_iff_mul_le (k := Q) (x := j) (y := c * y) hQ
  have hdu := Nat.div_lt_iff_lt_mul (k := Q) (x := c * y) (y := j + 1) hQ
  dsimp only [piece,boundary]
  omega

theorem boundary_zero {Q c : ℕ} (hc : 0 < c) : boundary Q c 0 = 0 := by
  have hh := (ceiling_le_iff (x := 0) (y := 0) hc).mpr (by simp)
  simp only [boundary,zero_mul]
  omega

theorem boundary_last {Q c : ℕ} (hc : 0 < c) : boundary Q c c = Q := by
  have hl := (ceiling_le_iff (x := c * Q) (y := Q) hc).mpr le_rfl
  have hu := (ceiling_le_iff (x := c * Q) (y := ceiling (c * Q) c) hc).mp le_rfl
  have hh : ceiling (c * Q) c = Q := by nlinarith
  simp only [boundary,hh,Nat.min_self]

/-- Each canonical input belongs to the interval of its actual quotient piece. -/
theorem source_interval {Q c y : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hy : y < Q) :
    boundary Q c (piece Q c y) ≤ y ∧ y < boundary Q c (piece Q c y + 1) :=
  (piece_interval hQ hc hy).mp rfl

/-- Contiguous interval form of the exact source-address set for one piece. -/
theorem source_set {Q c j : ℕ} (hQ : 0 < Q) (hc : 0 < c) :
    (Finset.range Q).filter (fun y => piece Q c y = j) =
      Finset.Ico (boundary Q c j) (boundary Q c (j + 1)) := by
  ext y
  simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
  constructor
  · rintro ⟨hy,hj⟩
    exact (piece_interval hQ hc hy).mp hj
  · intro hj
    have hy : y < Q := lt_of_lt_of_le hj.2 (boundary_le Q c (j + 1))
    exact ⟨hy,(piece_interval hQ hc hy).mpr hj⟩

/-- Exact number of source blocks assigned to a piece, including empty pieces. -/
theorem source_count {Q c j : ℕ} (hQ : 0 < Q) (hc : 0 < c) :
    ((Finset.range Q).filter (fun y => piece Q c y = j)).card =
      boundary Q c (j + 1) - boundary Q c j := by
  rw [source_set hQ hc,Nat.card_Ico]

end IntegerMultBounds.Machine.ScalingControl
