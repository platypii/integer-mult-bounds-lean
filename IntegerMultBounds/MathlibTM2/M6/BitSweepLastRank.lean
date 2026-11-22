module

public import IntegerMultBounds.Machine.FlatCoordinateLayout

/-! The last destination has the largest coordinate on every axis. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine.FlatCoordinateLayout

theorem lastRank_coordinates {M d : ℕ} [NeZero M] (k : Fin d) :
    (coordinates (⟨M^d-1,by have := pow_pos (NeZero.pos M) d; omega⟩ : Fin (M^d)) k).val = M-1 := by
  have pos := NeZero.pos M
  let top : ZMod M := (M-1 : ℕ)
  have digit : top.val = M-1 := by simp [top,ZMod.val_natCast,Nat.mod_eq_of_lt (by omega : M-1 < M)]
  have sum (e : ℕ) : (∑ i : Fin e, (M-1)*M^i.val)+1 = M^e := by
    induction e with
    | zero => simp
    | succ e ih =>
      rw [Fin.sum_univ_castSucc,pow_succ]
      simp only [Fin.val_castSucc,Fin.val_last]
      have h : M-1+1 = M := by omega
      nlinarith only [ih,congrArg (fun a => a*M^e) h]
  have index : rank (fun _ : Fin d => top) = ⟨M^d-1,by have := pow_pos pos d; omega⟩ := by
    apply Fin.ext
    simp only [rank,finFunctionFinEquiv_apply,finEquiv_symm_val,digit]
    have := sum d
    omega
  rw [← index,coordinates_rank,digit]

end IntegerMultBounds.MathlibTM2.M6.BitNode
