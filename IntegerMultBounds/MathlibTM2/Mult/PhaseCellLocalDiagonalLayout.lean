module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLocalRecoveryLayout
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiagonalBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedDiagonalPage

/-! Reuse cleared recovery work for diagonal roles, multiplier and page setup. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM
noncomputable section

local instance : Fintype RsbR := Fintype.ofList
  ((([CR.xs,.ys,.xsv,.ysv,.acc,.out,.wn,.pn,.nn,.tmp,.u0,.u1,.u2,.u3,.ma,.mb,.mc,.md,.sa,.sb,.sc,.sd,.p1,.p2,.p3,.p4,.qr,.qi,.sr,.si]).map RsbR.cm) ++
    [.src,.dst,.msk,.ms,.mwn,.m2wn,.m2n,.kn,.sn,.smwn,.tswn,.ef,.df,.hf,.tK,.tL,.tJ,.tC,.tA,
      .sr,.sel,.hv,.vk,.b1,.ya,.tb,.xa,.xs,.pr,.hc,.ac,.ac2,.nv,.dout,.bx,.bo,.dtab,.padc,.prm])
  (by intro i; cases i <;> simp; rename_i c; cases c <;> simp)
local instance : Fintype (TblR 48) := Fintype.ofList
  ((List.finRange 48).map TblR.v ++ [.wr,.wn,.acc] ++ (List.finRange 12).map TblR.z)
  (by intro i; cases i <;> simp)

private theorem rsb_card : Fintype.card RsbR ≤ 100 := by decide +kernel
private theorem table_card : Fintype.card (TblR 48) ≤ 90 := by decide +kernel

def diagonalRoleIndex (r : RsbR) : Fin 392 :=
  ⟨(Fintype.equivFin RsbR r).val,by have := (Fintype.equivFin RsbR r).isLt; have := rsb_card; omega⟩
def diagonalMulIndex (i : Fin 64) : Fin 392 := ⟨100+i.val,by omega⟩
def diagonalTableIndex (r : TblR 48) : Fin 392 :=
  ⟨200+(Fintype.equivFin (TblR 48) r).val,by
    have := (Fintype.equivFin (TblR 48) r).isLt; have := table_card; omega⟩

def diagonalRole (r : RsbR) : Fin tapes := recovery (.work (diagonalRoleIndex r))
def diagonalMul (i : Fin 64) : Fin tapes := recovery (.work (diagonalMulIndex i))
def diagonalTable (r : TblR 48) : Fin tapes := recovery (.work (diagonalTableIndex r))
def diagonalClock : Fin tapes := recovery (.work 300)
def diagonalBytes : Fin tapes := recovery (.work 301)
def diagonalSaved : Fin tapes := recovery (.work 302)
def diagonalTmp : Fin tapes := recovery (.work 303)
def diagonalQueue : Fin tapes := recovery (.control .cropDst)

private theorem work_injective : Function.Injective (fun i => recovery (.work i)) := by
  intro i j h; exact RecoveryBank.work.inj (recovery_injective h)

theorem diagonalRole_injective : Function.Injective diagonalRole := by
  intro r s h
  apply (Fintype.equivFin RsbR).injective
  have hh := congrArg (fun i : Fin 392 => i.val) (work_injective h)
  exact Fin.ext hh
theorem diagonalMul_injective : Function.Injective diagonalMul := by
  intro i j h
  apply Fin.ext
  have hh := congrArg Fin.val (work_injective h)
  change 100+i.val = 100+j.val at hh
  omega
theorem diagonalTable_injective : Function.Injective diagonalTable := by
  intro r s h
  apply (Fintype.equivFin (TblR 48)).injective
  apply Fin.ext
  have hh := congrArg Fin.val (work_injective h)
  change 200+(Fintype.equivFin (TblR 48) r).val = 200+(Fintype.equivFin (TblR 48) s).val at hh
  omega

theorem diagonalRole_ne_mul (r : RsbR) (i : Fin 64) : diagonalRole r ≠ diagonalMul i := by
  intro h
  have hh := congrArg Fin.val (work_injective h)
  have hr := (Fintype.equivFin RsbR r).isLt
  have hc := rsb_card
  change (Fintype.equivFin RsbR r).val = 100+i.val at hh
  omega

theorem diagonalRole_ne_queue (r : RsbR) : diagonalRole r ≠ diagonalQueue := by
  simp [diagonalRole,diagonalQueue,recovery_injective.eq_iff]
theorem diagonalMul_ne_queue (i : Fin 64) : diagonalMul i ≠ diagonalQueue := by
  simp [diagonalMul,diagonalQueue,recovery_injective.eq_iff]
theorem diagonalTable_ne_role (r : TblR 48) (s : RsbR) : diagonalTable r ≠ diagonalRole s := by
  intro h
  have hh := congrArg Fin.val (work_injective h)
  have hs := (Fintype.equivFin RsbR s).isLt
  have hc := rsb_card
  change 200+(Fintype.equivFin (TblR 48) r).val = (Fintype.equivFin RsbR s).val at hh
  omega

theorem diagonalRole_ne_work (r : RsbR) (i : Fin 392) (hi : 100 ≤ i.val) :
    diagonalRole r ≠ recovery (.work i) := by
  intro h
  have hh := congrArg (fun j : Fin 392 => j.val) (work_injective h)
  have hr := (Fintype.equivFin RsbR r).isLt
  have hc := rsb_card
  change (Fintype.equivFin RsbR r).val = i.val at hh
  omega

theorem diagonalMul_ne_work (i : Fin 64) (j : Fin 392) (hj : 200 ≤ j.val) :
    diagonalMul i ≠ recovery (.work j) := by
  intro h
  have hh := congrArg (fun k : Fin 392 => k.val) (work_injective h)
  change 100+i.val = j.val at hh
  omega

theorem diagonalTable_ne_work (r : TblR 48) (i : Fin 392) (hi : 300 ≤ i.val) :
    diagonalTable r ≠ recovery (.work i) := by
  intro h
  have hh := congrArg (fun j : Fin 392 => j.val) (work_injective h)
  have hr := (Fintype.equivFin (TblR 48) r).isLt
  have hc := table_card
  change 200+(Fintype.equivFin (TblR 48) r).val = i.val at hh
  omega

theorem diagonalTable_ne_mul (r : TblR 48) (i : Fin 64) : diagonalTable r ≠ diagonalMul i := by
  intro h
  have hh := congrArg (fun j : Fin 392 => j.val) (work_injective h)
  change 200+(Fintype.equivFin (TblR 48) r).val = 100+i.val at hh
  omega

theorem diagonalWork_ne_queue (i : Fin 392) : recovery (.work i) ≠ diagonalQueue := by
  simp [diagonalQueue,recovery_injective.eq_iff]

theorem diagonal_batch_regs :
    [diagonalClock,diagonalBytes,diagonalQueue,diagonalRole .src,diagonalRole .dst,diagonalSaved,diagonalTmp].Nodup := by
  have hc : [diagonalClock,diagonalBytes,diagonalSaved,diagonalTmp].Nodup := by
    simp [diagonalClock,diagonalBytes,diagonalSaved,diagonalTmp,recovery_injective.eq_iff]
  regs_ne hc
  have hsrcDst := diagonalRole_injective.ne (by decide : RsbR.src ≠ .dst)
  have hsrcClock := diagonalRole_ne_work .src 300 (by decide)
  have hdstClock := diagonalRole_ne_work .dst 300 (by decide)
  have hsrcBytes := diagonalRole_ne_work .src 301 (by decide)
  have hdstBytes := diagonalRole_ne_work .dst 301 (by decide)
  have hsrcSaved := diagonalRole_ne_work .src 302 (by decide)
  have hdstSaved := diagonalRole_ne_work .dst 302 (by decide)
  have hsrcTmp := diagonalRole_ne_work .src 303 (by decide)
  have hdstTmp := diagonalRole_ne_work .dst 303 (by decide)
  have hsrcQueue := diagonalRole_ne_queue .src
  have hdstQueue := diagonalRole_ne_queue .dst
  have hclockQueue := diagonalWork_ne_queue 300
  have hbytesQueue := diagonalWork_ne_queue 301
  have hsavedQueue := diagonalWork_ne_queue 302
  have htmpQueue := diagonalWork_ne_queue 303
  regs_nodup

theorem diagonal_free : RsbFree .src .df .dst := by simp [RsbFree]

theorem diagonal_tapes : 64 ≤ tapes := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective diagonalMul diagonalMul_injective

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
