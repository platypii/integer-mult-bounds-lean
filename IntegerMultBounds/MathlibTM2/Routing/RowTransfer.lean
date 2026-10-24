module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! Counted row extraction in forward order. The fixed code uses a supplied
width counter and restores its transfer buffer and counting scratch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type}

def rowTransfer (width src work buf tmp : Fin T) : Pr P T Q A U :=
  .seq (transfer width src buf tmp) (moveR buf work id)

/-- Remove exactly one counted row, preserving forward order and the unread suffix. -/
theorem rowTransfer_exec (body : P → Pr P T Q A U)
    (width src work buf tmp : Fin T) (hreg : [width, src, work, buf, tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (xs rest : List (Fin (A + 4)))
    (hsrc : S.R src = xs ++ rest) (hwidth : (S.R width).length = xs.length)
    (hbuf : S.R buf = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (rowTransfer width src work buf tmp) (mk v S) (6 * xs.length + 6)
        (mk v' { S with R := (Function.update (Function.update S.R src rest) work
          (xs ++ S.R work)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := transfer_exec (body := body)
    (show [width, src, buf, tmp].Nodup by simp_all) v S xs rest hsrc hwidth htmp
  let C : Stacks T A := { S with R := (Function.update (Function.update S.R src rest) buf
    (xs.reverse ++ S.R buf)) }
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body buf work ‹work ≠ buf›.symm id v₁ C
  have hlen : (C.R buf).length = xs.length := by simp [C, hbuf]
  have hfinal : ({ C with R := movedR C.R buf work id (C.R buf) } : Stacks T A) =
      { S with R := Function.update (Function.update S.R src rest) work (xs ++ S.R work) } := by
    congr 1
    funext r
    simp only [C, movedR, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  rw [hfinal, hlen] at he₂
  exact ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁ he₂).cast (by omega) rfl⟩

/-- Route one extracted row and archive its output in reverse for a final rewind. -/
def rowRoutingCall (width src work buf tmp output : Fin T) (call : Pr P T Q A U) : Pr P T Q A U :=
  .seq (rowTransfer width src work buf tmp) (.seq call (moveR work output id))

theorem rowRoutingCall_exec (body : P → Pr P T Q A U)
    (width src work buf tmp output : Fin T)
    (hreg : [width, src, work, buf, tmp, output].Nodup)
    (call : Pr P T Q A U) (price : ℝ)
    (v : HS T Q A U) (S : Stacks T A) (xs ys rest : List (Fin (A + 4)))
    (hsrc : S.R src = xs ++ rest) (hwidth : (S.R width).length = xs.length)
    (hwork : S.R work = []) (hbuf : S.R buf = []) (htmp : S.R tmp = [])
    (hsize : ys.length = xs.length)
    (hcall : ∀ u : HS T Q A U,
      let C : Stacks T A := { S with R := Function.update (Function.update S.R src rest) work xs }
      ∃ (u' : HS T Q A U) (steps : ℕ), u'.user = u.user ∧ (steps : ℝ) ≤ price ∧
        Exec body call (mk u C) steps (mk u' { C with R := Function.update C.R work ys })) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ price + (8 * xs.length + 8 : ℕ) ∧
      Exec body (rowRoutingCall width src work buf tmp output call) (mk v S) steps
        (mk v' { S with R := (Function.update (Function.update (Function.update S.R src rest)
          work []) output (ys.reverse ++ S.R output)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := rowTransfer_exec body width src work buf tmp
    (show [width, src, work, buf, tmp].Nodup by simp_all) v S xs rest hsrc hwidth hbuf htmp
  simp only [hwork, List.append_nil] at he₁
  let C : Stacks T A := { S with R := Function.update (Function.update S.R src rest) work xs }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := hcall v₁
  let D : Stacks T A := { C with R := Function.update C.R work ys }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body work output ‹work ≠ output› id v₂ D
  have hlen : (D.R work).length = xs.length := by simp [D, hsize]
  have hfinal : ({ D with R := movedR D.R work output id (D.R work) } : Stacks T A) =
      { S with R := (Function.update (Function.update (Function.update S.R src rest) work [])
        output (ys.reverse ++ S.R output)) } := by
    congr 1
    funext r
    simp only [D, C, movedR, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  rw [hfinal, hlen] at he₃
  refine ⟨v₃, 6 * xs.length + 6 + (m₂ + (2 * xs.length + 2)),
    hu₃.trans (hu₂.trans hu₁), ?_, Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  push_cast at hm₂ ⊢
  linarith only [hm₂]

open IntegerMultBounds.MathlibTM2.Node

/-- Consume one row-count symbol before invoking the reusable row wrapper. -/
def countedRowRoutingCall (count saved width src work buf tmp output : Fin T)
    (call : Pr P T Q A U) : Pr P T Q A U :=
  .seq (.act (popPush count saved)) (rowRoutingCall width src work buf tmp output call)

theorem countedRowRoutingCall_exec (body : P → Pr P T Q A U)
    (count saved width src work buf tmp output : Fin T)
    (hreg : [count, saved, width, src, work, buf, tmp, output].Nodup)
    (call : Pr P T Q A U) (price : ℝ) (c : Fin (A + 4)) (cs : List (Fin (A + 4)))
    (v : HS T Q A U) (S : Stacks T A) (xs ys rest : List (Fin (A + 4)))
    (hcount : S.R count = c :: cs)
    (hsrc : S.R src = xs ++ rest) (hwidth : (S.R width).length = xs.length)
    (hwork : S.R work = []) (hbuf : S.R buf = []) (htmp : S.R tmp = [])
    (hsize : ys.length = xs.length)
    (hcall : ∀ u : HS T Q A U,
      let B : Stacks T A := { S with R := (Function.update (Function.update S.R count cs)
        saved (c :: S.R saved)) }
      let C : Stacks T A := { B with R := Function.update (Function.update B.R src rest) work xs }
      ∃ (u' : HS T Q A U) (steps : ℕ), u'.user = u.user ∧ (steps : ℝ) ≤ price ∧
        Exec body call (mk u C) steps (mk u' { C with R := Function.update C.R work ys })) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ price + (8 * xs.length + 9 : ℕ) ∧
      Exec body (countedRowRoutingCall count saved width src work buf tmp output call)
        (mk v S) steps (mk v' { S with R := (Function.update (Function.update
          (Function.update (Function.update S.R count cs) saved (c :: S.R saved)) src rest)
          output (ys.reverse ++ S.R output)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  let B : Stacks T A := { S with R := (Function.update (Function.update S.R count cs)
    saved (c :: S.R saved)) }
  have hrun : (popPush count saved : Act T Q A U).run (mk v S) =
      mk { v with sym := some c } B := by
    simp [popPush, Action.run, update_rt, hcount, B, ‹count ≠ saved›.symm]
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := rowRoutingCall_exec body width src work buf tmp output
    (show [width, src, work, buf, tmp, output].Nodup by simp_all) call price
    { v with sym := some c } B xs ys rest
    (by simpa [B, ‹saved ≠ src›.symm, ‹count ≠ src›.symm] using hsrc)
    (by simpa [B, ‹saved ≠ width›.symm, ‹count ≠ width›.symm] using hwidth)
    (by simpa [B, ‹saved ≠ work›.symm, ‹count ≠ work›.symm] using hwork)
    (by simpa [B, ‹saved ≠ buf›.symm, ‹count ≠ buf›.symm] using hbuf)
    (by simpa [B, ‹saved ≠ tmp›.symm, ‹count ≠ tmp›.symm] using htmp) hsize hcall
  refine ⟨v₁, 1 + m₁, hu₁, ?_, ?_⟩
  · push_cast at hm₁ ⊢
    linarith only [hm₁]
  · have he := Exec.seq (hrun ▸ Exec.act (body := body) (popPush count saved) (mk v S)) he₁
    apply he.cast rfl
    congr 1
    congr 1
    funext r
    simp only [B, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all

/-- Restore the row counter and put the routed stream before the untouched suffix. -/
def rowRoutingRewind (count saved src output : Fin T) : Pr P T Q A U :=
  .seq (moveR saved count id) (moveR output src id)

theorem rowRoutingRewind_exec (body : P → Pr P T Q A U)
    (count saved src output : Fin T) (hreg : [count, saved, src, output].Nodup)
    (cs ys : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hcount : S.R count = []) (hsaved : S.R saved = cs.reverse)
    (houtput : S.R output = ys.reverse) :
    ∃ v', v'.user = v.user ∧
      Exec body (rowRoutingRewind count saved src output) (mk v S)
        (2 * cs.length + 2 * ys.length + 4)
        (mk v' { S with R := (Function.update (Function.update
          (Function.update (Function.update S.R saved []) count cs) output []) src
          (ys ++ S.R src)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := moveR_exec body saved count ‹count ≠ saved›.symm id v S
  let C : Stacks T A := { S with R := movedR S.R saved count id (S.R saved) }
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body output src ‹src ≠ output›.symm id v₁ C
  have hc : (C.R output).length = ys.length := by
    simp [C, movedR, ‹saved ≠ output›.symm, ‹count ≠ output›.symm, houtput]
  have hs : (S.R saved).length = cs.length := by simp [hsaved]
  have hf : ({ C with R := movedR C.R output src id (C.R output) } : Stacks T A) =
      { S with R := (Function.update (Function.update
        (Function.update (Function.update S.R saved []) count cs) output []) src
        (ys ++ S.R src)) } := by
    congr 1
    funext r
    simp only [C, movedR, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  rw [hf, hc] at he₂
  rw [hs] at he₁
  exact ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁ he₂).cast (by omega) rfl⟩

end IntegerMultBounds.MathlibTM2.Routing
