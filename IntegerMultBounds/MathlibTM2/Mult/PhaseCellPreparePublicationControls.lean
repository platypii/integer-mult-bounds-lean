module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConditionalCorePublicationControls

/-! Prepare both generated publication schedules once from retained dimensions.
Only the two control destinations change; existing suffixes remain borrowed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def preparePublicationControls
    (remainder count coreWidth wordWidth product fullControl clippedControl saved tmp : Fin T) : Pr P T Q A U :=
  .seq (copyR count fullControl tmp (fun _ => blank))
    (remainderPublicationControls remainder count coreWidth wordWidth product clippedControl saved tmp)

def preparePublicationControlsCost (s width w : ℕ) :=
  4*(s/width)+4+remainderPublicationControlsCost s width w

theorem preparePublicationControlsCost_le (s width w : ℕ) (hw : 1 ≤ w) :
    preparePublicationControlsCost s width w ≤ 32*s*w+17 := by
  have hq := Nat.div_le_self s width
  have hvol := Nat.div_mul_le_self s width
  have hwords := Nat.mul_le_mul_right w hvol
  have hsw : s ≤ s*w := by simpa using Nat.mul_le_mul_left s hw
  unfold preparePublicationControlsCost remainderPublicationControlsCost
  split_ifs <;> nlinarith only [hq,hvol,hwords,hsw]

theorem preparePublicationControls_exec
    (remainder count coreWidth wordWidth product fullControl clippedControl saved tmp : Fin T)
    (hreg : [remainder,count,coreWidth,wordWidth,product,fullControl,clippedControl,saved,tmp].Nodup)
    (s width w : ℕ) (hw : 0 < width) (v : HS T Q A U) (S : Stacks T A)
    (hrem : (S.R remainder).length = s%width)
    (hcount : (S.R count).length = s/width) (hcore : (S.R coreWidth).length = width)
    (hword : (S.R wordWidth).length = w)
    (hproduct : S.R product = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ preparePublicationControlsCost s width w ∧
      Exec body (preparePublicationControls remainder count coreWidth wordWidth product fullControl clippedControl saved tmp)
        (mk v S) n (mk v' {S with R := (Function.update
          (Function.update S.R fullControl
            (gatherControls A ((corePublicationWindows s width width hw).gaps w)++S.R fullControl))
          clippedControl (gatherControls A ((corePublicationWindows s width (s%width) hw).gaps w)++S.R clippedControl))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := fullCorePublicationControls_exec (body := body)
    count fullControl tmp (by regs_nodup) s width w hw v S hcount htmp
  let M : Stacks T A := {S with R := (Function.update S.R fullControl
    (gatherControls A ((corePublicationWindows s width width hw).gaps w)++S.R fullControl))}
  have hstable (i : Fin T) (hi : i ≠ fullControl) : M.R i = S.R i := by simp [M,hi]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := remainderPublicationControls_exec (body := body)
    remainder count coreWidth wordWidth product clippedControl saved tmp (by regs_nodup) s width w hw v₁ M
    (by rw [hstable _ ‹remainder ≠ fullControl›]; exact hrem)
    (by rw [hstable _ ‹count ≠ fullControl›]; exact hcount)
    (by rw [hstable _ ‹coreWidth ≠ fullControl›]; exact hcore)
    (by rw [hstable _ ‹wordWidth ≠ fullControl›]; exact hword)
    (by rw [hstable _ ‹product ≠ fullControl›]; exact hproduct)
    (by rw [hstable _ ‹fullControl ≠ saved›.symm]; exact hsaved)
    (by rw [hstable _ ‹fullControl ≠ tmp›.symm]; exact htmp)
  refine ⟨v₂,(4*(s/width)+4)+n₂,hu₂.trans hu₁,Nat.add_le_add_left hn₂ _,?_⟩
  have he := Exec.seq he₁ he₂
  simpa [preparePublicationControls,M,‹fullControl ≠ clippedControl›.symm] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
