module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpLineSetupFrame
public import IntegerMultBounds.MathlibTM2.Mult.ChirpReverse

/-! # Stage and collect one line without regenerating retained setup

Archive consumed input symbols in reverse order; restoring that archive once
returns the original batch. Collect output lines the same way, then reverse once.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 640 Q A U}

def groupInput : Fin 640 := 540
def inputArchive : Fin 640 := 541
def outputArchive : Fin 640 := 542
def lineSymbols : Fin 640 := 543
def lineCount : Fin 640 := 544
def savedLineCount : Fin 640 := 545
def groupBuf : Fin 640 := 546
def groupTmp : Fin 640 := 547
def groupOutput : Fin 640 := 548

def stageLine : Pr P 640 Q A U := reverseNext lineSymbols groupInput (raw .raw) inputArchive groupBuf groupTmp

def stageLineR (xs rest : List (Fin (A + 4))) (R : Regs 640 A) : Regs 640 A :=
  Function.update (Function.update (Function.update R groupInput rest)
    inputArchive (xs.reverse ++ R inputArchive)) (raw .raw) xs

/-- Consume one line from the batch, retain its original symbols and supply the raw-line tape. -/
theorem stageLine_exec (v : HS 640 Q A U) (S : Stacks 640 A) (xs rest : List (Fin (A + 4)))
    (hinput : S.R groupInput = xs ++ rest) (hcount : (S.R lineSymbols).length = xs.length)
    (hraw : S.R (raw .raw) = []) (hbuf : S.R groupBuf = []) (htmp : S.R groupTmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body stageLine (mk v S) (14 * xs.length + 14) (mk v' { S with R := stageLineR xs rest S.R }) := by
  obtain ⟨v', hu, he⟩ := reverseNext_exec (body := body)
    (show [lineSymbols, groupInput, raw .raw, inputArchive, groupBuf, groupTmp].Nodup by decide +kernel)
    v S xs rest hinput hcount hbuf htmp
  exact ⟨v', hu, by simpa only [stageLine, stageLineR, hraw, List.append_nil] using he⟩

def collectLine : Pr P 640 Q A U :=
  .seq (uclear (raw .raw)) (moveR (output.nr .out) outputArchive id)

def collectLineR (ys : List (Fin (A + 4))) (R : Regs 640 A) : Regs 640 A :=
  Function.update (Function.update (Function.update R (raw .raw) []) (output.nr .out) [])
    outputArchive (ys.reverse ++ R outputArchive)

/-- Discard the staged copy and collect its output, returning both line ports to empty. -/
theorem collectLine_exec (v : HS 640 Q A U) (S : Stacks 640 A) (xs ys : List (Fin (A + 4)))
    (hraw : S.R (raw .raw) = xs) (hout : S.R (output.nr .out) = ys) :
    ∃ v', v'.user = v.user ∧
      Exec body collectLine (mk v S) (2 * xs.length + 2 * ys.length + 4)
        (mk v' { S with R := collectLineR ys S.R }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := uclear_exec body (raw .raw) v S
  rw [hraw] at he₁
  let S₁ : Stacks 640 A := { S with R := Function.update S.R (raw .raw) [] }
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body (output.nr .out) outputArchive (by decide +kernel) id v₁ S₁
  have hword : S₁.R (output.nr .out) = ys := by
    simpa only [S₁, Function.update_of_ne (show output.nr .out ≠ raw .raw by decide +kernel)] using hout
  rw [hword] at he₂
  refine ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁ he₂).cast (by omega) ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  simp only [S₁, collectLineR, movedR, List.map_id,
    Function.update_of_ne (show outputArchive ≠ raw .raw by decide +kernel)]

/-- Only the batch cursor, input archive and raw-line input are changed by staging. -/
theorem stageLineR_off (xs rest : List (Fin (A + 4))) (R : Regs 640 A) (k : Fin 640)
    (hi : k ≠ groupInput) (ha : k ≠ inputArchive) (hr : k ≠ raw .raw) : stageLineR xs rest R k = R k := by
  simp only [stageLineR, Function.update_of_ne hr, Function.update_of_ne ha, Function.update_of_ne hi]

/-- Only the raw-line input, output tape and output archive are changed by collection. -/
theorem collectLineR_off (ys : List (Fin (A + 4))) (R : Regs 640 A) (k : Fin 640)
    (hr : k ≠ raw .raw) (ho : k ≠ output.nr .out) (ha : k ≠ outputArchive) : collectLineR ys R k = R k := by
  simp only [collectLineR, Function.update_of_ne ha, Function.update_of_ne ho, Function.update_of_ne hr]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
