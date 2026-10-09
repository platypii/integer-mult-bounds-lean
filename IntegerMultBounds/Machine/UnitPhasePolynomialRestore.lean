import IntegerMultBounds.Machine.UnitPhasePolynomialRecord

/-! The full polynomial body restores its original prepared caller bank.
Only source/output stream heads and cells advance; raw address and live
counter are preserved. This is the reusable boundary for the outer loop. -/
namespace IntegerMultBounds.Machine.UnitPhasePolynomialRestore
noncomputable section
open SharedPlacementAlphabet (setTape)
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open DelimitedRadixRecord (Context)
open UnitPhasePolynomialRecord (prepared finished)
variable {s : Shape}

def streams (v w : Tapes 60 2) := setTape (setTape v 56 (w.tape 56) (w.head 56)) 58 (w.tape 58) (w.head 58)

theorem stream_frame (v : Tapes 60 2) (ctx : ℕ → Context 2) (p : Fin 4)
    (hf : UnitPhasePolynomialLoop.flagsAt v p) (hc : UnitPhasePolynomialLoop.coreBlank v) (R : ℕ) :
    UnitPhasePolynomialLoop.state v ctx p R=streams v (UnitPhasePolynomialLoop.state v ctx p R) := by
  apply Placement.Tapes.ext'
  all_goals intro i
  all_goals by_cases h56 : i=56
  all_goals by_cases h58 : i=58
  all_goals simp [streams,setTape,h56,h58]
  all_goals have h := UnitPhasePolynomialFrame.frame v ctx p hf hc i ⟨h56,h58⟩ R
  all_goals first | exact h.1 | exact h.2

theorem reset_streams (v w : Tapes 60 2) :
    UnitPhaseControlReset.output (streams v w)=streams (UnitPhaseControlReset.output v) w := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem reset_prepared (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (addr : List Bool) (z : Tapes 4 2) :
    UnitPhaseControlReset.output (prepared order v rows axis m ws addr z)=
      (SparsePhaseFlagsCaller.input order v rows axis addr (SharedBank.empty 6 2)).append z := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def nextTail (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (addr : List Bool) (z : Tapes 4 2) (ctx : ℕ → Context 2) (R : ℕ) :=
  let w := finished order v rows axis m ws addr z ctx R
  setTape (setTape z 0 (w.tape 56) (w.head 56)) 2 (w.tape 58) (w.head 58)

theorem restored (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (addr : List Bool) (z : Tapes 4 2) (ctx : ℕ → Context 2) (R : ℕ) :
    UnitPhasePolynomialRecord.output order v rows axis m ws addr z ctx R=
      UnitPhasePolynomialRecord.initial order v rows axis addr (nextTail order v rows axis m ws addr z ctx R) R := by
  have h := stream_frame (prepared order v rows axis m ws addr z) ctx (UnitPhaseRecordKernel.exponent v axis m ws addr)
    (UnitPhasePolynomialRecord.prepared_flags order v rows axis m ws addr z)
    (UnitPhasePolynomialRecord.prepared_core order v rows axis m ws addr z) R
  change finished order v rows axis m ws addr z ctx R=streams (prepared order v rows axis m ws addr z)
    (finished order v rows axis m ws addr z ctx R) at h
  unfold UnitPhasePolynomialRecord.output
  rw [h,reset_streams,reset_prepared]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.UnitPhasePolynomialRestore
