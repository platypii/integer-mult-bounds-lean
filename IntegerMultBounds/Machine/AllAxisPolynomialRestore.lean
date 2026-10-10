import IntegerMultBounds.Machine.AllAxisPolynomialRecord
import IntegerMultBounds.Machine.AllAxisPhaseFlagsNormalize

/-! The full polynomial body restores its original prepared caller bank.
Only source/output stream heads and cells advance; raw address and live
counter are preserved. This is the reusable boundary for the outer loop. -/
namespace IntegerMultBounds.Machine.AllAxisPolynomialRestore
noncomputable section
open SharedPlacementAlphabet (setTape)
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open DelimitedRadixRecord (Context)
open AllAxisPolynomialRecord (prepared finished)
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

theorem reset_prepared (order : Order) (v : Stage s) (rows : ℕ) (m : ℕ)
    (ws : List (ZMod 4)) (addr : List Bool) (z : Tapes 4 2) :
    UnitPhaseControlReset.output (prepared order v rows m ws addr z)=
      (AllAxisPhaseFlagsCaller.input order v rows addr (SharedBank.empty 6 2)).append z := by
  unfold prepared
  rw [AllAxisPhaseFlagsNormalize.output_eq]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def nextTail (order : Order) (v : Stage s) (rows : ℕ) (m : ℕ)
    (ws : List (ZMod 4)) (addr : List Bool) (z : Tapes 4 2) (ctx : ℕ → Context 2) (R : ℕ) :=
  let w := finished order v rows m ws addr z ctx R
  setTape (setTape z 0 (w.tape 56) (w.head 56)) 2 (w.tape 58) (w.head 58)

theorem restored (order : Order) (v : Stage s) (rows : ℕ) (m : ℕ)
    (ws : List (ZMod 4)) (addr : List Bool) (z : Tapes 4 2) (ctx : ℕ → Context 2) (R : ℕ) :
    AllAxisPolynomialRecord.output order v rows m ws addr z ctx R=
      AllAxisPolynomialRecord.initial order v rows addr (nextTail order v rows m ws addr z ctx R) R := by
  have h := stream_frame (prepared order v rows m ws addr z) ctx (AllAxisPhaseFlagsCaller.phase v m ws addr)
    (AllAxisPolynomialRecord.prepared_flags order v rows m ws addr z)
    (AllAxisPolynomialRecord.prepared_core order v rows m ws addr z) R
  change finished order v rows m ws addr z ctx R=streams (prepared order v rows m ws addr z)
    (finished order v rows m ws addr z ctx R) at h
  unfold AllAxisPolynomialRecord.output
  rw [h,reset_streams,reset_prepared]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.AllAxisPolynomialRestore
