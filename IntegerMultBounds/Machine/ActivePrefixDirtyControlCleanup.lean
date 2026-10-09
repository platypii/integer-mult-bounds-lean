import IntegerMultBounds.Machine.ActivePrefixDirtyControlRun
import IntegerMultBounds.Machine.ActivePrefixOffsetStreamsCleanup

/-! Erase all generated metadata and source streams, including the real clock
used by compact-U parity extraction. Only the original six descriptors and the
rewound offset output remain. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlCleanup
noncomputable section
open ActivePrefixDirtyControlData ActivePrefixDirtyControlBank
open ActivePrefixDirtyControlHeaders (bank)
open SharedPlacementAlphabet (setTape)
open BinaryVaryingOffsetGatherPlaced (Kind sourceWidth outputWidth)
variable {a : ℕ} {k : Kind}

def focus : Fin 4 → Fin 15 := ![10,11,13,14]
def streams (s : Shape k) (hs : Fin 6 → List Bool) :=
  ActivePrefixOffsetStreamsCleanup.result (gathered (a := a) s hs) focus (offsetWord s)
def clock (s : Shape k) (hs : Fin 6 → List Bool) :=
  WordBankCleanup.write (streams (a := a) s hs) 12 (fun _ => blank)
def result (s : Shape k) (hs : Fin 6 → List Bool) :=
  setTape (base (a := a) hs) 14 (ActivePrefixOffsetStreamsCleanup.word (offsetWord s)) 0

def core := seq (seq (ActivePrefixOffsetStreamsCleanup.program (a := a) focus (by decide))
  (WordBankCleanup.clearProgram 12 (by decide : 1≤15) a))
  (CompactGadgetReservationHeadersCarvedPlacedCleanup.program derivedFocus)
def program := extend (core (a := a)) 24

def cost (s : Shape k) := (tempWord s).length+(controlWord s).length+
  2*(sourceWord s).length+(offsetWord s).length+12+
  (2*(clockWord s).length+3)+CompactGadgetReservationHeadersCarvedPlacedCleanup.cost (derivedWords s)+2

theorem streams_runs (s : Shape k) (hs : Fin 6 → List Bool) :
    HoareTime (ActivePrefixOffsetStreamsCleanup.program (a := a) focus (by decide))
      (fun v => v=gathered s hs) (fun v => v=streams s hs)
      ((tempWord s).length+(controlWord s).length+2*(sourceWord s).length+(offsetWord s).length+12) := by
  apply ActivePrefixOffsetStreamsCleanup.runs _ _ (by decide) _
  · rw [gathered_eq]; rfl
  · rw [gathered_eq]; rfl
  · rw [gathered_eq]; rfl
  · rw [gathered_eq]; rfl
  · rw [gathered_eq]
    change 0+(controlWord s).length*sourceWidth k s.q s.b=((tempWord s).length : ℤ)
    simp [tempWord,tempWidth,mul_assoc]
  · rw [gathered_eq]; rfl
  · rw [gathered_eq]; simp [emitted,gatherFocus,focus,setTape]
  · rw [gathered_eq]
    change 0+(controlWord s).length*outputWidth k s.q s.b=((offsetWord s).length : ℤ)
    simp [outputRowWidth,mul_assoc]

theorem clock_runs (s : Shape k) (hs : Fin 6 → List Bool) :
    HoareTime (WordBankCleanup.clearProgram 12 (by decide : 1≤15) a)
      (fun v => v=streams s hs) (fun v => v=clock s hs) (2*(clockWord s).length+3) := by
  have h := WordBankCleanup.clear_hoare (streams (a := a) s hs) 12 (by decide)
    ((clockWord s).map bitSymbol) (ReturnOrigin.bits_nonblank _) (by
      dsimp only [streams]
      rw [gathered_eq]
      rfl)
  simpa only [List.length_map,clock] using h

theorem final_eq (s : Shape k) (hs : Fin 6 → List Bool) :
    CompactGadgetReservationHeadersCarvedPlacedCleanup.cleared (clock (a := a) s hs) derivedFocus=result s hs := by
  unfold clock streams
  rw [gathered_eq]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem headers_runs (s : Shape k) (hs : Fin 6 → List Bool) :
    HoareTime (CompactGadgetReservationHeadersCarvedPlacedCleanup.program (a := a) derivedFocus)
      (fun v => v=clock s hs) (fun v => v=result s hs)
      (CompactGadgetReservationHeadersCarvedPlacedCleanup.cost (derivedWords s)) := by
  have h := CompactGadgetReservationHeadersCarvedPlacedCleanup.cleans (clock (a := a) s hs)
    derivedFocus (by decide) (derivedWords s)
    (by intro i; unfold clock streams; rw [gathered_eq]; fin_cases i <;> rfl)
    (by intro i; unfold clock streams; rw [gathered_eq]; fin_cases i <;> rfl)
  simpa only [final_eq] using h

theorem core_runs (s : Shape k) (hs : Fin 6 → List Bool) :
    HoareTime (core (a := a)) (fun v => v=gathered s hs) (fun v => v=result s hs) (cost s) := by
  exact (((streams_runs s hs).seq (clock_runs s hs)).seq (headers_runs s hs)).consequence
    (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

theorem runs (s : Shape k) (hs : Fin 6 → List Bool) :
    HoareTime (program (a := a)) (fun v => v=bank (gathered s hs)) (fun v => v=bank (result s hs)) (cost s) :=
  hoare_extend_eq (core_runs s hs) (SharedBank.empty 24 a)

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlCleanup
