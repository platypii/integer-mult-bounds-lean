import IntegerMultBounds.Machine.ActivePrefixOffsetRepeatRun
import IntegerMultBounds.Machine.PackedOffsetPayloadAlphabet

/-! Repetition in the caller alphabet, retaining the complete base word and
original row descriptor and restoring the private countdown tape blank. -/
namespace IntegerMultBounds.Machine.ActivePrefixOffsetRepeatAlphabet
noncomputable section
open StreamedFiberTranslationAlphabet (encoding mapTape)
open SharedPlacementAlphabet (setTape)
open BinaryAddressOffsetRepeatData (copies)
variable {a : ℕ}

def word (xs : List Bool) : ℤ → Fin (a+4) := putWord (fun _ => blank) 0 (xs.map bitSymbol)
def bank (xs rs : List Bool) (out : ℤ → Fin (a+4)) : Tapes 4 a :=
  ⟨![0,0,0,1],![word xs,out,fun _ => blank,RadixZeroFill.encodedBinary rs]⟩
def program (a : ℕ) := Alphabet.program (encoding (a := a)) ActivePrefixOffsetRepeatRun.program

theorem map_binary (rs : List Bool) :
    mapTape (a := a) (CountedLoopReuseAlphabet.binary (a := 0) rs)=RadixZeroFill.encodedBinary rs := by
  rw [← CountedLoopReuseAlphabet.encoding_binary]
  funext z
  generalize hx : CountedCopyReuse.binary rs z=x
  fin_cases x <;> rfl

theorem mapped_input (xs rs : List Bool) :
    Alphabet.mapTapes (encoding (a := a)) (ActivePrefixOffsetRepeatRun.input xs rs)=bank xs rs (fun _ => blank) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact map_binary rs | exact PackedOffsetPayloadAlphabet.map_bits (fun _ => blank) 0 _

theorem mapped_output (xs rs : List Bool) (rows : ℕ) :
    Alphabet.mapTapes (encoding (a := a)) (ActivePrefixOffsetRepeatRun.output xs rs rows)=
      bank xs rs (word (copies xs rows)) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact map_binary rs | exact PackedOffsetPayloadAlphabet.map_bits (fun _ => blank) 0 _

theorem output_eq (xs rs : List Bool) (out : ℤ → Fin (a+4)) :
    bank xs rs out=setTape (bank xs rs (fun _ => blank)) 1 out 0 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem repeats (xs rs : List Bool) (rows : ℕ) (hv : Counter.value rs=rows)
    (hc : GrowingCounterData.Canonical rs) :
    HoareTime (program a) (fun v => v=bank xs rs (fun _ => blank))
      (fun v => v=bank xs rs (word (copies xs rows))) (54*(rows*xs.length+1)) := by
  have h := Alphabet.map_hoare (encoding (a := a)) (ActivePrefixOffsetRepeatRun.runs_linear xs rs rows hv hc)
  refine h.consequence ?_ ?_ le_rfl
  · rintro v rfl
    exact ⟨_,rfl,(mapped_input xs rs).symm⟩
  · rintro v ⟨small,rfl,rfl⟩
    exact mapped_output xs rs rows

end
end IntegerMultBounds.Machine.ActivePrefixOffsetRepeatAlphabet
