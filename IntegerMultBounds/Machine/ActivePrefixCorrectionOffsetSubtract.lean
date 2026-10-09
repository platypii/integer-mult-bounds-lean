import IntegerMultBounds.Machine.ActivePrefixCorrectionOffsetData
import IntegerMultBounds.Machine.PackedOffsetPayloadAlphabet
import IntegerMultBounds.Machine.CompactGadgetReservationPlacement

/-! Caller-alphabet rowwise subtraction consumes both complete operand tables
and returns blank scratch, preserving runtime width/count descriptors. -/
namespace IntegerMultBounds.Machine.ActivePrefixCorrectionOffsetSubtract
noncomputable section
open StreamedFiberTranslationAlphabet (encoding)
open SharedPlacementAlphabet (setTape)
open BinaryCorrectionOffsetLoop (left right result Uniform)
variable {a t : ℕ}

def word (xs : List Bool) : ℤ → Fin (a+4) := putWord (fun _ => blank) 0 (xs.map bitSymbol)
def bank (xs ys zs : List Bool) (ws ns : List Bool) : Tapes 9 a :=
  ⟨![0,0,0,0,0,0,1,0,1],![word xs,word ys,word zs,(fun _ => blank),(fun _ => blank),
    (fun _ => blank),RadixZeroFill.encodedBinary ws,(fun _ => blank),RadixZeroFill.encodedBinary ns]⟩
def nativeProgram (a : ℕ) := Alphabet.program (encoding (a := a)) BinaryCorrectionOffsetSubtract.program

theorem mapped (xs ys zs ws ns : List Bool) :
    Alphabet.mapTapes (encoding (a := a)) (BinaryCorrectionOffsetSubtract.raw
      (BinaryCorrectionOffsetRow.word xs) (BinaryCorrectionOffsetRow.word ys)
      (BinaryCorrectionOffsetRow.word zs) 0 0 0 ws ns)=bank xs ys zs ws ns := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact PackedOffsetPayloadAlphabet.map_bits (fun _ => blank) 0 _

theorem native_runs (rows : List (List Bool × List Bool)) (W : ℕ) (hu : Uniform W rows)
    (ws ns : List Bool) (hw : Counter.value ws=W) (hn : Counter.value ns=rows.length)
    (hN : 0<rows.length) (cw : GrowingCounterData.Canonical ws) (cn : GrowingCounterData.Canonical ns) :
    HoareTime (nativeProgram a) (fun v => v=bank (left rows) (right rows) [] ws ns)
      (fun v => v=bank [] [] (result rows) ws ns) (160*(rows.length*(W+1))) := by
  have h := Alphabet.map_hoare (encoding (a := a)) (BinaryCorrectionOffsetSubtract.runs rows W hu ws ns hw hn)
  refine h.consequence ?_ ?_ (BinaryCorrectionOffsetSubtract.cost_linear W rows.length ws ns hN hw hn cw cn)
  · rintro v rfl
    exact ⟨_,rfl,(mapped (left rows) (right rows) [] ws ns).symm⟩
  · rintro v ⟨small,rfl,rfl⟩
    exact mapped [] [] (result rows) ws ns

def ports : Fin 5 → Fin 9 := ![0,1,2,6,8]
theorem ports_injective : Function.Injective ports := by decide

def sources (xs ys ws ns : List Bool) : Tapes 5 a := SharedBank.payload (bank xs ys [] ws ns) ports

def output (caller : Tapes t a) (focus : Fin 5 → Fin t) (xs : List Bool) :=
  setTape (setTape (setTape caller (focus 0) (fun _ => blank) 0) (focus 1) (fun _ => blank) 0)
    (focus 2) (word xs) 0

def program (focus : Fin 5 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (nativeProgram a) (CleanSubbank.placement ports focus hf)

theorem clean (xs ys zs ws ns : List Bool) :
    SharedBank.strip (bank (a := a) xs ys zs ws ns) ports=SharedBank.empty 9 a := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [bank,ports,Fin.exists_fin_succ]

theorem output_eq (xs ys zs ws ns : List Bool) :
    bank (a := a) [] [] zs ws ns=output (bank xs ys [] ws ns) ports zs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem runs (caller : Tapes t a) (focus : Fin 5 → Fin t) (hf : Function.Injective focus)
    (rows : List (List Bool × List Bool)) (W : ℕ) (hu : Uniform W rows)
    (ws ns : List Bool) (hw : Counter.value ws=W) (hn : Counter.value ns=rows.length)
    (hN : 0<rows.length) (cw : GrowingCounterData.Canonical ws) (cn : GrowingCounterData.Canonical ns)
    (hsrc : SharedBank.payload caller focus=sources (left rows) (right rows) ws ns) :
    HoareTime (program focus hf) (fun v => v=CleanSubbank.bank (s := 9) caller)
      (fun v => v=CleanSubbank.bank (s := 9) (output caller focus (result rows)))
      (160*(rows.length*(W+1))) := by
  refine CleanSubbank.realizes _ ports focus ports_injective hf caller (output caller focus (result rows))
    _ _ _ hsrc.symm ?_ (clean _ _ _ _ _) (clean _ _ _ _ _) ?_
    (native_runs rows W hu ws ns hw hn hN cw cn)
  · rw [output_eq (left rows) (right rows)]
    simp only [output,CompactGadgetReservationPlacement.payload_set _ _ ports_injective,
      CompactGadgetReservationPlacement.payload_set _ _ hf,hsrc,sources]
  · simp only [output,CompactGadgetReservationPlacement.strip_set]

end
end IntegerMultBounds.Machine.ActivePrefixCorrectionOffsetSubtract
