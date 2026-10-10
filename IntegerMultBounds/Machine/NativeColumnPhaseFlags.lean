import IntegerMultBounds.Machine.UnitPhaseFlagsLifecycle
import IntegerMultBounds.Machine.RecursiveChildQuotientsConstant

/-! Two genuine reads of the original little-endian column-count header
construct the Gaussian-unit phase 27 times that count modulo four. The
header is retained and its head restored; no direction or phase is supplied
to the transition table. -/
namespace IntegerMultBounds.Machine.NativeColumnPhaseFlags
open UnitPhaseNumerator (flags low high)
open MarkedWordCleanup (one)

def phase (b c : Bool) : Fin 4 :=
  if b then (if c then 1 else 3) else (if c then 2 else 0)

def program : Program 3 4 2 where
  tapes_pos := by decide
  start := 0
  transition := fun st sy =>
    if st=0 then some (if sy 0=bitSymbol true then 2 else 1,
      fun i => (sy i,if i=0 then Move.right else Move.stay))
    else if st=3 then none
    else some (3,fun i =>
      if i=0 then (sy i,Move.left)
      else (bitSymbol (if i=1 then decide (st=2)
        else Bool.xor (decide (st=2)) (decide (sy 0=bitSymbol true))),Move.stay))

def input (header : ℤ → Fin 6) :=
  (one header 1).append (SharedBank.empty 2 2)
def output (header : ℤ → Fin 6) (b c : Bool) :=
  (one header 1).append (flags (phase b c))

theorem phase_low (b c : Bool) : low (phase b c)=b := by
  cases b <;> cases c <;> decide

theorem phase_high (b c : Bool) : high (phase b c)=Bool.xor b c := by
  cases b <;> cases c <;> decide

/-- The machine reads the two actual cells; blank means a missing zero bit. -/
theorem runs (header : ℤ → Fin 6) (b c : Bool)
    (hb : decide (header 1=bitSymbol true)=b)
    (hc : decide (header 2=bitSymbol true)=c) :
    HoareTime program (fun v => v=input header)
      (fun v => v=output header b c) 2 := by
  rintro v rfl
  refine ⟨2,⟨3,(output header b c).head,(output header b c).tape⟩,le_rfl,?_,?_,rfl⟩
  · have hreadb : (header 1=bitSymbol true) ↔ b=true := by
      simpa only [hb] using (show (header 1=bitSymbol true) ↔ decide (header 1=bitSymbol true)=true from by simp)
    have hreadc : (header 2=bitSymbol true) ↔ c=true := by
      simpa only [hc] using (show (header 2=bitSymbol true) ↔ decide (header 2=bitSymbol true)=true from by simp)
    cases b <;> cases c
    all_goals simp only [Bool.false_eq_true,iff_false,iff_true] at hreadb hreadc
    all_goals simp [run,step,program,Tapes.start,input,output,
      Tapes.append,Fin.addCases,one,SharedBank.empty,flags,phase,low,high,
      putWord,Move.offset,hreadb,hreadc]
    all_goals constructor
    all_goals funext i; fin_cases i <;> simp
    all_goals funext z; try simp [Function.update_apply]
    all_goals split_ifs <;> simp_all

  · simp [step,program]

/-- Only the low two bits can affect this fixed Gaussian unit. -/
theorem phase_value (b c : Bool) (rest : List Bool) :
    (phase b c).val=(27*Counter.value (b::c::rest))%4 := by
  cases b <;> cases c <;> simp [phase,Counter.value] <;> omega

def ofWord (bs : List Bool) := phase (bs.headD false) (bs.tail.headD false)

theorem ofWord_value (bs : List Bool) :
    (ofWord bs).val=(27*Counter.value bs)%4 := by
  cases bs with
  | nil => rfl
  | cons b bs =>
    cases bs with
    | nil => cases b <;> decide
    | cons c rest => exact phase_value b c rest

private theorem encoded_low (bs : List Bool) :
    decide (RadixZeroFill.encodedBinary (q:=2) bs 1=bitSymbol true)=bs.headD false := by
  cases bs with
  | nil => decide
  | cons b bs =>
    cases b <;> simp [RadixZeroFill.encodedBinary,RadixToBinary.binaryEncoding,
      CountedCopyReuse.binary,putBits,bitSymbol,Fin.ext_iff]

private theorem encoded_high (bs : List Bool) :
    decide (RadixZeroFill.encodedBinary (q:=2) bs 2=bitSymbol true)=bs.tail.headD false := by
  cases bs with
  | nil => decide
  | cons b bs =>
    cases bs with
    | nil => cases b <;> decide
    | cons c rest =>
      cases c <;> simp [RadixZeroFill.encodedBinary,RadixToBinary.binaryEncoding,
        CountedCopyReuse.binary,putBits,bitSymbol,Fin.ext_iff]

theorem runs_word (bs : List Bool) :
    HoareTime program (fun v => v=input (RadixZeroFill.encodedBinary bs))
      (fun v => v=(one (RadixZeroFill.encodedBinary bs) 1).append (flags (ofWord bs))) 2 :=
  runs _ _ _ (encoded_low bs) (encoded_high bs)

/-- The original runtime columns word is the sole source of the phase. -/
theorem runs_columns (columns : ℕ) :
    HoareTime program
      (fun v => v=input (RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits columns)))
      (fun v => v=(one (RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits columns)) 1).append
        (flags ⟨(27*columns)%4,Nat.mod_lt _ (by decide)⟩)) 2 := by
  have h : ofWord (RecursiveChildQuotientsConstant.bits columns)=
      ⟨(27*columns)%4,Nat.mod_lt _ (by decide)⟩ := by
    apply Fin.ext
    rw [ofWord_value,RecursiveChildQuotientsConstant.bits_value]
  simpa only [h] using runs_word (RecursiveChildQuotientsConstant.bits columns)

end IntegerMultBounds.Machine.NativeColumnPhaseFlags
