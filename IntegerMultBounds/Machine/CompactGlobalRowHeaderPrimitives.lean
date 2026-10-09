import IntegerMultBounds.Machine.CompactGadgetReservationHeadersPowerRound
import IntegerMultBounds.Machine.FixedBasePowerUntilRange

/-! Fixed-base logarithm and power constructors on retained runtime binary
headers. The least-power witness is actually erased after extracting its
exponent. All routines share the existing fifteen private tapes. -/
namespace IntegerMultBounds.Machine.CompactGlobalRowHeaderPrimitives
noncomputable section
open CompactGadgetReservationHeadersCore
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {t a : ℕ}

def powerCore (B : ℕ) := extend (FixedBasePowerDescriptor.program (q := a) B) 7
def powerProgram (B : ℕ) (focus : Fin 2 → Fin t) (hf : Function.Injective focus) :=
  placed (powerCore (a := a) B) CompactGadgetReservationHeadersPowerRound.powerPorts focus hf

theorem power (B : ℕ) (hB : 2 ≤ B) (v : Tapes t a)
    (focus : Fin 2 → Fin t) (hf : Function.Injective focus)
    (ks : List Bool) (k : ℕ) (hk : Counter.value ks = k) (ck : GrowingCounterData.Canonical ks)
    (h0 : v.tape (focus 0) = RadixZeroFill.encodedBinary ks) (p0 : v.head (focus 0) = 1)
    (h1 : v.tape (focus 1) = fun _ => blank) (p1 : v.head (focus 1) = 0) :
    HoareTime (powerProgram (a := a) B focus hf) (fun u => u = bank v)
      (fun u => u = bank (setTape v (focus 1) (RadixZeroFill.encodedBinary (bits (B^k))) 1))
      (FixedBasePowerDescriptor.constant B*B^k) := by
  let X := (FixedBasePowerDescriptor.input (q := a) ks).append (SharedBank.empty 7 a)
  have hr := hoare_extend_eq (FixedBasePowerDescriptor.constructs_linear (q := a) B k hB ks hk ck)
    (SharedBank.empty 7 a)
  have he : FixedBasePowerStep.bits B k = bits (B^k) :=
    canonical_bits _ _ (FixedBasePowerStep.bits_canonical B k) (FixedBasePowerStep.bits_value B k)
  rw [FixedBasePowerDescriptor.output,he,← SharedPlacementAlphabet.setTape_append_left] at hr
  apply single (powerCore (a := a) B) CompactGadgetReservationHeadersPowerRound.powerPorts
    CompactGadgetReservationHeadersPowerRound.power_injective focus hf v X 1 _ _ ?_ ?_ hr
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals simp [X,CompactGadgetReservationHeadersPowerRound.powerPorts,FixedBasePowerDescriptor.input,
      Tapes.append,Fin.addCases,CountedLoopReuseAlphabet.controls,SharedBank.empty,h0,h1,p0,p1,encoded_binary]
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals simp [X,CompactGadgetReservationHeadersPowerRound.powerPorts,FixedBasePowerDescriptor.input,
      Tapes.append,Fin.addCases,Fin.exists_fin_succ,CountedLoopReuseAlphabet.controls,SharedBank.empty]

def logNative (B : ℕ) := seq (FixedBasePowerUntil.program (q := a) B)
  (BinaryDescriptorCleanupList.oneProgram (a := a) (5 : Fin 9))
def logConstant (B : ℕ) := FixedBasePowerUntil.constant B*B+2*B+7

theorem log_native (B D : ℕ) (hB : 2 ≤ B) (hD : 0 < D)
    (ds : List Bool) (hd : Counter.value ds = D) (cd : GrowingCounterData.Canonical ds) :
    HoareTime (logNative (a := a) B) (fun v => v=FixedBasePowerUntil.input ds)
      (fun v => v=setTape (FixedBasePowerUntil.input ds) (7 : Fin 9)
        (RadixZeroFill.encodedBinary (bits (Nat.clog B D))) 1) (logConstant B*D) := by
  have h0 := FixedBasePowerUntilRange.constructs_threshold_linear (q := a) B D hB hD ds hd cd
  have h1 := BinaryDescriptorCleanupList.one_hoare (5 : Fin 9)
    (FixedBasePowerUntil.output (q := a) B (Nat.clog B D) ds)
    (FixedBasePowerStep.bits B (Nat.clog B D))
    (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm rfl
  have hc : FixedBasePowerUntil.counter (Nat.clog B D) = bits (Nat.clog B D) :=
    canonical_bits _ _ (FixedBasePowerUntil.counter_canonical _) (FixedBasePowerUntil.counter_value _)
  have he : setTape (FixedBasePowerUntil.output (q := a) B (Nat.clog B D) ds)
      5 (fun _ => blank) 0 = setTape (FixedBasePowerUntil.input ds) 7
        (RadixZeroFill.encodedBinary (bits (Nat.clog B D))) 1 := by
    unfold FixedBasePowerUntil.output
    rw [hc,BinaryDescriptorStackRoundtrip.descriptor_encoded]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h1
  have hl := GrowingCounterData.canonical_width _ (FixedBasePowerStep.bits_canonical B (Nat.clog B D))
  rw [FixedBasePowerStep.bits_value] at hl
  have hb := FixedBasePowerUntilRange.final_power_lt B D hB hD
  have hp := Nat.log2_le_self (B^Nat.clog B D)
  apply (h0.seq h1).consequence (fun _ h => h) (fun _ h => h)
  unfold logConstant
  nlinarith

def logPorts : Fin 2 → Fin 15 := fun i => Fin.castAdd 6 (![6,7] i : Fin 9)
theorem log_injective : Function.Injective logPorts := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [logPorts]
def logCore (B : ℕ) := extend (logNative (a := a) B) 6
def logProgram (B : ℕ) (focus : Fin 2 → Fin t) (hf : Function.Injective focus) :=
  placed (logCore (a := a) B) logPorts focus hf

theorem logarithm (B : ℕ) (hB : 2 ≤ B) (v : Tapes t a)
    (focus : Fin 2 → Fin t) (hf : Function.Injective focus)
    (ds : List Bool) (D : ℕ) (hD : 0 < D) (hd : Counter.value ds = D)
    (cd : GrowingCounterData.Canonical ds)
    (h0 : v.tape (focus 0) = RadixZeroFill.encodedBinary ds) (p0 : v.head (focus 0) = 1)
    (h1 : v.tape (focus 1) = fun _ => blank) (p1 : v.head (focus 1) = 0) :
    HoareTime (logProgram (a := a) B focus hf) (fun u => u=bank v)
      (fun u => u=bank (setTape v (focus 1)
        (RadixZeroFill.encodedBinary (bits (Nat.clog B D))) 1)) (logConstant B*D) := by
  let X := (FixedBasePowerUntil.input (q := a) ds).append (SharedBank.empty 6 a)
  have h := hoare_extend_eq (log_native (a := a) B D hB hD ds hd cd) (SharedBank.empty 6 a)
  rw [← SharedPlacementAlphabet.setTape_append_left] at h
  apply single (logCore (a := a) B) logPorts log_injective focus hf v X 1 _ _ ?_ ?_ h
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals simp [X,logPorts,FixedBasePowerUntil.input,Tapes.append,Fin.addCases,
      SharedBank.empty,setTape,h0,h1,p0,p1,BinaryDescriptorStackRoundtrip.descriptor_encoded]
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals simp [X,logPorts,FixedBasePowerUntil.input,Tapes.append,Fin.addCases,
      SharedBank.empty,setTape,Fin.exists_fin_succ]

end
end IntegerMultBounds.Machine.CompactGlobalRowHeaderPrimitives
