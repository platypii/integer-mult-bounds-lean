import IntegerMultBounds.Machine.CompactGadgetReservationHeadersCore

/-! Physical binary power and enclosing-multiple constructors, with the same
shared fifteen private tapes as the immutable product/subtraction stages. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationHeadersPowerRound
noncomputable section
open CompactGadgetReservationHeadersCore
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {t a : ℕ}

def powerPorts : Fin 2 → Fin 15 := fun i => Fin.castAdd 7 (![7,5] i : Fin 8)
theorem power_injective : Function.Injective powerPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [powerPorts]
def powerCore := extend (FixedBasePowerDescriptor.program (q := a) 2) 7
def powerProgram (focus : Fin 2 → Fin t) (hf : Function.Injective focus) :=
  placed (powerCore (a := a)) powerPorts focus hf

theorem power (v : Tapes t a) (focus : Fin 2 → Fin t) (hf : Function.Injective focus)
    (ks : List Bool) (k : ℕ) (hk : Counter.value ks = k) (ck : GrowingCounterData.Canonical ks)
    (h0 : v.tape (focus 0) = RadixZeroFill.encodedBinary ks) (p0 : v.head (focus 0) = 1)
    (h1 : v.tape (focus 1) = fun _ => blank) (p1 : v.head (focus 1) = 0) :
    HoareTime (powerProgram (a := a) focus hf) (fun u => u = bank v)
      (fun u => u = bank (setTape v (focus 1) (RadixZeroFill.encodedBinary (bits (2^k))) 1))
      (FixedBasePowerDescriptor.constant 2*2^k) := by
  let X := (FixedBasePowerDescriptor.input (q := a) ks).append (SharedBank.empty 7 a)
  have hr := hoare_extend_eq (FixedBasePowerDescriptor.constructs_linear (q := a) 2 k (by decide) ks hk ck)
    (SharedBank.empty 7 a)
  have he : FixedBasePowerStep.bits 2 k = bits (2^k) :=
    canonical_bits _ _ (FixedBasePowerStep.bits_canonical 2 k) (FixedBasePowerStep.bits_value 2 k)
  rw [FixedBasePowerDescriptor.output,he,← SharedPlacementAlphabet.setTape_append_left] at hr
  apply single (powerCore (a := a)) powerPorts power_injective focus hf v X 1 _ _ ?_ ?_ hr
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals simp [X,SharedBank.payload,powerPorts,FixedBasePowerDescriptor.input,Tapes.append,Fin.addCases,Fin.exists_fin_succ,
      CountedLoopReuseAlphabet.controls,SharedBank.empty,h0,h1,p0,p1,encoded_binary]
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals simp [X,SharedBank.strip,powerPorts,FixedBasePowerDescriptor.input,Tapes.append,Fin.addCases,Fin.exists_fin_succ,
      CountedLoopReuseAlphabet.controls,SharedBank.empty]

def roundPorts : Fin 3 → Fin 15 := ![0,1,5]
theorem round_injective : Function.Injective roundPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [roundPorts]
def roundProgram (focus : Fin 3 → Fin t) (hf : Function.Injective focus) :=
  placed (RoundedRowDescriptor.program (q := a)) roundPorts focus hf

theorem round (v : Tapes t a) (focus : Fin 3 → Fin t) (hf : Function.Injective focus)
    (rs ds : List Bool) (R D : ℕ) (hR : 0 < R) (hD : 0 < D)
    (hr : Counter.value rs = R) (hd : Counter.value ds = D)
    (cr : GrowingCounterData.Canonical rs) (cd : GrowingCounterData.Canonical ds)
    (h0 : v.tape (focus 0) = RadixZeroFill.encodedBinary rs) (p0 : v.head (focus 0) = 1)
    (h1 : v.tape (focus 1) = RadixZeroFill.encodedBinary ds) (p1 : v.head (focus 1) = 1)
    (h2 : v.tape (focus 2) = fun _ => blank) (p2 : v.head (focus 2) = 0) :
    HoareTime (roundProgram (a := a) focus hf) (fun u => u = bank v)
      (fun u => u = bank (setTape v (focus 2)
        (RadixZeroFill.encodedBinary (bits (RoundedRowDescriptor.rounded R D))) 1))
      (4096*RoundedRowDescriptor.rounded R D) := by
  let X := RoundedRowDescriptor.input (q := a) rs ds
  have hr0 := RoundedRowDescriptor.construct_hoare (q := a) rs ds R D hr hd cr cd hR hD
  have he : RoundedRowDescriptor.bits R D = bits (RoundedRowDescriptor.rounded R D) :=
    canonical_bits _ _ (RoundedRowDescriptor.bits_canonical R D) (RoundedRowDescriptor.bits_value R D)
  have hout : RoundedRowDescriptor.output (q := a) rs ds R D =
      setTape X (roundPorts 2) (RadixZeroFill.encodedBinary (bits (RoundedRowDescriptor.rounded R D))) 1 := by
    unfold RoundedRowDescriptor.output
    rw [he]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [hout] at hr0
  apply single _ roundPorts round_injective focus hf v X 2 _ _ ?_ ?_ hr0
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals simp [X,SharedBank.payload,roundPorts,RoundedRowDescriptor.input,
      RoundedRowDescriptor.bank,h0,h1,h2,p0,p1,p2]
    all_goals rfl
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals simp [X,SharedBank.strip,roundPorts,RoundedRowDescriptor.input,
      RoundedRowDescriptor.bank,SharedBank.empty,Fin.exists_fin_succ]
    all_goals rfl

end
end IntegerMultBounds.Machine.CompactGadgetReservationHeadersPowerRound
