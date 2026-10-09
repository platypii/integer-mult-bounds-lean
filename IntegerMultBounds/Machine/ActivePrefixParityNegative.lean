import IntegerMultBounds.Machine.ActivePrefixParityNegativeRun

/-! Complete clean negative parity-XOR stream, synthesized only from the
original eight descriptors. Every original prefix uses its own current row. -/
namespace IntegerMultBounds.Machine.ActivePrefixParityNegative
noncomputable section
open ActivePrefixParityOffsetBank (Shape values)
variable {a : ℕ}

def input (hs : Fin 8 → List Bool) := ActivePrefixParityNegativeRun.bank (ActivePrefixParityNegativeBank.base (a := a) hs)
def output (s : Shape) (hs : Fin 8 → List Bool) := ActivePrefixParityNegativeRun.bank (ActivePrefixParityNegativeBank.output (a := a) s hs)
def program := ActivePrefixParityNegativeRun.program (a := a)
def constant := ActivePrefixParityNegativeRun.constant

theorem runs_linear (s : Shape) (hs : Fin 8 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a)) (fun x => x=input hs) (fun x => x=output s hs)
      (constant*(2^s.W*(s.W+1))) :=
  ActivePrefixParityNegativeRun.runs s hs hv hc

 theorem output_eq (s : Shape) (hs : Fin 8 → List Bool) :
    output (a := a) s hs=SharedPlacementAlphabet.setTape (input hs) (9 : Fin 56)
      (ActivePrefixParityNegativeNegate.word (ActivePrefixParityNegativeData.negative s)) 0 := by
  rw [output,ActivePrefixParityNegativeBank.output_eq]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.ActivePrefixParityNegative
