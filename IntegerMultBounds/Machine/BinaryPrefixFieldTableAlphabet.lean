import IntegerMultBounds.Machine.BinaryPrefixFieldTableRun
import IntegerMultBounds.Machine.PackedOffsetPayloadAlphabet

/-! Lift the complete generated-address field projection to arbitrary caller
alphabets, preserving the exact paid transition bound and blank workspace. -/
namespace IntegerMultBounds.Machine.BinaryPrefixFieldTableAlphabet
noncomputable section
open StreamedFiberTranslationAlphabet (encoding mapTape)
open SharedPlacementAlphabet (setTape)
variable {a : ℕ}

def bank (hs : Fin 3 → List Bool) (out : ℤ → Fin (a+4)) : Tapes 24 a :=
  ⟨fun i => if i.val<3 then 1 else 0,
    fun i => if h : i.val<3 then RadixZeroFill.encodedBinary (hs ⟨i.val,h⟩)
      else if i=7 then out else fun _ => blank⟩
def word (W start d : ℕ) (h : start+d≤W) : ℤ → Fin (a+4) :=
  putWord (fun _ => blank) 0 ((BinaryPrefixFieldTableData.word W start d h).map bitSymbol)
def program (a : ℕ) := Alphabet.program (encoding (a := a)) BinaryPrefixFieldTableRun.program

theorem mapped_input (hs : Fin 3 → List Bool) :
    Alphabet.mapTapes (encoding (a := a)) (BinaryPrefixFieldTableRun.input hs)=bank hs (fun _ => blank) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals rfl

theorem mapped_output (hs : Fin 3 → List Bool) (W start d : ℕ) (h : start+d≤W) :
    Alphabet.mapTapes (encoding (a := a)) (BinaryPrefixFieldTableRun.output hs W start d h)=bank hs (word W start d h) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl |
    exact PackedOffsetPayloadAlphabet.map_bits (fun _ => blank) 0 _

theorem output_eq (hs : Fin 3 → List Bool) (out : ℤ → Fin (a+4)) :
    bank hs out=setTape (bank hs (fun _ => blank)) 7 out 0 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem constructs (hs : Fin 3 → List Bool) (W start d : ℕ) (h : start+d≤W)
    (hv : ∀ i, Counter.value (hs i)=BinaryPrefixFieldTableGather.values W start d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program a) (fun v => v=bank hs (fun _ => blank))
      (fun v => v=bank hs (word W start d h)) (BinaryPrefixFieldTableRun.constant*(2^W*(W+1))) := by
  have hh := Alphabet.map_hoare (encoding (a := a)) (BinaryPrefixFieldTableRun.constructs_linear hs W start d h hv hc)
  refine hh.consequence ?_ ?_ le_rfl
  · rintro v rfl
    exact ⟨_,rfl,(mapped_input hs).symm⟩
  · rintro v ⟨z,rfl,rfl⟩
    exact mapped_output hs W start d h

end
end IntegerMultBounds.Machine.BinaryPrefixFieldTableAlphabet
