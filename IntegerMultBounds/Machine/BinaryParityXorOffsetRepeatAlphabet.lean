import IntegerMultBounds.Machine.BinaryParityXorOffsetRepeatBudget

/-! Lift the complete original-descriptor repeated-offset constructor to the
payload alphabet without changing any physical step count. -/
namespace IntegerMultBounds.Machine.BinaryParityXorOffsetRepeatAlphabet
open SharedPlacementAlphabet (setTape)
open StreamedFiberTranslationAlphabet (encoding mapTape)
open BinaryAddressOffsetRepeatAlphabet (word)
open BinaryParityXorOffsetRepeatData
variable {a : ℕ}
noncomputable section

def bank (hs : Fin 6 → List Bool) (Z : List Bool) (f : ℤ → Fin (a+4)) : Tapes 50 a :=
  ⟨fun i => if i.val<6 then 1 else 0,
    fun i => if h : i.val<6 then CountedLoopReuseAlphabet.binary (hs ⟨i.val,h⟩) else if i=9 then f else if i=18 then word Z else fun _ => blank⟩
def program (a : ℕ) := Alphabet.program (encoding (a := a)) BinaryParityXorOffsetRepeatConstruct.program

theorem mapped_input (hs : Fin 6 → List Bool) (Z : List Bool) :
    Alphabet.mapTapes (encoding (a := a)) (BinaryParityXorOffsetRepeatConstruct.input hs Z)=bank hs Z (fun _ => blank) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact CountedLoopReuseAlphabet.encoding_binary _ | exact BinaryAddressOffsetRepeatAlphabet.mapped_word _

theorem mapped_output (hs : Fin 6 → List Bool) (Z : List Bool) (q b n P H L : ℕ) (hb : 1≤b) (hbq : b+1≤q) :
    Alphabet.mapTapes (encoding (a := a)) (BinaryParityXorOffsetRepeatConstruct.output hs Z q b n P H L hb hbq)=
      bank hs Z (word (destination q b n L ((P*H)*2^(n*b)) Z hb hbq)) := by
  rw [BinaryParityXorOffsetRepeatConstruct.output_eq]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact CountedLoopReuseAlphabet.encoding_binary _ |
    exact BinaryAddressOffsetRepeatAlphabet.mapped_word _

theorem output_eq (hs : Fin 6 → List Bool) (Z : List Bool) (f : ℤ → Fin (a+4)) :
    bank hs Z f=setTape (bank hs Z (fun _ => blank)) (9 : Fin 50) f 0 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem constructs (hs : Fin 6 → List Bool) (Z : List Bool) (q b n P H L : ℕ) (hb : 1≤b) (hbq : b+1≤q) (hH : 0<H)
    (hvq : Counter.value (hs 0)=q) (hvb : Counter.value (hs 1)=b) (hvn : Counter.value (hs 2)=n)
    (hvP : Counter.value (hs 3)=P) (hvH : Counter.value (hs 4)=H) (hvL : Counter.value (hs 5)=L)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hZ : Z.length=n) :
    HoareTime (program a) (fun z => z=bank hs Z (fun _ => blank))
      (fun z => z=bank hs Z (word (destination q b n L ((P*H)*2^(n*b)) Z hb hbq)))
      (BinaryParityXorOffsetRepeatConstruct.cost hs q b n P H L) := by
  have h := Alphabet.map_hoare (encoding (a := a))
    (BinaryParityXorOffsetRepeatConstruct.constructs hs Z q b n P H L hb hbq hH hvq hvb hvn hvP hvH hvL hc hZ)
  apply h.consequence _ _ le_rfl
  · rintro z rfl
    exact ⟨_,rfl,(mapped_input hs Z).symm⟩
  · rintro z ⟨v,rfl,rfl⟩
    exact mapped_output hs Z q b n P H L hb hbq

end
end IntegerMultBounds.Machine.BinaryParityXorOffsetRepeatAlphabet
