import IntegerMultBounds.Machine.BinaryPackedEarlyPrefixBudget

/-! Lift the complete original-descriptor repeated-offset constructor to the
payload alphabet without changing any physical step count. -/
namespace IntegerMultBounds.Machine.BinaryPackedEarlyPrefixAlphabet
open SharedPlacementAlphabet (setTape)
open StreamedFiberTranslationAlphabet (encoding mapTape)
open BinaryAddressOffsetRepeatAlphabet (word)
open BinaryParityXorOffsetRepeatData
variable {a : ℕ}
noncomputable section

def bank (hs : Fin 5 → List Bool) (Z : List Bool) (f : ℤ → Fin (a+4)) : Tapes 50 a :=
  ⟨fun i => if i.val<3 ∨ i=16 ∨ i=17 then 1 else 0,
    fun i => if h : i.val<3 then CountedLoopReuseAlphabet.binary (hs ⟨i.val,by omega⟩)
      else if i=16 then CountedLoopReuseAlphabet.binary (hs 3) else if i=17 then CountedLoopReuseAlphabet.binary (hs 4)
      else if i=8 then f else if i=18 then word Z else fun _ => blank⟩

def negativeProgram (a : ℕ) := Alphabet.program (encoding (a := a)) BinaryPackedEarlyPrefixNegative.program

theorem mapped_input (hs : Fin 5 → List Bool) (Z : List Bool) :
    Alphabet.mapTapes (encoding (a := a)) (BinaryPackedEarlyPrefixNegative.input hs Z)=bank hs Z (fun _ => blank) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact CountedLoopReuseAlphabet.encoding_binary _ | exact BinaryAddressOffsetRepeatAlphabet.mapped_word _

theorem mapped_output (hs : Fin 5 → List Bool) (Z : List Bool) (q b n L K : ℕ) (hb : 1≤b) (hbq : b+1≤q) :
    Alphabet.mapTapes (encoding (a := a)) (BinaryPackedEarlyPrefixNegative.output hs Z q b n L K hb hbq)=
      bank hs Z (word (destination q b n L K Z hb hbq)) := by
  rw [BinaryPackedEarlyPrefixNegative.output_eq]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact CountedLoopReuseAlphabet.encoding_binary _ |
    exact BinaryAddressOffsetRepeatAlphabet.mapped_word _

theorem output_eq (hs : Fin 5 → List Bool) (Z : List Bool) (f : ℤ → Fin (a+4)) :
    bank hs Z f=setTape (bank hs Z (fun _ => blank)) (8 : Fin 50) f 0 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem negative_constructs (hs : Fin 5 → List Bool) (Z : List Bool) (q b n L K : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (hvq : Counter.value (hs 0)=q) (hvb : Counter.value (hs 1)=b) (hvn : Counter.value (hs 2)=n)
    (hvL : Counter.value (hs 3)=L) (hvK : Counter.value (hs 4)=K)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hZ : Z.length=n) :
    HoareTime (negativeProgram a) (fun z => z=bank hs Z (fun _ => blank))
      (fun z => z=bank hs Z (word (destination q b n L K Z hb hbq)))
      (BinaryPackedEarlyPrefixNegative.cost hs q b n L K) := by
  have h := Alphabet.map_hoare (encoding (a := a))
    (BinaryPackedEarlyPrefixNegative.constructs hs Z q b n L K hb hbq hvq hvb hvn hvL hvK hc hZ)
  apply h.consequence _ _ le_rfl
  · rintro z rfl
    exact ⟨_,rfl,(mapped_input hs Z).symm⟩
  · rintro z ⟨v,rfl,rfl⟩
    exact mapped_output hs Z q b n L K hb hbq

def parityProgram (a : ℕ) := Alphabet.program (encoding (a := a)) BinaryPackedEarlyPrefixParity.program

theorem parity_mapped_input (hs : Fin 5 → List Bool) (Z : List Bool) :
    Alphabet.mapTapes (encoding (a := a)) (BinaryPackedEarlyPrefixParity.input hs Z)=bank hs Z (fun _ => blank) :=
  mapped_input hs Z

theorem parity_mapped_output (hs : Fin 5 → List Bool) (Z : List Bool) (q b n L K : ℕ) (hb : 1≤b) (hbq : b+1≤q) :
    Alphabet.mapTapes (encoding (a := a)) (BinaryPackedEarlyPrefixParity.output hs Z q b n L K hb hbq)=
      bank hs Z (word (BinaryAddressOffsetRepeatData.destination q b n L K hb hbq)) := by
  rw [BinaryPackedEarlyPrefixParity.output_eq]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact CountedLoopReuseAlphabet.encoding_binary _ |
    exact BinaryAddressOffsetRepeatAlphabet.mapped_word _

theorem parity_constructs (hs : Fin 5 → List Bool) (Z : List Bool) (q b n L K : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (hvq : Counter.value (hs 0)=q) (hvb : Counter.value (hs 1)=b) (hvn : Counter.value (hs 2)=n)
    (hvL : Counter.value (hs 3)=L) (hvK : Counter.value (hs 4)=K)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (parityProgram a) (fun z => z=bank hs Z (fun _ => blank))
      (fun z => z=bank hs Z (word (BinaryAddressOffsetRepeatData.destination q b n L K hb hbq)))
      (BinaryPackedEarlyPrefixParity.cost hs q b n L K) := by
  have h := Alphabet.map_hoare (encoding (a := a))
    (BinaryPackedEarlyPrefixParity.constructs hs Z q b n L K hb hbq hvq hvb hvn hvL hvK hc)
  apply h.consequence _ _ le_rfl
  · rintro z rfl
    exact ⟨_,rfl,(parity_mapped_input hs Z).symm⟩
  · rintro z ⟨v,rfl,rfl⟩
    exact parity_mapped_output hs Z q b n L K hb hbq

end
end IntegerMultBounds.Machine.BinaryPackedEarlyPrefixAlphabet
