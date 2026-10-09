import IntegerMultBounds.Machine.BinaryAddressOffsetRepeatValue
import IntegerMultBounds.Machine.PackedOffsetPayloadAlphabet

/-! The physically initialized repetition machine on any larger fixed
alphabet, with identical runtime and literal binary output. -/
namespace IntegerMultBounds.Machine.BinaryAddressOffsetRepeatAlphabet
open BinaryAddressOffsetRepeatData
open StreamedFiberTranslationAlphabet (encoding mapTape)
variable {a : ℕ}
noncomputable section

def word (xs : List Bool) : ℤ → Fin (a+4) := putWord (fun _ => blank) 0 (xs.map bitSymbol)
def bank (f g : ℤ → Fin (a+4)) (hs : Fin 4 → List Bool) : Tapes 11 a :=
  ⟨![0,0,0,0,1,0,1,0,1,0,1],![f,g,(fun _ => blank),(fun _ => blank),CountedLoopReuseAlphabet.binary (hs 0),
    (fun _ => blank),CountedLoopReuseAlphabet.binary (hs 1),(fun _ => blank),
    CountedLoopReuseAlphabet.binary (hs 2),(fun _ => blank),CountedLoopReuseAlphabet.binary (hs 3)]⟩
def program (a : ℕ) := Alphabet.program (encoding (a := a)) BinaryAddressOffsetRepeat.program

theorem mapped_bank (f g : ℤ → Fin 4) (hs : Fin 4 → List Bool) :
    Alphabet.mapTapes (encoding (a := a)) (BinaryAddressOffsetRepeat.raw f g 0 0 hs)=
      bank (mapTape f) (mapTape g) hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact CountedLoopReuseAlphabet.encoding_binary _

theorem mapped_word (xs : List Bool) : mapTape (a := a) (word xs)=word xs :=
  PackedOffsetPayloadAlphabet.map_bits (fun _ => blank) 0 xs

theorem runs (blocks : List (List Bool)) (W L K : ℕ) (hu : BlockRotationData.Uniform W blocks)
    (hs : Fin 4 → List Bool) (hw : Counter.value (hs 0)=W) (hl : Counter.value (hs 1)=L)
    (hn : Counter.value (hs 2)=blocks.length) (hk : Counter.value (hs 3)=K) :
    HoareTime (program a) (fun z => z=bank (word blocks.flatten) (fun _ => blank) hs)
      (fun z => z=bank (fun _ => blank) (word (copies (expanded blocks L) K)) hs)
      (BinaryAddressOffsetRepeat.cost W L blocks.length K hs) := by
  have hh := Alphabet.map_hoare (encoding (a := a)) (BinaryAddressOffsetRepeat.runs blocks W L K hu hs hw hl hn hk)
  apply hh.consequence _ _ le_rfl
  · rintro z rfl
    refine ⟨_,rfl,?_⟩
    rw [mapped_bank]
    change bank (word blocks.flatten) (fun _ => blank) hs=bank (mapTape (word blocks.flatten)) (fun _ => blank) hs
    rw [mapped_word]
  · rintro z ⟨small,rfl,rfl⟩
    rw [mapped_bank]
    change bank (fun _ => blank) (mapTape (word (copies (expanded blocks L) K))) hs=_
    rw [mapped_word]

end
end IntegerMultBounds.Machine.BinaryAddressOffsetRepeatAlphabet
