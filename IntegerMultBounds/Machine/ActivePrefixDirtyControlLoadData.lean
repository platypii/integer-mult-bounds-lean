import IntegerMultBounds.Machine.ActivePrefixDirtyControlLoadProducer
import IntegerMultBounds.Machine.ActivePrefixOffsetRepeatPlaced
import IntegerMultBounds.Machine.ActiveTargetRotation

/-! Original six dirty-U headers, original row/suffix descriptors and one array.
Five blank work tapes hold the original/repeated offsets and three dimensions. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlLoadData
noncomputable section
open ActivePrefixDirtyControlLoadProducer (Mode Shape values width word)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ} {m : Mode}

def prefixCount (s : Shape m) (rows : ℕ) := rows*2^s.W
def volume (s : Shape m) (rows B : ℕ) := prefixCount s rows*(2^width s*B)
abbrev Array (s : Shape m) (rows B : ℕ) := Fin (volume s rows B) → Bool

def producerFocus : Fin 7 → Fin 14 := ![0,1,2,3,4,5,9]
def powerFocus : Fin 2 → Fin 14 := ![0,11]
def widthSlot : Mode → Fin 14 | .selected | .correction => 3 | .pure | .negative => 4
def widthFocus (m : Mode) : Fin 3 → Fin 14 := ![widthSlot m,5,12]
def productFocus : Fin 3 → Fin 14 := ![11,6,13]
def repeatFocus : Fin 3 → Fin 14 := ![6,9,10]
def rotateFocus : Fin 5 → Fin 14 := ![8,10,7,13,12]
theorem width_injective : Function.Injective (widthFocus m) := by cases m <;> decide

def base (s : Shape m) (rows B : ℕ) (hs : Fin 6 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) : Tapes 14 a :=
  ⟨fun i => if i.val<8 then 1 else 0,
    fun i => if h : i.val<6 then RadixZeroFill.encodedBinary (hs ⟨i.val,h⟩)
      else if i.val=6 then RadixZeroFill.encodedBinary rs
      else if i.val=7 then RadixZeroFill.encodedBinary bs
      else if i.val=8 then ActiveTargetRotation.word x
      else fun _ => blank⟩
def produced (v : Tapes 14 a) (s : Shape m) := ActivePrefixDirtyControlLoadProducer.result v producerFocus s
def powered (v : Tapes 14 a) (s : Shape m) :=
  setTape (produced v s) 11 (RadixZeroFill.encodedBinary (bits (2^s.W))) 1
def headers (v : Tapes 14 a) (s : Shape m) :=
  setTape (powered v s) 12 (RadixZeroFill.encodedBinary (bits (width s))) 1
def dimensions (v : Tapes 14 a) (s : Shape m) (rows : ℕ) :=
  setTape (headers v s) 13 (RadixZeroFill.encodedBinary (bits (prefixCount s rows))) 1

def offsets (s : Shape m) (rows : ℕ) := BinaryAddressOffsetRepeatData.copies (word s) rows
def repeated (v : Tapes 14 a) (s : Shape m) (rows : ℕ) :=
  ActivePrefixOffsetRepeatPlaced.result (dimensions v s rows) repeatFocus (word s) rows

def rotated (v : Tapes 14 a) (s : Shape m) (rows B : ℕ) (x : Array s rows B) :=
  ActiveTargetRotation.result (repeated v s rows) rotateFocus (offsets s rows) (width s) (prefixCount s rows) B x

theorem offsets_length (s : Shape m) (rows : ℕ) : (offsets s rows).length=prefixCount s rows*width s := by
  simp only [offsets,BinaryAddressOffsetRepeatData.copies_length,ActivePrefixDirtyControlLoadProducer.word_length,prefixCount]
  ring

theorem producer_sources (s : Shape m) (rows B : ℕ) (hs : Fin 6 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) : SharedBank.payload (base (a := a) s rows B hs rs bs x) producerFocus=
      ActivePrefixDirtyControlLoadProducer.sources hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem repeat_sources (s : Shape m) (rows B : ℕ) (hs : Fin 6 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) : SharedBank.payload (dimensions (base (a := a) s rows B hs rs bs x) s rows) repeatFocus=
      ActivePrefixOffsetRepeatPlaced.sources (word s) rs := by
  rw [ActivePrefixOffsetRepeatPlaced.sources_eq]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem rotation_tapes (s : Shape m) (rows B : ℕ) (hs : Fin 6 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) : ∀ i,
    (repeated (base (a := a) s rows B hs rs bs x) s rows).tape (rotateFocus i)=
      PackedOffsetPayloadPlaced.tapes (ActiveTargetRotation.word x) (ActiveTargetRotation.offsets (offsets s rows))
        bs (bits (prefixCount s rows)) (bits (width s)) i := by
  intro i; fin_cases i
  all_goals first | rfl | exact CountedLoopReuseAlphabet.encoding_binary _

theorem rotation_heads (s : Shape m) (rows B : ℕ) (hs : Fin 6 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) : ∀ i,
    (repeated (base (a := a) s rows B hs rs bs x) s rows).head (rotateFocus i)=
      PackedOffsetPayloadPlaced.heads 0 0 i := by
  intro i; fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlLoadData
