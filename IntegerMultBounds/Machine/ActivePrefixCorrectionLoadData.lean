import IntegerMultBounds.Machine.ActivePrefixCorrectionOffsetPlaced
import IntegerMultBounds.Machine.ActivePrefixOffsetRepeatPlaced
import IntegerMultBounds.Machine.ActiveTargetRotation

/-! One fixed caller bank for a complete original-input correction load. Only
original descriptors and the array are supplied; all offset words and rotation
metadata begin blank and are physically constructed. -/
namespace IntegerMultBounds.Machine.ActivePrefixCorrectionLoadData
noncomputable section
open ActivePrefixSelectedOffsetBank (Shape values)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ}

def offsetWord (s : Shape) := ActivePrefixCorrectionOffsetData.word s

def prefixCount (s : Shape) (rows : ℕ) := rows*2^s.W
def width (s : Shape) := s.n*s.q
def volume (s : Shape) (rows B : ℕ) := prefixCount s rows*(2^width s*B)
abbrev Array (s : Shape) (rows B : ℕ) := Fin (volume s rows B) → Bool

def producerFocus : Fin 9 → Fin 19 := ![0,1,2,3,4,5,6,7,11]
def headerFocus : Fin 10 → Fin 19 := ![0,3,4,5,7,13,14,15,16,17]
def productFocus : Fin 3 → Fin 19 := ![13,8,18]
def repeatFocus : Fin 3 → Fin 19 := ![8,11,12]
def rotateFocus : Fin 5 → Fin 19 := ![10,12,9,18,17]
def derivedFocus : Fin 5 → Fin 19 := ![13,14,15,16,17]
theorem producer_injective : Function.Injective producerFocus := by decide
theorem header_injective : Function.Injective headerFocus := by decide
theorem product_injective : Function.Injective productFocus := by decide
theorem repeat_injective : Function.Injective repeatFocus := by decide
theorem rotate_injective : Function.Injective rotateFocus := by decide
theorem derived_injective : Function.Injective derivedFocus := by decide

def base (s : Shape) (rows B : ℕ) (hs : Fin 8 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) : Tapes 19 a :=
  ⟨fun i => if i.val<10 then 1 else 0,
    fun i => if h : i.val<8 then RadixZeroFill.encodedBinary (hs ⟨i.val,h⟩)
      else if i.val=8 then RadixZeroFill.encodedBinary rs
      else if i.val=9 then RadixZeroFill.encodedBinary bs
      else if i.val=10 then ActiveTargetRotation.word x
      else fun _ => blank⟩
def produced (v : Tapes 19 a) (s : Shape) := ActivePrefixCorrectionOffsetPlaced.result v producerFocus s
def headers (v : Tapes 19 a) (s : Shape) :=
  ActivePrefixOffsetHeadersData.result (produced v s) headerFocus s.W s.q s.b s.n s.f
def dimensions (v : Tapes 19 a) (s : Shape) (rows : ℕ) :=
  setTape (headers v s) 18 (RadixZeroFill.encodedBinary (bits (prefixCount s rows))) 1

def offsets (s : Shape) (rows : ℕ) := BinaryAddressOffsetRepeatData.copies (offsetWord s) rows
def repeated (v : Tapes 19 a) (s : Shape) (rows : ℕ) :=
  ActivePrefixOffsetRepeatPlaced.result (dimensions v s rows) repeatFocus (offsetWord s) rows

def rotated (v : Tapes 19 a) (s : Shape) (rows B : ℕ) (x : Array s rows B) :=
  ActiveTargetRotation.result (repeated v s rows) rotateFocus (offsets s rows) (width s) (prefixCount s rows) B x

def headerWords (hs : Fin 8 → List Bool) : Fin 5 → List Bool := ![hs 0,hs 3,hs 4,hs 5,hs 7]

theorem offsets_length (s : Shape) (rows : ℕ) : (offsets s rows).length=prefixCount s rows*width s := by
  simp only [offsets,BinaryAddressOffsetRepeatData.copies_length,offsetWord,
    ActivePrefixCorrectionOffsetData.word_length,prefixCount,width]
  ring

theorem producer_sources (s : Shape) (rows B : ℕ) (hs : Fin 8 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) : SharedBank.payload (base (a := a) s rows B hs rs bs x) producerFocus=
      ActivePrefixCorrectionOffsetPlaced.sources hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem header_sources (s : Shape) (rows B : ℕ) (hs : Fin 8 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) : SharedBank.payload (produced (base (a := a) s rows B hs rs bs x) s) headerFocus=
      ActivePrefixOffsetHeadersData.sources (headerWords hs) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem repeat_sources (s : Shape) (rows B : ℕ) (hs : Fin 8 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) : SharedBank.payload (dimensions (base (a := a) s rows B hs rs bs x) s rows) repeatFocus=
      ActivePrefixOffsetRepeatPlaced.sources (offsetWord s) rs := by
  rw [ActivePrefixOffsetRepeatPlaced.sources_eq]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem rotation_tapes (s : Shape) (rows B : ℕ) (hs : Fin 8 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) : ∀ i,
    (repeated (base (a := a) s rows B hs rs bs x) s rows).tape (rotateFocus i)=
      PackedOffsetPayloadPlaced.tapes (ActiveTargetRotation.word x) (ActiveTargetRotation.offsets (offsets s rows))
        bs (bits (prefixCount s rows)) (bits (width s)) i := by
  intro i
  fin_cases i
  all_goals first | rfl | exact CountedLoopReuseAlphabet.encoding_binary _

theorem rotation_heads (s : Shape) (rows B : ℕ) (hs : Fin 8 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) : ∀ i,
    (repeated (base (a := a) s rows B hs rs bs x) s rows).head (rotateFocus i)=
      PackedOffsetPayloadPlaced.heads 0 0 i := by
  intro i
  fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.ActivePrefixCorrectionLoadData
