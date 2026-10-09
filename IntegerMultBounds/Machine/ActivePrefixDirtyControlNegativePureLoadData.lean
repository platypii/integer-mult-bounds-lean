import IntegerMultBounds.Machine.ActivePrefixDirtyControlLoad
import IntegerMultBounds.Machine.ActivePrefixDirtyControlNegativePureData

/-! Source-unload path inserts real rowwise negation after the pure-parity
producer and dimension construction. Positive, negative and repeated streams
reuse two work tapes; both are erased after rotation. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlNegativePureLoadData
noncomputable section
open ActivePrefixDirtyControlLoadProducer (width values)
open ActivePrefixDirtyControlLoadData (prefixCount volume Array base dimensions)
open ActivePrefixDirtyControlNegativePureData (negative rows rows_flatten rows_uniform rows_length)
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ}
abbrev Shape := ActivePrefixDirtyControlLoadProducer.Shape .pure

def negateFocus : Fin 4 → Fin 14 := ![9,10,12,11]
def repeatFocus : Fin 3 → Fin 14 := ![6,10,9]
def rotateFocus : Fin 5 → Fin 14 := ![8,9,7,13,12]

def negated (v : Tapes 14 a) (s : Shape) (rowCount : ℕ) :=
  ActivePrefixParityNegativeNegate.result (dimensions v s rowCount) negateFocus (negative s)
def offsets (s : Shape) (rowCount : ℕ) := BinaryAddressOffsetRepeatData.copies (negative s) rowCount
def repeated (v : Tapes 14 a) (s : Shape) (rowCount : ℕ) :=
  ActivePrefixOffsetRepeatPlaced.result (negated v s rowCount) repeatFocus (negative s) rowCount
def rotated (v : Tapes 14 a) (s : Shape) (rowCount B : ℕ) (x : Array s rowCount B) :=
  ActiveTargetRotation.result (repeated v s rowCount) rotateFocus (offsets s rowCount) (width s) (prefixCount s rowCount) B x

theorem offsets_length (s : Shape) (rowCount : ℕ) : (offsets s rowCount).length=prefixCount s rowCount*width s := by
  simp only [offsets,BinaryAddressOffsetRepeatData.copies_length,ActivePrefixDirtyControlNegativePureData.negative_length s,
    prefixCount,width,ActivePrefixDirtyControlLoadProducer.sourceKind,ActivePrefixDirtyControlData.outputRowWidth,BinaryVaryingOffsetGatherPlaced.outputWidth]
  ring

theorem negate_sources (s : Shape) (rowCount B : ℕ) (hs : Fin 6 → List Bool) (rs bs : List Bool)
    (x : Array s rowCount B) : SharedBank.payload (dimensions (base (a := a) s rowCount B hs rs bs x) s rowCount) negateFocus=
      ActivePrefixParityNegativeNegate.sources (rows s).flatten (bits (width s)) (bits (2^s.W)) := by
  rw [rows_flatten s,ActivePrefixParityNegativeNegate.sources,ActivePrefixParityNegativeNegate.local_payload]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem repeat_sources (s : Shape) (rowCount B : ℕ) (hs : Fin 6 → List Bool) (rs bs : List Bool)
    (x : Array s rowCount B) : SharedBank.payload (negated (base (a := a) s rowCount B hs rs bs x) s rowCount) repeatFocus=
      ActivePrefixOffsetRepeatPlaced.sources (negative s) rs := by
  rw [ActivePrefixOffsetRepeatPlaced.sources_eq]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem rotation_tapes (s : Shape) (rowCount B : ℕ) (hs : Fin 6 → List Bool) (rs bs : List Bool)
    (x : Array s rowCount B) : ∀ i,
    (repeated (base (a := a) s rowCount B hs rs bs x) s rowCount).tape (rotateFocus i)=
      PackedOffsetPayloadPlaced.tapes (ActiveTargetRotation.word x) (ActiveTargetRotation.offsets (offsets s rowCount))
        bs (bits (prefixCount s rowCount)) (bits (width s)) i := by
  intro i; fin_cases i
  all_goals first | rfl | exact CountedLoopReuseAlphabet.encoding_binary _

theorem rotation_heads (s : Shape) (rowCount B : ℕ) (hs : Fin 6 → List Bool) (rs bs : List Bool)
    (x : Array s rowCount B) : ∀ i,
    (repeated (base (a := a) s rowCount B hs rs bs x) s rowCount).head (rotateFocus i)=
      PackedOffsetPayloadPlaced.heads 0 0 i := by
  intro i; fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlNegativePureLoadData
