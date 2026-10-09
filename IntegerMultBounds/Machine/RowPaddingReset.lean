import IntegerMultBounds.Machine.CountedPairPosition
import IntegerMultBounds.Machine.CountedPosition
import IntegerMultBounds.Machine.RowPaddingBlock

/-! Physical origin restoration after streaming padding or cropping. -/
namespace IntegerMultBounds.Machine.RowPaddingReset

theorem binary_zero (bs : List Bool) : CountedLoopReuseAlphabet.binary (a := 0) bs =
    CountedCopyReuse.binary bs := by
  have h := CountedLoopReuseAlphabet.encoding_binary (a := 0) bs
  simpa only [CountedLoopReuseAlphabet.encoding] using h.symm

def padProgram : Program 5 36 0 := seq (extend (CountedPairPosition.program Move.left) 1)
  (Placement.placed (CountedPosition.program Move.left) RowPaddingBlock.fillPlacement)

def cropProgram : Program 5 36 0 := seq (extend (CountedPairPosition.program Move.left) 1)
  (Placement.placed (CountedPosition.program Move.left) RowPaddingBlock.erasePlacement)

theorem position_endpoint (source dest : ℤ → Fin 4) (p q : ℤ) (valid padding : List Bool) :
    ((CountedPosition.bank dest q padding).append (RowPaddingBlock.spectators source p valid)).reindex
      RowPaddingBlock.fillPlacement = RowPaddingBlock.bank source dest p q valid padding := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> try rfl
  exact binary_zero padding

theorem crop_position_endpoint (source dest : ℤ → Fin 4) (p q : ℤ) (valid padding : List Bool) :
    ((CountedPosition.bank source p padding).append (RowPaddingBlock.spectators dest q valid)).reindex
      RowPaddingBlock.erasePlacement = RowPaddingBlock.bank source dest p q valid padding := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> try rfl
  exact binary_zero padding

theorem pad_hoare (source dest : ℤ → Fin 4) (p q : ℤ) (valid padding : List Bool) :
    HoareTime padProgram (fun v => v = RowPaddingBlock.bank source dest p q valid padding)
      (fun v => v = RowPaddingBlock.bank source dest (p-Counter.value valid)
        (q-Counter.value valid-Counter.value padding) valid padding)
      (7*Counter.value valid+7*valid.length+7*Counter.value padding+7*padding.length+33) := by
  have hm := hoare_extend_eq (CountedPairPosition.position_hoare Move.left source dest p q valid)
    (CountedRawFill.one (CountedCopyReuse.binary padding) 1)
  simp only [Move.offset,Int.mul_neg_one,← sub_eq_add_neg] at hm
  have hf := hoare_place (CountedPosition.position_hoare Move.left dest (q-Counter.value valid)
    padding (Counter.value padding) rfl) RowPaddingBlock.fillPlacement
    (RowPaddingBlock.spectators source (p-Counter.value valid) valid)
  simp only [Move.offset,Int.mul_neg_one,← sub_eq_add_neg] at hf
  rw [position_endpoint,position_endpoint] at hf
  have he : 7*Counter.value valid+7*valid.length+16+1+
      (7*Counter.value padding+7*padding.length+16) =
      7*Counter.value valid+7*valid.length+7*Counter.value padding+7*padding.length+33 := by omega
  simpa only [padProgram,Placement.placed,RowPaddingBlock.bank,he] using hm.seq hf

theorem crop_hoare (source dest : ℤ → Fin 4) (p q : ℤ) (valid padding : List Bool) :
    HoareTime cropProgram (fun v => v = RowPaddingBlock.bank source dest p q valid padding)
      (fun v => v = RowPaddingBlock.bank source dest
        (p-Counter.value valid-Counter.value padding) (q-Counter.value valid) valid padding)
      (7*Counter.value valid+7*valid.length+7*Counter.value padding+7*padding.length+33) := by
  have hm := hoare_extend_eq (CountedPairPosition.position_hoare Move.left source dest p q valid)
    (CountedRawFill.one (CountedCopyReuse.binary padding) 1)
  simp only [Move.offset,Int.mul_neg_one,← sub_eq_add_neg] at hm
  have hf := hoare_place (CountedPosition.position_hoare Move.left source (p-Counter.value valid)
    padding (Counter.value padding) rfl) RowPaddingBlock.erasePlacement
    (RowPaddingBlock.spectators dest (q-Counter.value valid) valid)
  simp only [Move.offset,Int.mul_neg_one,← sub_eq_add_neg] at hf
  rw [crop_position_endpoint,crop_position_endpoint] at hf
  have he : 7*Counter.value valid+7*valid.length+16+1+
      (7*Counter.value padding+7*padding.length+16) =
      7*Counter.value valid+7*valid.length+7*Counter.value padding+7*padding.length+33 := by omega
  simpa only [cropProgram,Placement.placed,RowPaddingBlock.bank,he] using hm.seq hf

end IntegerMultBounds.Machine.RowPaddingReset
