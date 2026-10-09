import IntegerMultBounds.Compact.LatePowerTwoWords
import IntegerMultBounds.Machine.CountedLateRepairKeyBank

/-! Literal physical later inverse and toggle words encode the exact destination rank. -/
namespace IntegerMultBounds.Compact.PowerTwo
noncomputable section
open IntegerMultBounds.Counter (value)
open IntegerMultBounds.Machine
open CountedLateRepairInverse

variable (q b : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) (X V W U : List Bool)
variable (hq : 1 ≤ q) (hV : V.length=X.length*q) (hW : W.length=X.length*b)
variable (hU : U.length=X.length*b)

def lateRecovered : LateAddress (Bi b) (Li q) (controls X).length :=
  lateWordsAddr q b X (CountedLateRepairInverse.target q b hb hbq V W U X) (temp q b hb hbq V W U X)
    (restored b hb U X) hq
    ((lengths q b hb hbq V W U X hV hW hU).2.2.2.2.1.trans hV)
    ((lengths q b hb hbq V W U X hV hW hU).2.2.2.2.2.trans hW)
    ((lengths q b hb hbq V W U X hV hW hU).2.2.2.1.trans hU)

theorem late_inverse_words :
    (lateSperm q b X).symm (lateWordsAddr q b X V W U hq hV hW hU) =
      lateRecovered q b hb hbq X V W U hq hV hW hU := by
  rw [Equiv.symm_apply_eq]
  have h := packedLatePerm_agrees (2*Li q) (Bi b) (by have := Li_pos q; omega)
    (by have := Bi_one b; omega) (controls X)
    (lateRecovered q b hb hbq X V W U hq hV hW hU)
  change (_,_,_) = packedLate (2*Li q) (Bi b) (controls X)
    (value (CountedLateRepairInverse.target q b hb hbq V W U X)) (value (temp q b hb hbq V W U X))
    (value (restored b hb U X)) at h
  have hv := value_spec q b hb hbq V W U X hV hW hU
  rw [← two_Li q hq] at hv
  rw [hv] at h
  apply Prod.ext
  · exact Subtype.ext (congrArg (fun z => z.2.2) h).symm
  · apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst h).symm
    · exact Subtype.ext (congrArg (fun z => z.2.1) h).symm

theorem late_ideal_words (hV : V.length=X.length*q) :
    lateTperm q b X (lateWordsAddr q b X V W U hq hV hW hU) =
      lateWordsAddr q b X (CountedIdealToggle.word q V X) W U hq
        ((CountedIdealToggle.word_length q V X hq hV).trans hV) hW hU := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply Subtype.ext
      have h := idealTarget_value (Li q) (Li_pos q) (controls X) (controls_bits X)
        (lateWordsAddr q b X V W U hq hV hW hU).2.1
      change (idealTarget (Li q) (Li_pos q) (controls X) (controls_bits X)
        (lateWordsAddr q b X V W U hq hV hW hU).2.1).val = _
      rw [h]
      change Radix.pack (2*Li q) (toggleList (Radix.digits (2*Li q) (controls X).length (value V)) (controls X)) = (value (CountedIdealToggle.word q V X) : ℤ)
      rw [two_Li q hq,controls_length]
      exact (CountedIdealToggle.value q hq V X hV).symm
    · rfl

theorem late_destination_words :
    rankBits (X.length*q+X.length*b+X.length*b)
      (lateRankEquiv q b X (lateTperm q b X
        ((lateSperm q b X).symm (lateWordsAddr q b X V W U hq hV hW hU)))).val =
      CountedLateRepairKeyBank.bits q b hb hbq V W U X := by
  rw [late_inverse_words q b hb hbq X V W U hq hV hW hU]
  unfold lateRecovered
  rw [late_ideal_words,late_words_bits]
  simp only [CountedLateRepairKeyBank.bits,CountedLateRepairKeyBank.target,
    CountedLateRepairKeyBank.dirty,List.append_assoc]

end
end IntegerMultBounds.Compact.PowerTwo
