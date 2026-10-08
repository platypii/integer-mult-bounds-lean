import IntegerMultBounds.Machine.RadixLinearCombinationShared
import IntegerMultBounds.Machine.CountedLoopReuseAlphabet

/-! Erase an actual encoded binary descriptor and its sentinel, restoring a
fully blank tape at origin. No length descriptor is supplied to the machine. -/
namespace IntegerMultBounds.Machine.MarkedBinaryCleanup

open MarkedWordCleanup (one empty marked)
variable {q : ℕ}

private theorem bits_word (f : ℤ → Fin (q+4)) (p : ℤ) (bs : List Bool) :
    CountedLoopAlphabet.putBits f p bs = putWord f p (bs.map bitSymbol) := by
  induction bs generalizing p with
  | nil => rfl
  | cons b bs ih => simp only [CountedLoopAlphabet.putBits,putWord,List.map_cons,ih]

theorem binary_state (bs : List Bool) :
    RadixToBinary.binaryState q bs = one (marked (bs.map bitSymbol)) 1 := by
  have hh := CountedLoopReuseAlphabet.encoding_binary (a := q) bs
  rw [CountedLoopReuseAlphabet.binary,bits_word] at hh
  unfold RadixToBinary.binaryState Alphabet.mapTapes GrowingCounter.tapes one
  congr 1
  funext i
  exact hh

/-- Four fixed states suffice to erase, rewind and erase the sentinel. -/
def program : Program 1 4 q := seq (seq MarkedWordCleanup.clearProgram (Rewind.program separator)) MarkedWordCleanup.unmarkProgram

private theorem word_hoare (xs : List (Fin (q+4))) (hn : ∀ x ∈ xs, x ≠ blank) :
    HoareTime program (fun v => v = one (marked xs) 1) (fun v => v = one (fun _ => blank) 0) (2*xs.length+4) := by
  have hr := Rewind.rewind_hoare (separator : Fin (q+4)) empty (xs.length+1) (xs.length+1)
    (by intro j hj; simp [empty,show (xs.length:ℤ)+1-j ≠ 0 by omega,blank,separator,Fin.ext_iff])
    (by simp [empty])
  have hr' : HoareTime (Rewind.program (separator : Fin (q+4)))
      (fun v => v = one empty (1+xs.length)) (fun v => v = one empty 0) (xs.length+1) := by
    simpa only [Rewind.cfg,Config.tapes,one,sub_self,Nat.cast_add,Nat.cast_one,add_comm] using hr
  exact (((MarkedWordCleanup.clear_hoare xs hn).seq hr').seq (MarkedWordCleanup.unmark_hoare [])).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

theorem cleanup_hoare (bs : List Bool) :
    HoareTime (program (q := q)) (fun v => v = RadixToBinary.binaryState q bs)
      (fun v => v = one (fun _ => blank) 0) (2*bs.length+4) := by
  have hn : ∀ x ∈ bs.map (bitSymbol : Bool → Fin (q+4)), x ≠ blank := by
    intro x hx
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx
    cases b <;> simp [bitSymbol,blank,Fin.ext_iff]
  rw [binary_state]
  simpa only [List.length_map] using word_hoare (bs.map bitSymbol) hn

end IntegerMultBounds.Machine.MarkedBinaryCleanup
