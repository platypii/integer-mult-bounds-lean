import IntegerMultBounds.Machine.ElementaryMultiplyOutputData
import IntegerMultBounds.Assembly

/-! A complete fixed elementary multiplication machine. Real scanning erases
the original packed input, and a preserved operand clocks the padded reverse
copy of the Horner accumulator onto tape zero. This gives correctness at every
input length with quadratic cost, for use as a finite small-input fallback. -/
namespace IntegerMultBounds.Machine.ElementaryMultiply
noncomputable section
variable {a : ℕ}
open ElementaryMultiplyCore (bank)

def seekPlacement : Fin (2+2) ≃ Fin 4 where
  toFun := ![3,1,0,2]
  invFun := ![2,1,3,0]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
def accPlacement : Fin (1+3) ≃ Fin 4 where
  toFun := ![3,0,1,2]
  invFun := ![1,2,3,0]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
def copyPlacement : Fin (3+1) ≃ Fin 4 where
  toFun := ![3,1,0,2]
  invFun := ![2,1,3,0]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def scanPart := extend (MultiplicationInputSplit.scan (a := a) blank) 3
def erasePart := extend (EraseBack.program (a := a)) 3
def seekPart := reindex (extend (DoubleClockReverseCopy.doubleSeekProgram a) 2) seekPlacement
def rewindPart := ElementaryMultiplyCore.rewindPart (a := a)
def shiftPart := reindex (extend (MultiplicationInputSplit.shift (a := a) .left) 3) accPlacement
def copyPart := reindex (extend (DoubleClockReverseCopy.reverseCopyProgram a) 1) copyPlacement
/-- One finite program works for all input lengths. -/
def program (a : ℕ) := seq (seq (seq (seq (seq (seq (ElementaryMultiplyCore.program a)
  (scanPart (a := a))) (erasePart (a := a))) (seekPart (a := a)))
  (rewindPart (a := a))) (shiftPart (a := a))) (copyPart (a := a))

theorem source_bank (f x y acc : ℤ → Fin (a+4)) (p px py pa : ℤ) :
    ((⟨fun _ => p,fun _ => f⟩ : Tapes 1 a).append
      (MultiplicationInputSplit.bank x y acc px py pa)) = bank f x y acc p px py pa := by
  unfold MultiplicationInputSplit.bank ElementaryMultiplyCore.bank Tapes.append
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem seek_bank (f x y acc : ℤ → Fin (a+4)) (p px py pa : ℤ) :
    ((DoubleClockReverseCopy.seekBank acc x pa px).append
      (MultiplicationInputSplit.pair f y p py)).reindex seekPlacement = bank f x y acc p px py pa := by
  unfold DoubleClockReverseCopy.seekBank MultiplicationInputSplit.pair ElementaryMultiplyCore.bank
    Tapes.append Tapes.reindex seekPlacement
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem acc_bank (f x y acc : ℤ → Fin (a+4)) (p px py pa : ℤ) :
    ((⟨fun _ => pa,fun _ => acc⟩ : Tapes 1 a).append
      (MultiplicationInputSplit.bank f x y p px py)).reindex accPlacement = bank f x y acc p px py pa := by
  unfold MultiplicationInputSplit.bank ElementaryMultiplyCore.bank Tapes.append Tapes.reindex accPlacement
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem copy_bank (f x y acc : ℤ → Fin (a+4)) (p px py pa : ℤ) :
    ((DoubleClockReverseCopy.copyBank acc x f pa px p).append
      (MultiplicationInputSplit.single y py)).reindex copyPlacement = bank f x y acc p px py pa := by
  unfold DoubleClockReverseCopy.copyBank MultiplicationInputSplit.single ElementaryMultiplyCore.bank
    Tapes.append Tapes.reindex copyPlacement
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def out (n : ℕ) (x y : List Bool) := DoubleClockReverseCopy.copied
  (putWord (fun _ => (blank : Fin (a+4))) (-(n : ℤ))
    ((BinaryMultiply.horner x.reverse y.reverse).map bitSymbol)) (n-1) n

def output (n : ℕ) (x y : List Bool) : Tapes 4 a := bank
  (putWord (fun _ => blank) 0 ((out (a := a) n x y).map bitSymbol))
  (putWord (fun _ => blank) 0 (x.reverse.map bitSymbol))
  (putWord (fun _ => blank) 0 (y.reverse.map bitSymbol))
  (putWord (fun _ => blank) (-(n : ℤ)) ((BinaryMultiply.horner x.reverse y.reverse).map bitSymbol))
  (2*n) n (-1) (-(n : ℤ)-1)

/-- The complete literal endpoint, including empty equal-length inputs. -/
theorem multiplies {n : ℕ} {x y : List Bool} (hx : x.length = n) (hy : y.length = n) :
    HoareTime (program a) (fun v => v = ElementaryMultiplyCore.input (a := a) x y)
      (fun v => v = output (a := a) n x y) (40*(n^2+n+1)) := by
  let F := MultiplicationInputSplit.source (a := a) x y
  let X := putWord (fun _ => blank) 0 (x.reverse.map (bitSymbol (a := a)))
  let Y := putWord (fun _ => blank) 0 (y.reverse.map (bitSymbol (a := a)))
  let A := putWord (fun _ => blank) (-(n : ℤ)) ((BinaryMultiply.horner x.reverse y.reverse).map (bitSymbol (a := a)))
  let prefWord := x.map (bitSymbol (a := a))
  let suffWord := [separator]++y.map (bitSymbol (a := a))
  let B := putWord (fun _ => blank) 0 prefWord
  have hsource : putWord B n suffWord = F := by
    dsimp [B,F,MultiplicationInputSplit.source,prefWord,suffWord]
    have hp : (n : ℤ) = 0+(x.map (bitSymbol (a := a))).length := by simp [hx]
    rw [hp,putWord_append_forward,List.append_assoc]
    rfl
  have hend : B (n+suffWord.length) = blank := by
    dsimp [B]
    rw [putWord_outside _ _ _ _ (Or.inr (by simp [prefWord,hx]))]
  have hsuffWord : ∀ z ∈ suffWord, z ≠ (blank : Fin (a+4)) := by
    intro z hz
    simp only [suffWord,List.mem_append,List.mem_singleton] at hz
    rcases hz with rfl | hz
    · simp [separator,blank,Fin.ext_iff]
    · exact ReturnOrigin.bits_nonblank y z hz
  have hcore := ElementaryMultiplyCore.runs_equal_length (a := a) hx hy
  simp only [ElementaryMultiplyCore.output,hx,hy] at hcore
  have h1 := hoare_extend_eq (MultiplicationInputSplit.scan_hoare blank B n suffWord hsuffWord hend)
    (MultiplicationInputSplit.bank X Y A 0 (-1) (-(n : ℤ)))
  simp only [MultiplicationInputSplit.oneCfg,Config.tapes] at h1
  rw [source_bank,source_bank,hsource] at h1
  have hlen : suffWord.length = n+1 := by simp [suffWord,hy]
  rw [hlen] at h1
  have h2 := hoare_extend_eq (EraseBack.erase_hoare (a := a) (fun _ => blank) 0 (prefWord++suffWord)
    (by intro z hz; rcases List.mem_append.mp hz with hz|hz
        · exact ReturnOrigin.bits_nonblank x z hz
        · exact hsuffWord z hz) rfl (fun _ _ => rfl))
    (MultiplicationInputSplit.bank X Y A 0 (-1) (-(n : ℤ)))
  simp only [EraseBack.cfg,Config.tapes] at h2
  rw [source_bank,source_bank] at h2
  have hpacked : putWord (fun _ => (blank : Fin (a+4))) 0 (prefWord++suffWord) = F := by
    simp only [F,MultiplicationInputSplit.source,prefWord,suffWord,List.append_assoc]
  have hwhole : (prefWord++suffWord).length = 2*n+1 := by simp [prefWord,hlen,hx]; omega
  rw [hpacked,hwhole] at h2
  have h3 := hoare_place (DoubleClockReverseCopy.doubleSeek_hoare A (fun _ => blank) (-(n : ℤ)) 0
    x.reverse rfl) seekPlacement (MultiplicationInputSplit.pair (fun _ => blank) Y 0 (-1))
  rw [seek_bank,seek_bank] at h3
  simp only [List.length_reverse,hx,zero_add] at h3
  have hpseek : -(n : ℤ)+2*n = n := by ring
  rw [hpseek] at h3
  have h4 := hoare_place (ReturnOrigin.return_hoare (a := a) (x.reverse.map bitSymbol)
    (ReturnOrigin.bits_nonblank _)) ElementaryMultiplyCore.rewindPlacement
    (MultiplicationInputSplit.bank (fun _ => blank) Y A 0 (-1) n)
  simp only [ReturnOrigin.cfg,Config.tapes] at h4
  rw [ElementaryMultiplyCore.rewind_bank,ElementaryMultiplyCore.rewind_bank] at h4
  simp only [List.length_map,List.length_reverse,hx] at h4
  have h5 := hoare_place (MultiplicationInputSplit.shifts .left A n) accPlacement
    (MultiplicationInputSplit.bank (fun _ => blank) X Y 0 0 (-1))
  rw [acc_bank,acc_bank] at h5
  simp only [Move.offset,Int.add_neg_one] at h5
  have h6 := hoare_place (DoubleClockReverseCopy.reverseCopy_hoare A (fun _ => blank) (fun _ => blank)
    (n-1) 0 0 x.reverse rfl) copyPlacement (MultiplicationInputSplit.single Y (-1))
  rw [copy_bank,copy_bank] at h6
  simp only [List.length_reverse,hx,zero_add] at h6
  have hpout : (n : ℤ)-1-2*n = -(n : ℤ)-1 := by ring
  rw [hpout] at h6
  simp only [zero_add,Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat] at h1 h2
  rw [show (n : ℤ)+(n+1) = 2*n+1 by ring] at h1
  have hall := (((((hcore.seq h1).seq h2).seq h3).seq h4).seq h5).seq h6
  apply hall.consequence (fun _ h => h) (fun _ h => h) _
  nlinarith

/-- The original packed input is the complete precondition of the machine. -/
theorem input_start (x y : List Bool) :
    (ElementaryMultiplyCore.input (a := a) x y).start (program a) = Machine.input (program a) x y := by
  apply congrArg₂ (Config.mk (program a).start)
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> simp [ElementaryMultiplyCore.input,MultiplicationInputSplit.input,
      MultiplicationInputSplit.bank,MultiplicationInputSplit.single,Tapes.append,MultiplicationInputSplit.source_wordTape]
    all_goals rfl

/-- Genuine halting and the exact required 2n-bit MSB product on tape zero. -/
theorem runs_correct {n : ℕ} {x y : List Bool} (hx : x.length = n) (hy : y.length = n) :
    ∃ k ≤ 40*(n^2+n+1), ∃ c,
      run (program a) k (Machine.input (program a) x y) = some c ∧
      step (program a) c = none ∧ outputCorrect (program a) n x y c := by
  obtain ⟨k,c,hk,hr,hh,hout⟩ := multiplies (a := a) hx hy _ rfl
  refine ⟨k,hk,c,by simpa only [input_start] using hr,hh,out (a := a) n x y,
    ElementaryMultiplyOutputData.horner_output_length hx hy,
    ElementaryMultiplyOutputData.horner_output_value hx hy,?_⟩
  change c.tapes.tape ⟨0,(program a).tapes_pos⟩ = _
  rw [hout]
  change putWord (fun _ => blank) 0 ((out (a := a) n x y).map bitSymbol) = _
  funext j
  simpa only [sub_zero] using putWord_blank (a := a) 0 j ((out (a := a) n x y).map bitSymbol)

/-- Polynomial fallback contract in the same format as the final assembly. -/
theorem runsWithin : Assembly.RunsWithin (program a) (fun n => ((40*(n^2+n+1) : ℕ) : ℝ)) := by
  intro n _ x y hx hy
  obtain ⟨k,hk,c,hr,hh,hout⟩ := runs_correct (a := a) hx hy
  refine ⟨k,c,hr,hh,hout,?_⟩
  change (k : ℝ) ≤ ((40*(n^2+n+1) : ℕ) : ℝ)
  exact_mod_cast hk

end
end IntegerMultBounds.Machine.ElementaryMultiply
