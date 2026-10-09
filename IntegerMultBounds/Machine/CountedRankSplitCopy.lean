import IntegerMultBounds.Machine.SharedBank
import IntegerMultBounds.Machine.WordMoves
import IntegerMultBounds.Machine.CountedLoopReuseAlphabet
import IntegerMultBounds.Machine.ArbitraryWidthZeroHeaderShared
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList

/-! Fixed zero-filling copy driven by a preserved binary count. Its private
clock sentinel is physically initialized and erased, including count zero. -/
namespace IntegerMultBounds.Machine.CountedRankSplitCopy
noncomputable section
variable {a : ℕ}

def payload (f g : ℤ → Fin (a+4)) (p q : ℤ) : Tapes 2 a := (CopyCells.cfg f g p q 0).tapes
def header (bs : List Bool) : Tapes 1 a := ⟨fun _ => 1,fun _ => RadixZeroFill.encodedBinary bs⟩
def bank (f g : ℤ → Fin (a+4)) (p q : ℤ) (bs : List Bool) :=
  ((payload f g p q).append (SharedBank.empty 1 a)).append (header bs)
def prepared (f g : ℤ → Fin (a+4)) (p q : ℤ) (bs : List Bool) :=
  CountedLoopReuseAlphabet.bank (payload f g p q) CountedLoopReuseAlphabet.empty
    (CountedLoopReuseAlphabet.binary bs) 1 1

def setup := extend (ArbitraryWidthZeroHeaderShared.program (a := a) (t := 2)) 1
def loopProgram := CountedLoopReuseAlphabet.program (CopyCells.cell (a := a))
def cleanup := BinaryDescriptorCleanupList.oneProgram (a := a) (2 : Fin 4)
def program := seq (seq (setup (a := a)) loopProgram) cleanup

theorem cells_add (f : ℤ → Fin (a+4)) (p : ℤ) (n m : ℕ) :
    CopyCells.cells f p (n+m) = CopyCells.cells f p n ++ CopyCells.cells f (p+n) m := by
  induction n generalizing p with
  | zero => simp [CopyCells.cells]
  | succ n ih =>
    rw [Nat.succ_add,CopyCells.cells,CopyCells.cells,ih]
    simp only [List.cons_append,Nat.cast_add,Nat.cast_one]
    simp [add_comm,add_left_comm]

theorem cells_snoc (f : ℤ → Fin (a+4)) (p : ℤ) (n : ℕ) :
    CopyCells.cells f p (n+1) = CopyCells.cells f p n ++ [CopyCells.zeroFill (f (p+n))] := by
  rw [cells_add]
  rfl

theorem copied_step (f g : ℤ → Fin (a+4)) (p q : ℤ) (n : ℕ) :
    Function.update (putWord g q (CopyCells.cells f p n)) (q+n) (CopyCells.zeroFill (f (p+n))) =
      putWord g q (CopyCells.cells f p (n+1)) := by
  rw [cells_snoc]
  have h := putWord_append_forward g q (CopyCells.cells f p n) [CopyCells.zeroFill (f (p+n))]
  simpa only [CopyCells.cells_length,putWord] using h

theorem loop_hoare (f g : ℤ → Fin (a+4)) (p q : ℤ) (bs : List Bool)
    (n : ℕ) (hv : Counter.value bs = n) :
    HoareTime (loopProgram (a := a)) (fun w => w = prepared f g p q bs)
      (fun w => w = prepared f (putWord g q (CopyCells.cells f p n)) (p+n) (q+n) bs)
      (7*n+7*bs.length+16) := by
  have h := CountedLoopReuseAlphabet.loop_hoare (CopyCells.cell (a := a)) bs n
    (fun i => payload f (putWord g q (CopyCells.cells f p i)) (p+i) (q+i)) (fun _ => 1) hv (by
      intro i _
      have hcell := CopyCells.cell_hoare f (putWord g q (CopyCells.cells f p i)) (p+i) (q+i)
      rw [copied_step] at hcell
      have hp : p+(i : ℤ)+1 = p+((i+1 : ℕ) : ℤ) := by push_cast; ring
      have hq : q+(i : ℤ)+1 = q+((i+1 : ℕ) : ℤ) := by push_cast; ring
      simpa only [payload,hp,hq] using hcell)
  apply h.consequence ?_ (fun _ h => h) ?_
  · intro w hw
    simpa only [prepared,CopyCells.cells,putWord,Nat.cast_zero,add_zero] using hw
  · simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one]
    omega

private theorem encoded_binary (bs : List Bool) :
    RadixZeroFill.encodedBinary (q := a) bs = CountedLoopReuseAlphabet.binary bs :=
  CountedLoopReuseAlphabet.encoding_binary bs

theorem sets_up (f g : ℤ → Fin (a+4)) (p q : ℤ) (bs : List Bool) :
    HoareTime (setup (a := a)) (fun w => w = bank f g p q bs)
      (fun w => w = prepared f g p q bs) 6 := by
  have h := hoare_extend_eq (ArbitraryWidthZeroHeaderShared.constructs (payload f g p q)) (header bs)
  apply h.consequence (fun _ h => h) ?_ le_rfl
  intro w hw
  rw [hw]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact encoded_binary bs

theorem cleans (f g : ℤ → Fin (a+4)) (p q : ℤ) (bs : List Bool) :
    HoareTime (cleanup (a := a)) (fun w => w = prepared f g p q bs)
      (fun w => w = bank f g p q bs) 4 := by
  have h := BinaryDescriptorCleanupList.one_hoare (2 : Fin 4) (prepared f g p q bs) [] (by rfl) rfl
  apply h.consequence (fun _ h => h) ?_ le_rfl
  rintro w rfl
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact (encoded_binary bs).symm

/-- Literal zero-filled cell copying, retaining source and count and returning
the entire private clock tape blank at origin. -/
theorem copies (f g : ℤ → Fin (a+4)) (p q : ℤ) (bs : List Bool)
    (n : ℕ) (hv : Counter.value bs = n) :
    HoareTime (program (a := a)) (fun w => w = bank f g p q bs)
      (fun w => w = bank f (putWord g q (CopyCells.cells f p n)) (p+n) (q+n) bs)
      (7*n+7*bs.length+28) := by
  have h := ((sets_up f g p q bs).seq (loop_hoare f g p q bs n hv)).seq
    (cleans f (putWord g q (CopyCells.cells f p n)) (p+n) (q+n) bs)
  exact h.consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.CountedRankSplitCopy
