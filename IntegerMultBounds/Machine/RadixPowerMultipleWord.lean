import IntegerMultBounds.Machine.RadixPowerWord
import IntegerMultBounds.Machine.CountedLoopReuseAlphabet

/-! Fixed-many passes over one immutable binary exponent append all radix zeroes.
No copies of the exponent and no multiplication subroutine are supplied. -/
namespace IntegerMultBounds.Machine.RadixPowerMultipleWord

open RadixDigits MarkedWordCleanup
variable {q : ℕ} (hq : 2 ≤ q)

private def field (n : ℕ) : Tapes 1 q := one (RadixZeroFill.radixZeros hq n) (1+n)

private def writeProgram : Program 1 2 q where
  tapes_pos := by decide
  start := 0
  transition := fun s _ => if s = 0 then
    some (1,fun _ => (digitSymbol (RadixCounterData.zeroDigit hq),.right)) else none

private theorem write_hoare (n : ℕ) :
    HoareTime (writeProgram hq) (fun v => v = field hq n) (fun v => v = field hq (n+1)) 1 := by
  have he : Function.update (RadixZeroFill.radixZeros hq n) (1+n)
      (digitSymbol (RadixCounterData.zeroDigit hq)) = RadixZeroFill.radixZeros hq (n+1) := by
    simpa [RadixZeroFill.radixZeros,List.replicate_add,putWord] using
      putWord_append_forward (RadixZeroFill.radixEmpty (q := q)) 1
        (List.replicate n (digitSymbol (RadixCounterData.zeroDigit hq)))
        [digitSymbol (RadixCounterData.zeroDigit hq)]
  rintro v rfl
  refine ⟨1,⟨1,(field hq (n+1)).head,(field hq (n+1)).tape⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,writeProgram,Tapes.start,ite_true,field,one,Move.offset]
    congr 1
    congr 1
    funext i z
    simpa [Function.update_apply] using congrFun he z
  · simp [step,writeProgram]

/-- Growing radix field and the same two reusable control tapes. -/
def bank (bs : List Bool) (n : ℕ) : Tapes 3 q :=
  CountedLoopReuseAlphabet.bank (field hq n) CountedLoopReuseAlphabet.empty
    (CountedLoopReuseAlphabet.binary bs) 1 1

private theorem binary_eq (bs : List Bool) :
    CountedLoopReuseAlphabet.binary (a := q) bs = RadixZeroFill.encodedBinary bs := by
  rw [← CountedLoopReuseAlphabet.encoding_binary]
  rfl

private def loopProgram : Program 3 18 q := CountedLoopReuseAlphabet.program (writeProgram hq)

private theorem loop_hoare (bs : List Bool) (b n : ℕ) (hb : Counter.value bs = b) :
    HoareTime (loopProgram hq) (fun v => v = bank hq bs n) (fun v => v = bank hq bs (n+b))
      (7*b+7*bs.length+16) := by
  have hh := CountedLoopReuseAlphabet.loop_hoare (writeProgram hq) bs b
    (fun i => field hq (n+i)) (fun _ => 1) hb (fun i _ => by
      simpa only [Nat.add_assoc] using write_hoare hq (n+i))
  apply hh.consequence (fun _ h => h) (fun _ h => h) _
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one]
  omega

private def haltProgram : Program 3 1 q where
  tapes_pos := by decide
  start := 0
  transition := fun _ _ => none

def loopStates : ℕ → ℕ
  | 0 => 1
  | k+1 => loopStates k+18

theorem loopStates_eq (k : ℕ) : loopStates k = 1+18*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [loopStates,ih,Nat.mul_add,Nat.mul_one]; omega

/-- k is a compile-time constant; each pass reads the actual same b tape. -/
def loops : (k : ℕ) → Program 3 (loopStates k) q
  | 0 => haltProgram
  | k+1 => seq (loops k) (loopProgram hq)

private theorem loops_hoare (k : ℕ) (bs : List Bool) (b n : ℕ) (hb : Counter.value bs = b) :
    HoareTime (loops hq k) (fun v => v = bank hq bs n) (fun v => v = bank hq bs (n+k*b))
      (k*(7*b+7*bs.length+17)) := by
  induction k with
  | zero =>
    rintro v rfl
    exact ⟨0,(bank hq bs n).start haltProgram,by omega,rfl,rfl,by simp [Tapes.start,Config.tapes]⟩
  | succ k ih =>
    have hh := ih.seq (loop_hoare hq bs b (n+k*b) hb)
    apply hh.consequence (fun _ h => h) (fun _ h => by simpa [Nat.add_mul,Nat.add_assoc] using h)
    simp only [Nat.add_mul,Nat.one_mul]
    omega

private def initializeProgram : Program 3 2 q where
  tapes_pos := by decide
  start := 0
  transition := fun s sy => if s = 0 then
    some (1,fun i => if i = 2 then (sy i,.stay) else (separator,.right)) else none

def input (bs : List Bool) : Tapes 3 q := RadixPowerWord.input bs

private theorem initialize_hoare (bs : List Bool) :
    HoareTime (initializeProgram (q := q)) (fun v => v = input bs) (fun v => v = bank hq bs 0) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,(bank hq bs 0).head,(bank hq bs 0).tape⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,initializeProgram,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i; fin_cases i <;> rfl
    · funext i z
      fin_cases i
      · change (if z = 0 then separator else blank) = RadixZeroFill.radixEmpty z
        rfl
      · change (if z = 0 then separator else blank) = CountedLoopReuseAlphabet.empty z
        rfl
      · change (if z = 1 then RadixZeroFill.encodedBinary bs 1 else
          RadixZeroFill.encodedBinary bs z) = CountedLoopReuseAlphabet.binary bs z
        rw [binary_eq]
        by_cases hz : z = 1 <;> simp [hz]
  · simp [step,initializeProgram]

private def rewound (bs : List Bool) (n : ℕ) : Tapes 3 q :=
  CountedLoopReuseAlphabet.bank (one (RadixZeroFill.radixZeros hq n) 0)
    CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary bs) 1 1

private theorem rewind_hoare (bs : List Bool) (n : ℕ) :
    HoareTime (extend (Rewind.program (separator : Fin (q+4))) 2)
      (fun v => v = bank hq bs n) (fun v => v = rewound hq bs n) (n+1) := by
  have hh := Rewind.rewind_hoare (separator : Fin (q+4)) (RadixZeroFill.radixZeros hq n)
    (1+n) (n+1) (by
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        rw [Nat.cast_zero,sub_zero,RadixZeroFill.radixZeros,putWord_outside _ _ _ _ (Or.inr (by simp))]
        simp [RadixZeroFill.radixEmpty,show (1:ℤ)+n ≠ 0 by omega,blank,separator]
      · have hz : (1:ℤ)+n-j = 1+((n-j : ℕ) : ℤ) := by omega
        rw [RadixZeroFill.radixZeros,hz,WordSegments.get _ _ _ (n-j) (by simp; omega)]
        simp [digitSymbol,separator]) (by
      have hz : (1:ℤ)+n-(n+1 : ℕ) = 0 := by omega
      rw [hz,RadixZeroFill.radixZeros,putWord_outside _ _ _ _ (Or.inl (by omega))]
      rfl)
  have hh' : HoareTime (Rewind.program (separator : Fin (q+4)))
      (fun v => v = field hq n) (fun v => v = one (RadixZeroFill.radixZeros hq n) 0) (n+1) := by
    have hz : (1:ℤ)+n-(n+1 : ℕ) = 0 := by omega
    simpa only [hz,Rewind.cfg,Config.tapes,field,one] using hh
  apply (hh'.extend (CountedLoopReuseAlphabet.controls CountedLoopReuseAlphabet.empty
    (CountedLoopReuseAlphabet.binary bs) 1 1)).consequence _ _ le_rfl
  · intro v hv; exact ⟨_,rfl,hv⟩
  · rintro v ⟨w,rfl,rfl⟩; rfl

private def restored (bs : List Bool) (n : ℕ) : Tapes 3 q :=
  ⟨![1,0,1],![RadixZeroFill.radixZeros hq n,fun _ => blank,RadixZeroFill.encodedBinary bs]⟩

private def restoreProgram : Program 3 3 q where
  tapes_pos := by decide
  start := 0
  transition := fun s sy =>
    if s = 0 then some (1,fun i => (sy i,if i = 0 then .right else if i = 1 then .left else .stay))
    else if s = 1 then some (2,fun i => (if i = 1 then blank else sy i,.stay))
    else none

private theorem restore_hoare (bs : List Bool) (n : ℕ) :
    HoareTime (restoreProgram (q := q)) (fun v => v = rewound hq bs n)
      (fun v => v = restored hq bs n) 2 := by
  let middle : Tapes 3 q := ⟨![1,0,1],(rewound hq bs n).tape⟩
  have hs : step restoreProgram ((rewound hq bs n).start restoreProgram) =
      some (⟨1,middle.head,middle.tape⟩ : Config 3 3 q) := by
    simp only [step,restoreProgram,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i; fin_cases i <;> rfl
    · funext i z
      by_cases hz : z = (rewound hq bs n).head i <;> simp [hz,middle]
  rintro v rfl
  refine ⟨2,⟨2,(restored hq bs n).head,(restored hq bs n).tape⟩,le_rfl,?_,?_,rfl⟩
  · rw [run_add restoreProgram 1 1,run_one,hs]
    simp only [Option.bind_some,run_one,step,restoreProgram,
      show (1 : Fin 3) ≠ 0 by decide,ite_false,ite_true]
    congr 1
    congr 1
    · funext i; fin_cases i <;> rfl
    · funext i z
      fin_cases i
      · change (if z = 1 then RadixZeroFill.radixZeros hq n 1 else RadixZeroFill.radixZeros hq n z) = _
        by_cases hz : z = 1 <;> simp [hz,restored]
      · change (if z = 0 then blank else CountedLoopReuseAlphabet.empty z) = blank
        by_cases hz : z = 0 <;> simp [hz,CountedLoopReuseAlphabet.empty]
      · change (if z = 1 then CountedLoopReuseAlphabet.binary bs 1 else CountedLoopReuseAlphabet.binary bs z) = _
        rw [binary_eq]
        by_cases hz : z = 1 <;> simp [hz,restored]

  · simp [step,restoreProgram]

/-- Unmarked radix power, original exponent, and a completely blank clock. -/
def output (bs : List Bool) (k b : ℕ) : Tapes 3 q := RadixPowerWord.output hq bs (k*b)

def program (k : ℕ) : Program 3 (2+loopStates k+1+3+3) q :=
  seq (seq (seq (seq initializeProgram (loops hq k)) (extend (Rewind.program separator) 2))
      restoreProgram) (extend (RadixPowerWord.appendProgram hq) 2)

theorem construct_hoare (k : ℕ) (bs : List Bool) (b : ℕ) (hb : Counter.value bs = b) :
    HoareTime (program hq k) (fun v => v = input bs) (fun v => v = output hq bs k b)
      (10*(k*b)+7*k*bs.length+17*k+10) := by
  have hl := loops_hoare hq k bs b 0 hb
  simp only [Nat.zero_add] at hl
  let frame : Tapes 2 q := ⟨![0,1],![fun _ => blank,RadixZeroFill.encodedBinary bs]⟩
  have ha : HoareTime (extend (RadixPowerWord.appendProgram hq) 2)
      (fun v => v = restored hq bs (k*b)) (fun v => v = output hq bs k b) (2*(k*b)+2) := by
    apply ((RadixPowerWord.append_hoare hq (k*b)).extend frame).consequence _ _ le_rfl
    · intro v hv
      refine ⟨_,rfl,?_⟩
      rw [hv]
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
    · rintro v ⟨w,rfl,rfl⟩
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hh := ((((initialize_hoare hq bs).seq hl).seq (rewind_hoare hq bs (k*b))).seq
    (restore_hoare hq bs (k*b))).seq ha
  apply hh.consequence (fun _ h => h) (fun _ h => h)
  simp only [Nat.mul_add]
  nlinarith

end IntegerMultBounds.Machine.RadixPowerMultipleWord
