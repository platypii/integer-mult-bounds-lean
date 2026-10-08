import IntegerMultBounds.Machine.FlatRepeatedControlArray
import IntegerMultBounds.Machine.RadixZeroFill

/-! Exact physical setup for the repeated-control shift. Only B,Q,C,N,width
and the payload pair are present initially. The H field, clocks, metadata
markers, and zero offset are constructed on initially blank workspace. -/
namespace IntegerMultBounds.Machine.RepeatedControlBootstrap
variable {radix : ℕ} [Fact radix.Prime]

def workspace (i : Fin 20) : Bool := decide (i ≠ 5 ∧ i ≠ 7 ∧ i ≠ 10 ∧ i ≠ 11 ∧ i ≠ 17 ∧ i ≠ 19)
def marker (i : Fin 21) : Bool := decide (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 6 ∨ i = 8 ∨ i = 12 ∨ i = 16)

def raw (v : Tapes 20 radix) : Tapes 20 radix :=
  ⟨fun i => if workspace i then 0 else v.head i,
    fun i => if workspace i then (fun _ => blank) else v.tape i⟩

def widthTape (ws : List Bool) : Tapes 1 radix :=
  ⟨fun _ => 1,fun _ => RadixZeroFill.encodedBinary ws⟩

def input (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs cs ns ws : List Bool) : Tapes 21 radix :=
  (raw (FlatRepeatedControlNormalize.bank source dest p q bs qs cs ns [] [])).append (widthTape ws)

def filled (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs cs ns ws : List Bool) (b : ℕ) : Tapes 21 radix :=
  let v := input source dest p q bs qs cs ns ws
  ⟨fun i => if i = 15 ∨ i = 18 then 1 else v.head i,
    fun i => if i = 15 then RadixZeroFill.radixZeros (Fact.out : radix.Prime).two_le b
      else if i = 18 then RadixZeroFill.radixEmpty else v.tape i⟩

def output (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs cs ns ws : List Bool) (b : ℕ) : Tapes 21 radix :=
  (FlatRepeatedControlNormalize.bank source dest p q bs qs cs ns []
    (RadixCounterData.zeros (Fact.out : radix.Prime).two_le b)).append (widthTape ws)

def placement : Fin (3+18) ≃ Fin 21 where
  toFun := ![15,18,20,3,4,5,6,7,8,9,10,11,12,13,14,0,16,17,1,19,2]
  invFun := ![15,18,20,3,4,5,6,7,8,9,10,11,12,13,14,0,16,17,1,19,2]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

omit [Fact radix.Prime] in
private theorem active_input (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs cs ns ws : List Bool) :
    Placement.active placement (input (radix := radix) source dest p q bs qs cs ns ws) = RadixZeroFill.input ws := by
  unfold Placement.active placement input raw workspace widthTape
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem active_filled (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs cs ns ws : List Bool) (b : ℕ) :
    Placement.active placement (filled (radix := radix) source dest p q bs qs cs ns ws b) =
      RadixZeroFill.output (Fact.out : radix.Prime).two_le ws b := by
  unfold Placement.active placement filled input raw workspace widthTape
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem extra_filled (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs cs ns ws : List Bool) (b : ℕ) :
    Placement.extra placement (input (radix := radix) source dest p q bs qs cs ns ws) =
      Placement.extra placement (filled (radix := radix) source dest p q bs qs cs ns ws b) := by
  unfold Placement.extra placement filled
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def fillProgram : Program 21 23 radix := Placement.placed (RadixZeroFill.program (Fact.out : radix.Prime).two_le) placement

theorem fill_hoare (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs cs ns ws : List Bool) (b : ℕ)
    (hw : Counter.value ws = b) (cw : GrowingCounterData.Canonical ws) :
    HoareTime (fillProgram (radix := radix)) (fun v => v = input source dest p q bs qs cs ns ws)
      (fun v => v = filled source dest p q bs qs cs ns ws b) (15*b+28) := by
  have hh := RadixZeroFill.fill_zeros_linear (Fact.out : radix.Prime).two_le ws b hw cw
  apply (Placement.hoare_at hh placement (input (radix := radix) source dest p q bs qs cs ns ws)
    (active_input _ _ _ _ _ _ _ _ _)).consequence (fun _ h => h) _ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  rw [Placement.replace,extra_filled,← active_filled]
  exact Placement.view _ _

def marked (v : Tapes 21 radix) : Tapes 21 radix :=
  ⟨fun i => v.head i+if marker i || decide (i = 0) then 1 else 0,
    fun i => if marker i then Function.update (v.tape i) (v.head i) separator else v.tape i⟩

def markerProgram : Program 21 2 radix where
  tapes_pos := by decide
  start := 0
  transition := fun st symbols => if st = 0 then some (1,fun i =>
    if marker i then (separator,.right) else if i = 0 then (symbols i,.right) else (symbols i,.stay)) else none

omit [Fact radix.Prime] in
private theorem marker_hoare (v : Tapes 21 radix) :
    HoareTime markerProgram (fun x => x = v) (fun x => x = marked v) 1 := by
  intro x hx
  subst x
  refine ⟨1,⟨1,(marked v).head,(marked v).tape⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,markerProgram,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i
      cases hm : marker i <;> by_cases hi : i = 0 <;> simp [hm,hi,marked,Move.offset]
    · funext i z
      by_cases hi : i = 0
      · subst i; simp [marker,marked]; intro hz; rw [hz]
      · cases hm : marker i <;> by_cases hz : z = v.head i <;> simp [hm,hi,hz,marked]
  · simp [step,markerProgram]

private def frame (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs cs ns : List Bool) (xs : List (Fin radix)) : Tapes 20 radix :=
  ⟨![1,1,1,1,1,1,1,1,1,0,p,q,1,0,0,1,1,1,1,1],
    ![fun _ => blank,RadixZeroFill.radixEmpty,RadixZeroFill.radixEmpty,RadixZeroFill.radixEmpty,
      RadixZeroFill.radixEmpty,RadixZeroFill.encodedBinary bs,RadixZeroFill.radixEmpty,
      RadixZeroFill.encodedBinary qs,RadixZeroFill.radixEmpty,fun _ => blank,
      FlatRepeatedControlNormalize.encoded source,FlatRepeatedControlNormalize.encoded dest,
      RadixZeroFill.radixEmpty,fun _ => blank,fun _ => blank,RadixRationalBinary.source xs,
      RadixZeroFill.radixEmpty,CountedLoopReuseAlphabet.binary cs,
      RadixZeroFill.radixEmpty,CountedLoopReuseAlphabet.binary ns]⟩

omit [Fact radix.Prime] in
private theorem bank_frame (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs cs ns : List Bool) (xs : List (Fin radix)) :
    FlatRepeatedControlNormalize.bank source dest p q bs qs cs ns [] xs = frame source dest p q bs qs cs ns xs := by
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> rfl
  · have he : (fun z => (RadixToBinary.binaryEncoding (q := radix)).encode (CountedCopyReuse.empty z)) =
        RadixZeroFill.radixEmpty := by
      funext z
      by_cases hz : z = 0 <;> simp [hz,RadixToBinary.binaryEncoding,CountedCopyReuse.empty,
        RadixZeroFill.radixEmpty,blank,separator]
    funext i z
    fin_cases i <;> first | rfl | exact congrFun he z

private theorem marked_filled (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs cs ns ws : List Bool) (b : ℕ) :
    marked (filled (radix := radix) source dest p q bs qs cs ns ws b) = output (radix := radix) source dest p q bs qs cs ns ws b := by
  unfold marked filled output input
  rw [bank_frame,bank_frame]
  unfold raw frame marker workspace
  apply congrArg₂ Tapes.mk
  · funext i
    change Fin (20+1) at i
    induction i using Fin.addCases with
    | left i =>
      simp only [Tapes.append,Fin.addCases_left]
      fin_cases i <;> simp
    | right i =>
      simp only [Tapes.append,Fin.addCases_right]
      fin_cases i; simp
  · funext i z
    change Fin (20+1) at i
    induction i using Fin.addCases with
    | left i =>
      simp only [Tapes.append,Fin.addCases_left]
      fin_cases i <;> simp [Function.update_apply,RadixZeroFill.radixEmpty,
        RadixZeroFill.radixZeros,RadixRationalBinary.source,MarkedWordCleanup.marked,RadixCounterData.zeros,List.map_replicate]
      rfl
    | right i =>
      simp only [Tapes.append,Fin.addCases_right]
      fin_cases i; simp

def program := seq (fillProgram (radix := radix)) markerProgram

theorem construct_hoare (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs cs ns ws : List Bool) (b : ℕ)
    (hw : Counter.value ws = b) (cw : GrowingCounterData.Canonical ws) :
    HoareTime program (fun v => v = input source dest p q bs qs cs ns ws)
      (fun v => v = output (radix := radix) source dest p q bs qs cs ns ws b) (15*b+30) := by
  have hm := marker_hoare (filled (radix := radix) source dest p q bs qs cs ns ws b)
  rw [marked_filled] at hm
  exact ((fill_hoare source dest p q bs qs cs ns ws b hw cw).seq hm).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.RepeatedControlBootstrap
