import IntegerMultBounds.Machine.RadixZeroFill
import IntegerMultBounds.Machine.MarkedWordCleanup

/-! A physical radix power word, constructed from the supplied binary exponent.
The fixed radix lives in finite control; the exponent is read on tape. -/
namespace IntegerMultBounds.Machine.RadixPowerWord

open RadixDigits MarkedWordCleanup
variable {q : ℕ} (hq : 2 ≤ q)

def digits (b : ℕ) : List (Fin q) :=
  List.replicate b (RadixCounterData.zeroDigit hq) ++ [⟨1,by omega⟩]

@[simp] theorem digits_length (b : ℕ) : (digits hq b).length = b+1 := by simp [digits]

@[simp] theorem digits_value (b : ℕ) : value (digits hq b) = q^b := by
  induction b with
  | zero => simp [digits,value]
  | succ b ih =>
    change value (RadixCounterData.zeroDigit hq :: digits hq b) = q^(b+1)
    simp only [value,RadixCounterData.zeroDigit,zero_add,ih,pow_succ]
    exact Nat.mul_comm _ _

private def cfg (f : ℤ → Fin (q+4)) (p : ℤ) (s : Fin 3) : Config 1 3 q :=
  ⟨s,fun _ => p,fun _ => f⟩

/-- Scan the zero field, append its high one, return, and erase its marker. -/
def appendProgram : Program 1 3 q where
  tapes_pos := by decide
  start := 0
  transition := fun s sy =>
    if s = 0 then
      if sy 0 = blank then some (1,fun _ => (digitSymbol (⟨1,by omega⟩ : Fin q),.left))
      else some (0,fun i => (sy i,.right))
    else if s = 1 then
      if sy 0 = separator then some (2,fun _ => (blank,.stay))
      else some (1,fun i => (sy i,.left))
    else none

private theorem forward (b n : ℕ) (hn : n ≤ b) :
    run (appendProgram hq) n (cfg (RadixZeroFill.radixZeros hq b) 1 0) =
      some (cfg (RadixZeroFill.radixZeros hq b) (1+n) 0) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    rw [run_add,ih (by omega)]
    simp only [Option.bind_some,run_one]
    have hs : RadixZeroFill.radixZeros hq b (1+n) ≠ blank := by
      rw [RadixZeroFill.radixZeros,WordSegments.get _ _ _ n (by simp; omega)]
      simp [digitSymbol,blank]
    simp only [step,appendProgram,cfg,ite_true,hs,ite_false,Move.offset]
    congr 1
    congr 1
    funext i z
    by_cases hz : z = 1+n <;> simp [hz]

private theorem backward (f : ℤ → Fin (q+4)) (p : ℤ) (n : ℕ)
    (hn : ∀ j : ℕ, j < n → f (p-j) ≠ separator) :
    run (appendProgram hq) n (cfg f p 1) = some (cfg f (p-n) 1) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    rw [run_add,ih (fun j hj => hn j (by omega))]
    simp only [Option.bind_some,run_one,step,appendProgram,cfg,
      show (1 : Fin 3) ≠ 0 by decide,ite_false,ite_true,hn n (by omega)]
    congr 1
    congr 1
    · funext i; simp [Move.offset]; omega
    · funext i z
      by_cases hz : z = p-n <;> simp [hz]

theorem append_hoare (b : ℕ) :
    HoareTime (appendProgram hq)
      (fun v => v = one (RadixZeroFill.radixZeros hq b) 1)
      (fun v => v = one (word ((digits hq b).map digitSymbol)) 0) (2*b+2) := by
  let xs := (digits hq b).map digitSymbol
  have he : Function.update (RadixZeroFill.radixZeros hq b) (1+b)
      (digitSymbol (⟨1,by omega⟩ : Fin q)) = marked xs := by
    change Function.update (putWord empty 1 _) _ _ = putWord empty 1 _
    simpa [xs,digits,List.map_append,List.map_replicate,putWord] using
      putWord_append_forward (empty (a := q)) 1
        (List.replicate b (digitSymbol (RadixCounterData.zeroDigit hq)))
        [digitSymbol (⟨1,by omega⟩ : Fin q)]
  have hb : RadixZeroFill.radixZeros hq b (1+b) = blank := by
    rw [RadixZeroFill.radixZeros,putWord_outside _ _ _ _ (Or.inr (by simp))]
    simp [RadixZeroFill.radixEmpty,show (1:ℤ)+b ≠ 0 by omega]
  have hs : step (appendProgram hq) (cfg (RadixZeroFill.radixZeros hq b) (1+b) 0) =
      some (cfg (marked xs) b 1) := by
    simp only [step,appendProgram,cfg,ite_true,hb,Move.offset]
    congr 1
    congr 1
    · funext i; simp
    · funext i z
      have hh := congrFun he z
      simp only [Function.update_apply] at hh
      by_cases hz : z = 1+b
      · simp only [hz,ite_true] at hh ⊢
        exact hh
      · simp only [hz,ite_false] at hh ⊢
        exact hh
  have hr := backward hq (marked xs) b b (by
    intro j hj
    have hz : (b:ℤ)-j = 1+((b-j-1 : ℕ) : ℤ) := by omega
    rw [marked,hz,WordSegments.get _ _ _ (b-j-1) (by simp [xs]; omega)]
    have hm : xs[b-j-1]'(by simp [xs]; omega) ∈ xs := List.getElem_mem _
    obtain ⟨d,_,hd⟩ := List.mem_map.mp hm
    rw [← hd]
    simp [digitSymbol,separator])
  simp only [sub_self] at hr
  have hm : marked xs 0 = separator := by
    rw [marked,putWord_outside _ _ _ _ (Or.inl (by omega))]
    rfl
  have hu : Function.update (marked xs) 0 blank = word xs := by
    rw [← mark_word,Function.update_idem]
    exact Function.update_eq_self_iff.mpr (by
      rw [word,putWord_outside _ _ _ _ (Or.inl (by omega))])
  rintro v rfl
  refine ⟨2*b+2,cfg (word xs) 0 2,le_rfl,?_,?_,rfl⟩
  · rw [show 2*b+2 = b+1+b+1 by omega,run_add,run_add,run_add]
    change (((run (appendProgram hq) b (cfg (RadixZeroFill.radixZeros hq b) 1 0)).bind _).bind _).bind _ = _
    rw [forward hq b b le_rfl]
    simp only [Option.bind_some,run_one]
    rw [hs,Option.bind_some,hr]
    simp only [Option.bind_some,step,appendProgram,cfg,
      show (1 : Fin 3) ≠ 0 by decide,ite_false,ite_true,hm,Move.offset,add_zero]
    congr 1
    congr 1
    funext i z
    simpa [Function.update_apply] using congrFun hu z
  · simp [step,appendProgram,cfg]


def bank (bs : List Bool) (b : ℕ) (clock : ℤ → Fin (q+4)) (r : ℤ) : Tapes 3 q :=
  ⟨![0,r,1],![word ((digits hq b).map digitSymbol),clock,RadixZeroFill.encodedBinary bs]⟩

/-- Only the exponent descriptor is supplied; both writable tapes are blank. -/
def input (bs : List Bool) : Tapes 3 q := RadixZeroFill.input bs

def output (bs : List Bool) (b : ℕ) : Tapes 3 q := bank hq bs b (fun _ => blank) 0

private def cleanClock : Program 3 3 q where
  tapes_pos := by decide
  start := 0
  transition := fun s sy =>
    if s = 0 then some (1,fun i => (sy i,if i = 1 then .left else .stay))
    else if s = 1 then some (2,fun i => (if i = 1 then blank else sy i,.stay))
    else none

private theorem cleanClock_hoare (bs : List Bool) (b : ℕ) :
    HoareTime (cleanClock (q := q)) (fun v => v = bank hq bs b empty 1)
      (fun v => v = output hq bs b) 2 := by
  let middle := bank hq bs b empty 0
  have hs : step cleanClock ((bank hq bs b empty 1).start cleanClock) =
      some (⟨1,middle.head,middle.tape⟩ : Config 3 3 q) := by
    simp only [step,cleanClock,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i; fin_cases i <;> rfl
    · funext i z
      by_cases hz : z = (bank hq bs b empty 1).head i <;> simp_all [middle,bank]
  rintro v rfl
  refine ⟨2,⟨2,(output hq bs b).head,(output hq bs b).tape⟩,le_rfl,?_,?_,rfl⟩
  · rw [run_add cleanClock 1 1,run_one,hs]
    simp only [Option.bind_some,run_one,step,cleanClock,
      show (1 : Fin 3) ≠ 0 by decide,ite_false,ite_true]
    congr 1
    congr 1
    · funext i; fin_cases i <;> rfl
    · funext i z
      fin_cases i <;> simp [middle,output,bank,empty] <;> aesop
  · simp [step,cleanClock]

/-- One fixed machine writes the unmarked radix expansion of q^b. -/
def program : Program 3 29 q :=
  seq (seq (RadixZeroFill.program hq) (extend (appendProgram hq) 2)) cleanClock

theorem construct_hoare (bs : List Bool) (b : ℕ) (hb : Counter.value bs = b) :
    HoareTime (program hq) (fun v => v = input bs) (fun v => v = output hq bs b)
      (10*b+7*bs.length+27) := by
  let frame : Tapes 2 q := ⟨fun _ => 1,![empty,RadixZeroFill.encodedBinary bs]⟩
  have ha : HoareTime (extend (appendProgram hq) 2)
      (fun v => v = RadixZeroFill.output hq bs b)
      (fun v => v = bank hq bs b empty 1) (2*b+2) := by
    apply ((append_hoare hq b).extend frame).consequence _ _ le_rfl
    · intro v hv
      refine ⟨_,rfl,?_⟩
      rw [hv]
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
    · rintro v ⟨w,rfl,rfl⟩
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  exact (((RadixZeroFill.fill_zeros hq bs b hb).seq ha).seq
    (cleanClock_hoare hq bs b)).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem construct_hoare_linear (bs : List Bool) (b : ℕ) (hb : Counter.value bs = b)
    (hc : GrowingCounterData.Canonical bs) :
    HoareTime (program hq) (fun v => v = input bs) (fun v => v = output hq bs b) (17*b+34) := by
  have hw := GrowingCounterData.canonical_width bs hc
  have hl := Nat.log2_le_self b
  rw [hb] at hw
  exact (construct_hoare hq bs b hb).consequence (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.RadixPowerWord
