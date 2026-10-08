import IntegerMultBounds.Machine.MarkedRadixRefresh
import IntegerMultBounds.Machine.RadixZeroFill

/-! Copy a binary descriptor from a preserved source to a wholly blank tape,
installing its sentinel and restoring both heads. Every scan is charged. -/
namespace IntegerMultBounds.Machine.BinaryDescriptorCopy
open MarkedWordCleanup (marked empty one)

def source (xs : List Bool) : ℤ → Fin 4 := marked (xs.map bitSymbol)
def bank (xs ys : List Bool) : Tapes 2 0 := Copy.tapes (source xs) (source ys) 1 1
def input (xs : List Bool) : Tapes 2 0 := Copy.tapes (source xs) (fun _ => blank) 1 0

private theorem nonblank (xs : List Bool) : ∀ x ∈ xs.map bitSymbol, x ≠ (blank : Fin 4) := by
  intro x hx
  obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx
  cases y <;> decide

private def initProgram : Program 2 2 0 where
  tapes_pos := by decide
  start := 0
  transition := fun s sy => if s = 0 then
    some (1,fun i => if i = 0 then (sy i,.stay) else (separator,.right)) else none

private theorem init_hoare (xs : List Bool) :
    HoareTime initProgram (fun v => v = input xs) (fun v => v = bank xs []) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,(bank xs []).head,(bank xs []).tape⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,initProgram,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i; fin_cases i <;> rfl
    · funext i z
      fin_cases i
      · change (if z = 1 then source xs 1 else source xs z) = source xs z
        by_cases hz : z = 1 <;> simp [hz]
      · rfl
  · simp [step,initProgram]

private theorem copy_body_hoare (xs : List Bool) :
    HoareTime (Copy.program blank false) (fun v => v = bank xs [])
      (fun v => v = Copy.tapes (source xs) (source xs) (1+xs.length) (1+xs.length)) xs.length := by
  have hh := Copy.copy_hoare (blank : Fin 4) false empty empty 1 1 (xs.map bitSymbol) (nonblank xs)
    (by simp only [empty,List.length_map]; rw [ite_eq_right (by omega)])
  have hr : (Copy.retained false : Fin 4 → Fin 4) = id := by funext x; rfl
  simpa only [hr,List.map_id,List.length_map,bank,source,marked,List.map_nil,putWord] using hh

private theorem marker (xs : List Bool) : source xs 0 = separator := by
  rw [source,marked,putWord_outside _ _ _ _ (Or.inl (by omega))]
  rfl

private theorem no_marker (xs : List Bool) (z : ℤ) (hz : 0 < z) : source xs z ≠ separator := by
  by_cases hi : z < 1+xs.length
  · have hm := ReturnOrigin.putWord_mem (a := 0) empty 1 (xs.map bitSymbol) z ⟨by omega,by simpa using hi⟩
    obtain ⟨y,_,hy⟩ := List.mem_map.mp hm
    change putWord empty 1 (xs.map bitSymbol) z ≠ separator
    rw [← hy]
    cases y <;> decide
  · rw [source,marked,putWord_outside _ _ _ _ (Or.inr (by simpa using le_of_not_gt hi))]
    simp [empty,show z ≠ 0 by omega,blank,separator,Fin.ext_iff]

private def resetProgram : Program 2 2 0 where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols => if s = 0 then
    if symbols 0 = separator then some (1,fun i => (symbols i,Move.right))
    else some (0,fun i => (symbols i,Move.left)) else none

private def resetCfg (xs : List Bool) (p : ℤ) : Config 2 2 0 :=
  ⟨0,(Copy.tapes (source xs) (source xs) p p).head,(Copy.tapes (source xs) (source xs) p p).tape⟩

private theorem reset_step (xs : List Bool) (p : ℤ) (hp : 0 < p) :
    step resetProgram (resetCfg xs p) = some (resetCfg xs (p-1)) := by
  simp only [step,resetProgram,resetCfg,Copy.tapes,Copy.cfg,Config.tapes,ite_true,no_marker xs p hp,ite_false,Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i z; fin_cases i <;> by_cases hz : z = p <;> simp [hz]

private theorem reset_run (xs : List Bool) (n : ℕ) :
    run resetProgram n (resetCfg xs n) = some (resetCfg xs 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run,Nat.cast_add,Nat.cast_one,reset_step xs (n+1) (by omega)]
    simpa using ih

private theorem reset_hoare (xs : List Bool) :
    HoareTime resetProgram (fun v => v = Copy.tapes (source xs) (source xs) (1+xs.length) (1+xs.length))
      (fun v => v = bank xs xs) (xs.length+2) := by
  let last : Config 2 2 0 := ⟨1,(bank xs xs).head,(bank xs xs).tape⟩
  have hs : step resetProgram (resetCfg xs 0) = some last := by
    simp only [step,resetProgram,resetCfg,Copy.tapes,Copy.cfg,Config.tapes,ite_true,marker,Move.offset]
    congr 1
    congr 1
    · funext i; fin_cases i <;> rfl
    · funext i z; fin_cases i <;> by_cases hz : z = 0 <;> simp [bank,Copy.tapes,Copy.cfg,Config.tapes,hz]
  have hr := reset_run xs (xs.length+1)
  rw [Nat.cast_add,Nat.cast_one] at hr
  rintro v rfl
  refine ⟨xs.length+2,last,le_rfl,?_,?_,rfl⟩
  · rw [show xs.length+2 = (xs.length+1)+1 by omega,run_add]
    have hstart : (Copy.tapes (source xs) (source xs) (1+xs.length) (1+xs.length)).start resetProgram =
        resetCfg xs (xs.length+1) := by simp [Tapes.start,resetCfg,resetProgram,add_comm]
    rw [hstart,hr]
    simp only [Option.bind_some,run_one,hs]
  · simp [last,step,resetProgram]

/-- Five states, two tapes; no descriptor width occurs in finite control. -/
def program : Program 2 5 0 := seq (seq initProgram (Copy.program blank false)) resetProgram

theorem copy_hoare (xs : List Bool) :
    HoareTime program (fun v => v = input xs) (fun v => v = bank xs xs)
      (2*xs.length+5) := by
  exact (((init_hoare xs).seq (copy_body_hoare xs)).seq (reset_hoare xs)).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

theorem source_binary (xs : List Bool) : source xs = CountedCopyReuse.binary xs := by
  have h (f : ℤ → Fin 4) (p : ℤ) (bs : List Bool) :
      putBits f p bs = putWord f p (bs.map bitSymbol) := by
    induction bs generalizing p with
    | nil => rfl
    | cons x bs ih => simp only [putBits,putWord,List.map_cons,ih]
  exact (h _ _ _).symm

def encodedProgram (q : ℕ) : Program 2 5 q :=
  Alphabet.program RadixToBinary.binaryEncoding program

def encodedInput (q : ℕ) (xs : List Bool) : Tapes 2 q :=
  Copy.tapes (RadixZeroFill.encodedBinary xs) (fun _ => blank) 1 0

def encodedOutput (q : ℕ) (xs : List Bool) : Tapes 2 q :=
  Copy.tapes (RadixZeroFill.encodedBinary xs) (RadixZeroFill.encodedBinary xs) 1 1

theorem encoded_copy_hoare (q : ℕ) (xs : List Bool) :
    HoareTime (encodedProgram q) (fun v => v = encodedInput q xs)
      (fun v => v = encodedOutput q xs) (2*xs.length+5) := by
  have hi : Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := q)) (input xs) =
      encodedInput q xs := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    · rfl
    · rfl
    · simp only [input,Copy.tapes,Copy.cfg,Config.tapes,source_binary]
      rfl
    · rfl
  have ho : Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := q)) (bank xs xs) =
      encodedOutput q xs := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    · rfl
    · rfl
    · simp only [bank,Copy.tapes,Copy.cfg,Config.tapes,source_binary]
      rfl
    · simp only [bank,Copy.tapes,Copy.cfg,Config.tapes,source_binary]
      rfl
  apply (Alphabet.map_hoare (RadixToBinary.binaryEncoding (q := q)) (copy_hoare xs)).consequence _ _ le_rfl
  · intro v hv; exact ⟨_,rfl,hv.trans hi.symm⟩
  · rintro v ⟨w,rfl,hv⟩; exact hv.trans ho

end IntegerMultBounds.Machine.BinaryDescriptorCopy
