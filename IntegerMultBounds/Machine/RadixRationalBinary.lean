import IntegerMultBounds.Machine.RadixRational
import IntegerMultBounds.Machine.RadixToBinary
import IntegerMultBounds.Machine.MarkedWordCleanup
import IntegerMultBounds.Machine.ReturnOrigin

/-! Compute a fixed rational multiple of a marked radix word, convert its
canonical residue to binary, and erase the temporary radix result. The source
word and its head are preserved; every arithmetic/conversion/cleanup step runs
on the actual tapes over the fixed radix alphabet. -/

namespace IntegerMultBounds.Machine.RadixRationalBinary

open RadixDigits
open MarkedWordCleanup (one word marked)
variable {q : ℕ} [Fact q.Prime]

def result (r : ℚ) (xs : List (Fin q)) :=
  RadixRationalData.digits (RadixRationalData.initial r.num r.den) xs

def source (xs : List (Fin q)) := marked (xs.map digitSymbol)

def radix (xs : List (Fin q)) := word (xs.map digitSymbol)

def pair (f g : ℤ → Fin (q+4)) (p r : ℤ) : Tapes 2 q := Copy.tapes f g p r

omit [Fact q.Prime] in
private theorem source_marker (xs : List (Fin q)) : source xs 0 = separator := by
  rw [source,marked,putWord_outside _ _ _ _ (Or.inl (by omega))]
  rfl

omit [Fact q.Prime] in
private theorem source_ne_marker (xs : List (Fin q)) (z : ℤ) (hz : 0 < z) : source xs z ≠ separator := by
  by_cases hi : z < 1+xs.length
  · have hm := ReturnOrigin.putWord_mem MarkedWordCleanup.empty 1 (xs.map digitSymbol) z
      ⟨by omega,by simpa using hi⟩
    obtain ⟨x,_,hx⟩ := List.mem_map.mp hm
    change putWord MarkedWordCleanup.empty 1 (xs.map digitSymbol) z ≠ separator
    rw [← hx]
    simp [digitSymbol,separator,Fin.ext_iff]
  · rw [source,marked,putWord_outside _ _ _ _ (Or.inr (by simpa using not_lt.mp hi))]
    simp [MarkedWordCleanup.empty,ne_of_gt hz,blank,separator]

private def initializeProgram : Program 2 2 q where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols => if s = 0 then
    some (1,fun i => if i = 0 then (symbols i,Move.stay) else (separator,Move.right)) else none

omit [Fact q.Prime] in
private theorem initialize_hoare (xs : List (Fin q)) :
    HoareTime initializeProgram
      (fun v => v = pair (source xs) (fun _ => blank) 1 0)
      (fun v => v = pair (source xs) MarkedWordCleanup.empty 1 1) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,(pair (source xs) MarkedWordCleanup.empty 1 1).head,
    (pair (source xs) MarkedWordCleanup.empty 1 1).tape⟩,le_rfl,?_,?_,rfl⟩
  · rw [run_one]
    simp only [step,initializeProgram,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i; fin_cases i <;> rfl
    · funext i z
      fin_cases i <;> simp [pair,Copy.tapes,Copy.cfg,Config.tapes,MarkedWordCleanup.empty]
      intro hz; subst z; rfl
  · simp [step,initializeProgram]

private theorem arithmetic_hoare (r : ℚ) (xs : List (Fin q)) :
    HoareTime (RadixRational.program q r.num r.den)
      (fun v => v = pair (source xs) MarkedWordCleanup.empty 1 1)
      (fun v => v = pair (source xs) (source (result r xs)) (1+xs.length) (1+xs.length)) xs.length := by
  rintro v rfl
  obtain ⟨hr,hh⟩ := RadixRational.rational_exact (RadixRationalData.initial r.num r.den) xs
    MarkedWordCleanup.empty MarkedWordCleanup.empty 1 1
    (by simp [MarkedWordCleanup.empty,show (1:ℤ)+xs.length ≠ 0 by omega])
  exact ⟨xs.length,_,le_rfl,hr,hh,rfl⟩

/-- Synchronous return: keep the source sentinel/head, remove the result sentinel. -/
private def resetProgram : Program 2 2 q where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols => if s = 0 then
    if symbols 0 = separator then
      some (1,fun i => if i = 0 then (symbols i,Move.right) else (blank,Move.stay))
    else some (0,fun i => (symbols i,Move.left)) else none

private def resetCfg (xs ys : List (Fin q)) (p : ℤ) : Config 2 2 q :=
  ⟨0,(pair (source xs) (source ys) p p).head,(pair (source xs) (source ys) p p).tape⟩

omit [Fact q.Prime] in
private theorem reset_step (xs ys : List (Fin q)) (p : ℤ) (hp : 0 < p) :
    step resetProgram (resetCfg xs ys p) = some (resetCfg xs ys (p-1)) := by
  simp only [step,resetProgram,resetCfg,pair,Copy.tapes,Copy.cfg,Config.tapes,ite_true,
    source_ne_marker xs p hp,ite_false,Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i z
    fin_cases i <;> by_cases hz : z = p <;> simp [hz]

omit [Fact q.Prime] in
private theorem reset_run (xs ys : List (Fin q)) (n : ℕ) :
    run resetProgram n (resetCfg xs ys n) = some (resetCfg xs ys 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run,Nat.cast_add,Nat.cast_one,reset_step xs ys (n+1) (by omega)]
    simpa using ih

omit [Fact q.Prime] in
private theorem reset_hoare (xs ys : List (Fin q)) :
    HoareTime resetProgram
      (fun v => v = pair (source xs) (source ys) (1+xs.length) (1+xs.length))
      (fun v => v = pair (source xs) (radix ys) 1 0) (xs.length+2) := by
  let last : Config 2 2 q := ⟨1,(pair (source xs) (radix ys) 1 0).head,(pair (source xs) (radix ys) 1 0).tape⟩
  have hs : step resetProgram (resetCfg xs ys 0) = some last := by
    simp only [step,resetProgram,resetCfg,pair,Copy.tapes,Copy.cfg,Config.tapes,ite_true,source_marker]
    congr 1
    congr 1
    · funext i; fin_cases i <;> rfl
    · funext i z
      fin_cases i
      · simp [pair,Copy.tapes,Copy.cfg,Config.tapes]
        intro hz; subst z; rfl
      · change (if z = 0 then blank else source ys z) = radix ys z
        by_cases hz : z = 0
        · subst z; simp only [ite_true]
          rw [radix,word,putWord_outside _ _ _ _ (Or.inl (by omega))]
        · simp [source,radix,← MarkedWordCleanup.mark_word,hz]
  have hr := reset_run xs ys (xs.length+1)
  rw [Nat.cast_add,Nat.cast_one] at hr
  rintro v rfl
  refine ⟨xs.length+2,last,le_rfl,?_,?_,rfl⟩
  · rw [show xs.length+2 = (xs.length+1)+1 by omega,run_add]
    have hstart : (pair (source xs) (source ys) (1+xs.length) (1+xs.length)).start resetProgram =
        resetCfg xs ys (xs.length+1) := by simp [Tapes.start,resetCfg,resetProgram,add_comm]
    rw [hstart,hr]
    simp only [Option.bind_some,run_one,hs]
  · simp [last,step,resetProgram]

/-- Mark, perform fixed-rational arithmetic, restore source head and unmark result. -/
def arithmeticProgram (r : ℚ) : Program 2 (2+(2*r.num.natAbs+r.den+1)+2) q :=
  seq (seq initializeProgram (RadixRational.program q r.num r.den)) resetProgram

theorem arithmetic_stage_hoare (r : ℚ) (xs : List (Fin q)) :
    HoareTime (arithmeticProgram r)
      (fun v => v = pair (source xs) (fun _ => blank) 1 0)
      (fun v => v = pair (source xs) (radix (result r xs)) 1 0) (2*xs.length+5) := by
  exact (((initialize_hoare xs).seq (arithmetic_hoare r xs)).seq (reset_hoare xs (result r xs))).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

/-- Binary result, converter clock, temporary radix result, marked input. -/
def bank (binaryTape : ℤ → Fin (q+4)) (h : ℤ) (xs ys : List (Fin q)) : Tapes 4 q :=
  ⟨![h,0,0,1],![binaryTape,fun _ => blank,radix ys,source xs]⟩

def input (xs : List (Fin q)) : Tapes 4 q := bank (fun _ => blank) 0 xs []

def output (r : ℚ) (xs : List (Fin q)) : Tapes 4 q :=
  bank ((RadixToBinary.binaryState q (RadixToBinaryData.output (result r xs))).tape 0) 1 xs []

private def arithmeticPlacement : Fin (2+2) ≃ Fin 4 := (Equiv.swap 0 3).trans (Equiv.swap 1 2)

private theorem arithmetic_at (r : ℚ) (xs : List (Fin q)) :
    HoareTime (Placement.placed (arithmeticProgram r) arithmeticPlacement)
      (fun v => v = input xs) (fun v => v = bank (fun _ => blank) 0 xs (result r xs)) (2*xs.length+5) := by
  have ha : Placement.active arithmeticPlacement (input xs) = pair (source xs) (fun _ => blank) 1 0 := by
    unfold Placement.active arithmeticPlacement input bank pair Copy.tapes Copy.cfg Config.tapes
    congr 1 <;> funext i <;> fin_cases i <;> rfl
  have hf : Placement.active arithmeticPlacement (bank (fun _ => blank) 0 xs (result r xs)) =
      pair (source xs) (radix (result r xs)) 1 0 := by
    unfold Placement.active arithmeticPlacement bank pair Copy.tapes Copy.cfg Config.tapes
    congr 1 <;> funext i <;> fin_cases i <;> rfl
  have he : Placement.extra arithmeticPlacement (input xs) =
      Placement.extra arithmeticPlacement (bank (fun _ => blank) 0 xs (result r xs)) := by
    unfold Placement.extra arithmeticPlacement input bank
    congr 1
    funext i
    fin_cases i <;> rfl
  apply (Placement.hoare_at (arithmetic_stage_hoare r xs) arithmeticPlacement (input xs) ha).consequence
    (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  rw [Placement.replace,he,← hf]
  exact Placement.view _ _

omit [Fact q.Prime] in
private theorem conversion_input (xs ys : List (Fin q)) :
    (RadixToBinary.input ys).append (one (source xs) 1) = bank (fun _ => blank) 0 xs ys := by
  unfold Tapes.append bank one RadixToBinary.input
  congr 1 <;> funext i <;> fin_cases i <;> rfl

omit [Fact q.Prime] in
private theorem conversion_output (xs ys : List (Fin q)) :
    (RadixToBinary.output ys).append (one (source xs) 1) =
      bank ((RadixToBinary.binaryState q (RadixToBinaryData.output ys)).tape 0) 1 xs ys := by
  unfold Tapes.append bank one RadixToBinary.output
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem conversion_at (xs ys : List (Fin q)) :
    HoareTime (extend (RadixToBinary.convertProgram (Fact.out : q.Prime).two_le) 1)
      (fun v => v = bank (fun _ => blank) 0 xs ys)
      (fun v => v = bank ((RadixToBinary.binaryState q (RadixToBinaryData.output ys)).tape 0) 1 xs ys)
      (10*value ys+6*ys.length+14) := by
  have hh := (RadixToBinary.convert_hoare (Fact.out : q.Prime).two_le ys).extend (one (source xs) 1)
  apply hh.consequence _ _ le_rfl
  · intro v hv; exact ⟨_,rfl,by simpa only [conversion_input] using hv⟩
  · rintro v ⟨w,rfl,hv⟩; simpa only [conversion_output] using hv

private def cleanupPlacement : Fin (1+3) ≃ Fin 4 := Equiv.swap 0 2

omit [Fact q.Prime] in
private theorem cleanup_at (f : ℤ → Fin (q+4)) (h : ℤ) (xs ys : List (Fin q)) :
    HoareTime (Placement.placed MarkedWordCleanup.program cleanupPlacement)
      (fun v => v = bank f h xs ys) (fun v => v = bank f h xs []) (2*ys.length+6) := by
  have hd : ∀ d ∈ ys.map digitSymbol, d ≠ (blank : Fin (q+4)) := by
    intro d hm
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hm
    simp [digitSymbol,blank,Fin.ext_iff]
  have ha : Placement.active cleanupPlacement (bank f h xs ys) = one (word (ys.map digitSymbol)) 0 := by
    unfold Placement.active cleanupPlacement bank one
    congr 1 <;> funext i <;> fin_cases i <;> rfl
  have hf : Placement.active cleanupPlacement (bank f h xs []) = one (fun _ => blank) 0 := by
    unfold Placement.active cleanupPlacement bank one
    congr 1 <;> funext i <;> fin_cases i <;> rfl
  have he : Placement.extra cleanupPlacement (bank f h xs ys) = Placement.extra cleanupPlacement (bank f h xs []) := by
    unfold Placement.extra cleanupPlacement bank
    congr 1
    funext i
    fin_cases i <;> rfl
  have hh := Placement.hoare_at (MarkedWordCleanup.cleanup_hoare (ys.map digitSymbol) hd)
    cleanupPlacement (bank f h xs ys) ha
  simp only [List.length_map] at hh
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  rw [Placement.replace,he,← hf]
  exact Placement.view _ _

/-- Literal fixed-rational arithmetic, physical conversion, complete scratch cleanup. -/
def program (r : ℚ) : Program 4 ((2+(2*r.num.natAbs+r.den+1)+2)+18+6) q :=
  seq (seq (Placement.placed (arithmeticProgram r) arithmeticPlacement)
    (extend (RadixToBinary.convertProgram (Fact.out : q.Prime).two_le) 1))
    (Placement.placed MarkedWordCleanup.program cleanupPlacement)

theorem compute_hoare (r : ℚ) (xs : List (Fin q)) :
    HoareTime (program r) (fun v => v = input xs) (fun v => v = output r xs)
      (10*value (result r xs)+10*xs.length+27) := by
  have hh := ((arithmetic_at r xs).seq (conversion_at xs (result r xs))).seq
    (cleanup_at ((RadixToBinary.binaryState q (RadixToBinaryData.output (result r xs))).tape 0) 1 xs (result r xs))
  have hlen : (result r xs).length = xs.length := RadixRationalData.digits_length _ _
  exact hh.consequence (fun _ h => h) (fun _ h => h) (by omega)

/-- Canonical binary output agrees with the rational residue used by the network. -/
theorem output_value (r : ℚ) (hden : r.den < q) (xs : List (Fin q)) :
    (Counter.value (RadixToBinaryData.output (result r xs)) : ZMod (q^xs.length)) =
      Swap.Modular.ratMod (q^xs.length) r * (value xs : ZMod (q^xs.length)) := by
  rw [RadixToBinaryData.output_value]
  exact RadixRational.output_ratMod r hden xs

theorem output_canonical (r : ℚ) (xs : List (Fin q)) :
    GrowingCounterData.Canonical (RadixToBinaryData.output (result r xs)) :=
  RadixToBinaryData.output_canonical _

/-- Literal binary tape, using the reserved four symbols of the radix alphabet. -/
theorem output_binary (r : ℚ) (xs : List (Fin q)) :
    (output r xs).head 0 = 1 ∧ (output r xs).tape 0 =
      fun z => (RadixToBinary.binaryEncoding (q := q)).encode
        (CountedCopyReuse.binary (RadixToBinaryData.output (result r xs)) z) := ⟨rfl,rfl⟩

/-- All temporary radix storage is blank and its heads have returned to zero. -/
theorem workspace_restored (r : ℚ) (xs : List (Fin q)) :
    (output r xs).tape 1 = (fun _ => blank) ∧ (output r xs).head 1 = 0 ∧
    (output r xs).tape 2 = (fun _ => blank) ∧ (output r xs).head 2 = 0 ∧
    (output r xs).tape 3 = source xs ∧ (output r xs).head 3 = 1 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem compute_hoare_fiber (r : ℚ) (xs : List (Fin q)) (B : ℕ) (hB : 0 < B) :
    HoareTime (program r) (fun v => v = input xs) (fun v => v = output r xs) (47*(q^xs.length*B)) := by
  apply (compute_hoare r xs).consequence (fun _ h => h) (fun _ h => h) _
  have hv := value_lt (Fact.out : q.Prime).two_le (result r xs)
  have hw := RadixToBinaryData.width_le_power (Fact.out : q.Prime).two_le xs.length
  have hlen : (result r xs).length = xs.length := RadixRationalData.digits_length _ _
  rw [hlen] at hv
  have hp : 1 ≤ q^xs.length := Nat.one_le_pow _ _ (by have := (Fact.out : q.Prime).two_le; omega)
  have hm : q^xs.length ≤ q^xs.length*B := by nlinarith
  omega

end IntegerMultBounds.Machine.RadixRationalBinary
