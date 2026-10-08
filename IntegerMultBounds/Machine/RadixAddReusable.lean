import IntegerMultBounds.Machine.RadixAdd
import IntegerMultBounds.Machine.MarkedWordCleanup
import IntegerMultBounds.Machine.ReturnOrigin
import IntegerMultBounds.Machine.FamilyPlacementAlphabet

/-! Literal modular radix addition with restored input and output heads. All
three temporary markers are written and removed by the machine. The source
words are preserved exactly, and the output can feed another arithmetic stage. -/
namespace IntegerMultBounds.Machine.RadixAddReusable

open RadixDigits
open MarkedWordCleanup (word marked)
variable {q : ℕ}

def bank (xs ys zs : List (Fin q)) : Tapes 3 q :=
  ⟨![0,0,0],![word (xs.map digitSymbol),word (ys.map digitSymbol),word (zs.map digitSymbol)]⟩

private def markedBank (xs ys zs : List (Fin q)) (p : ℤ) : Tapes 3 q :=
  ⟨![p,p,p],![marked (xs.map digitSymbol),marked (ys.map digitSymbol),marked (zs.map digitSymbol)]⟩

def result (hq : 2 ≤ q) (xs ys : List (Fin q)) := RadixAdd.digits hq 0 (xs.zip ys)

private def initializeProgram : Program 3 2 q where
  tapes_pos := by decide
  start := 0
  transition := fun s _ => if s = 0 then some (1,fun _ => (separator,Move.right)) else none

private theorem initialize_hoare (xs ys : List (Fin q)) :
    HoareTime initializeProgram (fun v => v = bank xs ys []) (fun v => v = markedBank xs ys [] 1) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,(markedBank xs ys [] 1).head,(markedBank xs ys [] 1).tape⟩,le_rfl,?_,?_,rfl⟩
  · rw [run_one]
    simp only [step,initializeProgram,Tapes.start,ite_true,Move.offset]
    congr 1
    congr 1
    · funext i; fin_cases i <;> rfl
    · funext i z
      fin_cases i <;> simp [bank,markedBank,← MarkedWordCleanup.mark_word,Function.update_apply]
  · simp [step,initializeProgram]

private theorem marked_marker (xs : List (Fin q)) : marked (xs.map digitSymbol) 0 = separator := by
  rw [marked,putWord_outside _ _ _ _ (Or.inl (by omega))]
  rfl

private theorem marked_ne_marker (xs : List (Fin q)) (z : ℤ) (hz : 0 < z) :
    marked (xs.map digitSymbol) z ≠ separator := by
  by_cases hi : z < 1+xs.length
  · have hm := ReturnOrigin.putWord_mem MarkedWordCleanup.empty 1 (xs.map digitSymbol) z
      ⟨by omega,by simpa using hi⟩
    obtain ⟨x,_,hx⟩ := List.mem_map.mp hm
    change putWord MarkedWordCleanup.empty 1 (xs.map digitSymbol) z ≠ separator
    rw [← hx]
    simp [digitSymbol,separator,Fin.ext_iff]
  · rw [marked,putWord_outside _ _ _ _ (Or.inr (by simpa using le_of_not_gt hi))]
    simp [MarkedWordCleanup.empty,show z ≠ 0 by omega,blank,separator,Fin.ext_iff]

private def resetProgram : Program 3 2 q where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols => if s = 0 then
    if symbols 0 = separator then some (1,fun _ => (blank,Move.stay))
    else some (0,fun i => (symbols i,Move.left)) else none

private def resetCfg (xs ys zs : List (Fin q)) (p : ℤ) : Config 3 2 q :=
  ⟨0,(markedBank xs ys zs p).head,(markedBank xs ys zs p).tape⟩

private theorem reset_step (xs ys zs : List (Fin q)) (p : ℤ) (hp : 0 < p) :
    step resetProgram (resetCfg xs ys zs p) = some (resetCfg xs ys zs (p-1)) := by
  simp only [step,resetProgram,resetCfg,markedBank,Matrix.cons_val_zero,ite_true,marked_ne_marker xs p hp,ite_false,Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i z
    fin_cases i <;> by_cases hz : z = p <;> simp [hz]

private theorem reset_run (xs ys zs : List (Fin q)) (n : ℕ) :
    run resetProgram n (resetCfg xs ys zs n) = some (resetCfg xs ys zs 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run,Nat.cast_add,Nat.cast_one,reset_step xs ys zs (n+1) (by omega)]
    simpa using ih

private theorem reset_hoare (xs ys zs : List (Fin q)) :
    HoareTime resetProgram (fun v => v = markedBank xs ys zs (1+xs.length))
      (fun v => v = bank xs ys zs) (xs.length+2) := by
  let last : Config 3 2 q := ⟨1,(bank xs ys zs).head,(bank xs ys zs).tape⟩
  have hs : step resetProgram (resetCfg xs ys zs 0) = some last := by
    simp only [step,resetProgram,resetCfg,markedBank,Matrix.cons_val_zero,ite_true,marked_marker]
    congr 1
    congr 1
    · funext i; fin_cases i <;> rfl
    · funext i z
      fin_cases i <;> change (if z = 0 then blank else marked _ z) = word _ z
      all_goals
        by_cases hz : z = 0
        · subst z; simp only [ite_true]
          rw [word,putWord_outside _ _ _ _ (Or.inl (by omega))]
        · simp [← MarkedWordCleanup.mark_word,hz]
  have hr := reset_run xs ys zs (xs.length+1)
  rw [Nat.cast_add,Nat.cast_one] at hr
  rintro v rfl
  refine ⟨xs.length+2,last,le_rfl,?_,?_,rfl⟩
  · rw [show xs.length+2 = (xs.length+1)+1 by omega,run_add]
    have hstart : (markedBank xs ys zs (1+xs.length)).start resetProgram = resetCfg xs ys zs (xs.length+1) := by
      simp [Tapes.start,resetCfg,resetProgram,add_comm]
    rw [hstart,hr]
    simp only [Option.bind_some,run_one,hs]
  · simp [last,step,resetProgram]

private theorem arithmetic_hoare (hq : 2 ≤ q) (xs ys : List (Fin q)) (hlen : xs.length = ys.length) :
    HoareTime (RadixAdd.program q hq) (fun v => v = markedBank xs ys [] 1)
      (fun v => v = markedBank xs ys (result hq xs ys) (1+xs.length)) xs.length := by
  rintro v rfl
  obtain ⟨hr,hh⟩ := RadixAdd.add_exact hq 0 xs ys hlen
    MarkedWordCleanup.empty MarkedWordCleanup.empty MarkedWordCleanup.empty 1 1 1
    (by simp [MarkedWordCleanup.empty,show (1:ℤ)+xs.length ≠ 0 by omega])
    (by simp [MarkedWordCleanup.empty,show (1:ℤ)+ys.length ≠ 0 by omega])
  have hin : (markedBank xs ys [] 1).start (RadixAdd.program q hq) =
      RadixAdd.cfg (marked (xs.map digitSymbol)) (marked (ys.map digitSymbol)) MarkedWordCleanup.empty 1 1 1 0 := by
    unfold Tapes.start markedBank RadixAdd.program RadixAdd.cfg
    congr 1 <;> funext i <;> fin_cases i <;> rfl
  rw [hin]
  refine ⟨xs.length,_,le_rfl,hr,hh,?_⟩
  unfold Config.tapes RadixAdd.cfg markedBank result
  congr 1 <;> funext i <;> fin_cases i <;> simp [hlen,marked]

/-- Three tapes, six states, and real origin restoration after modular addition. -/
def program (q : ℕ) (hq : 2 ≤ q) : Program 3 6 q :=
  seq (seq initializeProgram (RadixAdd.program q hq)) resetProgram

theorem add_hoare (hq : 2 ≤ q) (xs ys : List (Fin q)) (hlen : xs.length = ys.length) :
    HoareTime (program q hq) (fun v => v = bank xs ys []) (fun v => v = bank xs ys (result hq xs ys))
      (2*xs.length+5) := by
  exact (((initialize_hoare xs ys).seq (arithmetic_hoare hq xs ys hlen)).seq (reset_hoare xs ys (result hq xs ys))).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

theorem result_length (hq : 2 ≤ q) (xs ys : List (Fin q)) (hlen : xs.length = ys.length) :
    (result hq xs ys).length = xs.length := by simp [result,hlen]

theorem result_value (hq : 2 ≤ q) (xs ys : List (Fin q)) (hlen : xs.length = ys.length) :
    value (result hq xs ys) = (value xs+value ys)%q^xs.length := by
  simpa [result] using RadixAdd.digits_value_mod hq 0 xs ys hlen

private theorem bank_group (xs ys zs : List (Fin q)) :
    bank xs ys zs =
      ((MarkedWordCleanup.one (word (xs.map digitSymbol)) 0).append
        (MarkedWordCleanup.one (word (ys.map digitSymbol)) 0)).append
        (MarkedWordCleanup.one (word (zs.map digitSymbol)) 0) := by
  unfold bank MarkedWordCleanup.one Tapes.append
  congr 1 <;> funext i <;> fin_cases i <;> rfl

/-- Accumulate two temporary words, then erase and restore both source tapes. -/
def consumeProgram (q : ℕ) (hq : 2 ≤ q) : Program 3 18 q :=
  seq (program q hq)
    (extend (FamilyPlacementAlphabet.sequence MarkedWordCleanup.program MarkedWordCleanup.program) 1)

theorem consume_hoare (hq : 2 ≤ q) (xs ys : List (Fin q)) (hlen : xs.length = ys.length) :
    HoareTime (consumeProgram q hq) (fun v => v = bank xs ys [])
      (fun v => v = bank [] [] (result hq xs ys)) (6*xs.length+19) := by
  have hn (ws : List (Fin q)) : ∀ x ∈ ws.map digitSymbol, x ≠ (blank : Fin (q+4)) := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx
    simp [digitSymbol,blank,Fin.ext_iff]
  have hc := FamilyPlacementAlphabet.extend_hoare (FamilyPlacementAlphabet.sequence_hoare
    (MarkedWordCleanup.cleanup_hoare (xs.map digitSymbol) (hn xs))
    (MarkedWordCleanup.cleanup_hoare (ys.map digitSymbol) (hn ys)))
    (MarkedWordCleanup.one (word ((result hq xs ys).map digitSymbol)) 0)
  have hc' : HoareTime
      (extend (FamilyPlacementAlphabet.sequence MarkedWordCleanup.program MarkedWordCleanup.program) 1)
      (fun v => v = bank xs ys (result hq xs ys))
      (fun v => v = bank [] [] (result hq xs ys)) (4*xs.length+13) := by
    apply hc.consequence _ _ (by simp only [List.length_map]; omega)
    · intro v hv; simpa only [bank_group] using hv
    · intro v hv; simpa only [bank_group,word,List.map_nil,putWord] using hv
  exact ((add_hoare hq xs ys hlen).seq hc').consequence (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.RadixAddReusable
