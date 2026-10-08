import IntegerMultBounds.Machine.GrowingCounter
import IntegerMultBounds.Machine.Placement

/-! Literal delimiter-terminated source length measurement. A fixed two-tape
controller grows a binary descriptor from its empty marked tape. Every source
cell is preserved, every increment and head movement is charged, and the
controller truly halts on the first blank source symbol. -/

namespace IntegerMultBounds.Machine.BinaryLength

open GrowingCounterData (increment carrySteps advance)
open Placement (ExactRun)

/-- Source tape zero, growing binary length tape one. -/
def bank (source : ℤ → Fin 4) (p : ℤ) (bs : List Bool) : Tapes 2 0 :=
  ⟨fun i => if i = 0 then p else 1,
    fun i => if i = 0 then source else putBits GrowingCounter.emptyTape 1 bs⟩

def counterPlacement : Fin (1+1) ≃ Fin 2 := Equiv.swap 0 1

def incrementProgram : Program 2 3 0 := Placement.placed GrowingCounter.program counterPlacement

private theorem active_bank (source : ℤ → Fin 4) (p : ℤ) (bs : List Bool) :
    Placement.active counterPlacement (bank source p bs) = GrowingCounter.clock bs := by
  unfold Placement.active counterPlacement bank GrowingCounter.clock GrowingCounter.tapes
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem replace_bank (source : ℤ → Fin 4) (p : ℤ) (bs cs : List Bool) :
    Placement.replace counterPlacement (bank source p bs) (GrowingCounter.clock cs) = bank source p cs := by
  unfold Placement.replace Placement.combine Placement.extra Tapes.append Tapes.reindex
    counterPlacement bank GrowingCounter.clock GrowingCounter.tapes
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem increment_exact (source : ℤ → Fin 4) (p : ℤ) (bs : List Bool) :
    ExactRun incrementProgram (2*carrySteps bs) (bank source p bs) (bank source p (increment bs)) := by
  obtain ⟨hr,hh⟩ := GrowingCounter.clock_increment bs
  have h : ExactRun GrowingCounter.program (2*carrySteps bs)
      (GrowingCounter.clock bs) (GrowingCounter.clock (increment bs)) := ⟨_,hr,hh,rfl⟩
  rw [← active_bank source p bs] at h
  have hp := Placement.placed_exact GrowingCounter.program counterPlacement (bank source p bs) _ h
  simpa only [replace_bank,incrementProgram] using hp

/-- One actual source-head movement; both complete tapes are read back unchanged. -/
def advanceProgram : Program 2 2 0 where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols => if state = 0 then
    some (1,fun i => (symbols i,if i = 0 then .right else .stay)) else none

private theorem advance_exact (source : ℤ → Fin 4) (p : ℤ) (bs : List Bool) :
    ExactRun advanceProgram 1 (bank source p bs) (bank source (p+1) bs) := by
  let c : Config 2 2 0 := ⟨1,(bank source (p+1) bs).head,(bank source (p+1) bs).tape⟩
  refine ⟨c,?_,?_,rfl⟩
  · simp only [run_one,step,advanceProgram,Tapes.start,bank,ite_true]
    congr 1
    congr 1
    · funext i; fin_cases i <;> simp [bank,Move.offset]
    · funext i j
      fin_cases i <;> simp [bank,eq_comm] <;> intro hj <;> rw [hj]
  · simp [c,step,advanceProgram]

def body : Program 2 5 0 := seq incrementProgram advanceProgram

private theorem body_exact (source : ℤ → Fin 4) (p : ℤ) (bs : List Bool) :
    ExactRun body (2*carrySteps bs+2) (bank source p bs) (bank source (p+1) (increment bs)) := by
  simpa only [body,Nat.add_assoc] using
    Placement.exact_seq (increment_exact source p bs) (advance_exact source p (increment bs))

def test (symbols : Fin 2 → Fin 4) : Bool := decide (symbols 0 ≠ blank)

/-- Six fixed states work for all source lengths and all descriptor widths. -/
def program : Program 2 6 0 := whileLoop body test

/-- Exact transition cost: real increments, source moves, joins, and loop control. -/
def runtime (n : ℕ) (bs : List Bool) : ℕ := GrowingCounterData.totalCost n bs+4*n

theorem runtime_succ (n : ℕ) (bs : List Bool) :
    runtime (n+1) bs = 2*carrySteps bs+4+runtime n (increment bs) := by
  simp only [runtime,GrowingCounterData.totalCost]
  omega

theorem runtime_le (n : ℕ) (bs : List Bool) : runtime n bs ≤ 8*n+2*bs.length := by
  have h := GrowingCounterData.amortized_cost n bs
  dsimp only [runtime]
  omega

/-- Scan exactly a nonblank segment, retaining the source and every counter bit. -/
theorem scan_run (n : ℕ) (source : ℤ → Fin 4) (p : ℤ) (bs : List Bool)
    (hsource : ∀ j : ℕ, j < n → source (p+j) ≠ blank) :
    run program (runtime n bs) ((bank source p bs).start program) =
      some ((bank source (p+n) (advance n bs)).start program) := by
  induction n generalizing p bs with
  | zero => simp [runtime,GrowingCounterData.totalCost,advance,run]
  | succ n ih =>
    obtain ⟨c,hr,hh,hc⟩ := body_exact source p bs
    have ht : test (bank source p bs).reads = true := by
      have hz := hsource 0 (by omega)
      simpa [test,Tapes.reads,bank] using hz
    have hi := while_run_iteration body test (bank source p bs) ht hr hh
    rw [hc] at hi
    change run program (2*carrySteps bs+2+2) ((bank source p bs).start program) = _ at hi
    rw [runtime_succ,show 2*carrySteps bs+4 = 2*carrySteps bs+2+2 by omega,run_add,hi]
    simp only [Option.bind_some]
    have hs : ∀ j : ℕ, j < n → source (p+1+j) ≠ blank := by
      intro j hj
      have hj' := hsource (j+1) (by omega)
      simpa only [Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using hj'
    simpa only [program,advance,Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using
      ih (p+1) (increment bs) hs

/-- The final source blank makes the fixed controller genuinely halt. -/
theorem scan_exact (n : ℕ) (source : ℤ → Fin 4) (p : ℤ) (bs : List Bool)
    (hsource : ∀ j : ℕ, j < n → source (p+j) ≠ blank) (hend : source (p+n) = blank) :
    run program (runtime n bs) ((bank source p bs).start program) =
      some ((bank source (p+n) (advance n bs)).start program) ∧
    step program ((bank source (p+n) (advance n bs)).start program) = none := by
  refine ⟨scan_run n source p bs hsource,?_⟩
  exact while_step_exit body test _ (by simp [test,Tapes.reads,bank,hend])

/-- Descriptor bootstrap from an empty marked counter: exact natural length,
canonical binary output, logarithmic width, and at most eight transitions per
source symbol, with no prepared counter width. -/
theorem length_exact (n : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (hsource : ∀ j : ℕ, j < n → source (p+j) ≠ blank) (hend : source (p+n) = blank) :
    let bs := advance n []
    Counter.value bs = n ∧ GrowingCounterData.Canonical bs ∧ bs.length ≤ n.log2+1 ∧
    runtime n [] ≤ 8*n ∧
    run program (runtime n []) ((bank source p []).start program) =
      some ((bank source (p+n) bs).start program) ∧
    step program ((bank source (p+n) bs).start program) = none := by
  refine ⟨GrowingCounterData.empty_value n,GrowingCounterData.advance_canonical n [] (Or.inl rfl),
    GrowingCounterData.empty_width n,by simpa using runtime_le n [],?_⟩
  exact scan_exact n source p [] hsource hend

theorem length_hoare (n : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (hsource : ∀ j : ℕ, j < n → source (p+j) ≠ blank) (hend : source (p+n) = blank) :
    HoareTime program (fun v => v = bank source p [])
      (fun v => ∃ bs : List Bool, Counter.value bs = n ∧ GrowingCounterData.Canonical bs ∧
        bs.length ≤ n.log2+1 ∧ v = bank source (p+n) bs) (8*n) := by
  intro v hv
  subst v
  obtain ⟨hvalue,hcanonical,hwidth,hcost,hr,hh⟩ := length_exact n source p hsource hend
  exact ⟨runtime n [],_,hcost,hr,hh,advance n [],hvalue,hcanonical,hwidth,rfl⟩

end IntegerMultBounds.Machine.BinaryLength
