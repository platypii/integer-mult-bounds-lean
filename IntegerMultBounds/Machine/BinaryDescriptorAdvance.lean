import IntegerMultBounds.Machine.BinaryDescriptorIncrement
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList
import IntegerMultBounds.Machine.RecursiveChildQuotientsConstant
import IntegerMultBounds.Machine.CountedLoopReuseAlphabet

/-! Physically advance a marked offset by a retained runtime count.
Amortized increments pay for all carries; the work clock is initialized
and erased by the program, and the immutable count is restored. -/
namespace IntegerMultBounds.Machine.BinaryDescriptorAdvance
noncomputable section
variable {q : ℕ}
open SharedPlacementAlphabet (setTape)

def bank (ts bs : List Bool) (clock : ℤ → Fin (q+4)) (r : ℤ) : Tapes 3 q :=
  CountedLoopReuseAlphabet.bank (BinaryDescriptorIncrement.bank ts) clock
    (CountedLoopReuseAlphabet.binary bs) r 1

def input (ts bs : List Bool) := bank (q := q) ts bs (fun _ => blank) 0
def working (ts bs : List Bool) := bank (q := q) ts bs CountedLoopReuseAlphabet.empty 1

def initProgram := Placement.placed (RecursiveChildQuotientsConstant.program (a := q) 0)
  (FiniteReturnStackAt.placement (1 : Fin 3))
def loop := CountedLoopReuseAlphabet.program (BinaryDescriptorIncrement.program (q := q))
def cleanup := BinaryDescriptorCleanupList.oneProgram (a := q) (1 : Fin 3)
def program := seq (seq (initProgram (q := q)) loop) cleanup

private theorem initialize_hoare (ts bs : List Bool) :
    HoareTime (initProgram (q := q)) (fun v => v = input ts bs)
      (fun v => v = working ts bs) (RecursiveChildQuotientsConstant.cost 0) := by
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := q) 0)
    (FiniteReturnStackAt.placement (1 : Fin 3)) (input ts bs)
    (by rw [FiniteReturnStackAt.active_bank]; rfl)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem increment_advance (n : ℕ) (ts : List Bool) :
    GrowingCounterData.increment (GrowingCounterData.advance n ts) =
      GrowingCounterData.advance (n+1) ts := by
  induction n generalizing ts with
  | zero => rfl
  | succ n ih => exact ih (GrowingCounterData.increment ts)

private theorem cost_sum (n : ℕ) (ts : List Bool) :
    (∑ i ∈ Finset.range n, 2*GrowingCounterData.carrySteps (GrowingCounterData.advance i ts)) =
      GrowingCounterData.totalCost n ts := by
  induction n generalizing ts with
  | zero => simp [GrowingCounterData.totalCost]
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp only [GrowingCounterData.advance,ih,GrowingCounterData.totalCost]
    omega

theorem loop_hoare (ts bs : List Bool) (b : ℕ) (hb : Counter.value bs = b) :
    HoareTime (loop (q := q)) (fun v => v = working ts bs)
      (fun v => v = working (GrowingCounterData.advance b ts) bs)
      (GrowingCounterData.totalCost b ts+6*b+7*bs.length+16) := by
  have h := CountedLoopReuseAlphabet.loop_hoare BinaryDescriptorIncrement.program bs b
    (fun i => BinaryDescriptorIncrement.bank (GrowingCounterData.advance i ts))
    (fun i => 2*GrowingCounterData.carrySteps (GrowingCounterData.advance i ts)) hb
    (by intro i _; simpa only [increment_advance] using
      BinaryDescriptorIncrement.increment_hoare (q := q) (GrowingCounterData.advance i ts))
  rw [cost_sum] at h
  exact h

private theorem cleanup_hoare (ts bs : List Bool) :
    HoareTime (cleanup (q := q)) (fun v => v = working ts bs)
      (fun v => v = input ts bs) 4 := by
  have h := BinaryDescriptorCleanupList.one_hoare (1 : Fin 3) (working (q := q) ts bs) [] rfl rfl
  have he : setTape (working (q := q) ts bs) (1 : Fin 3) (fun _ => blank) 0 = input ts bs := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h
  exact h

theorem advances_hoare (ts bs : List Bool) (b : ℕ) (hb : Counter.value bs = b) :
    HoareTime (program (q := q)) (fun v => v = input ts bs)
      (fun v => v = input (GrowingCounterData.advance b ts) bs)
      (10*b+2*ts.length+7*bs.length+28) := by
  have h := ((initialize_hoare (q := q) ts bs).seq (loop_hoare ts bs b hb)).seq
    (cleanup_hoare (GrowingCounterData.advance b ts) bs)
  apply h.consequence (fun _ h => h) (fun _ h => h)
  have hc := GrowingCounterData.amortized_cost b ts
  have hz : RecursiveChildQuotientsConstant.cost 0 = 6 := rfl
  rw [hz]
  omega

theorem value (ts : List Bool) (b : ℕ) :
    Counter.value (GrowingCounterData.advance b ts) = Counter.value ts+b :=
  GrowingCounterData.advance_value b ts

theorem canonical (ts : List Bool) (b : ℕ) (ht : GrowingCounterData.Canonical ts) :
    GrowingCounterData.Canonical (GrowingCounterData.advance b ts) :=
  GrowingCounterData.advance_canonical b ts ht

end
end IntegerMultBounds.Machine.BinaryDescriptorAdvance
