import IntegerMultBounds.Machine.WeightedPhaseAccumulator
import IntegerMultBounds.Machine.CountedLoopReuseAlphabet

/-! A fixed-weight phase scanner repeats each statically selected edge weight
across a runtime number of coordinate axes. It traverses the control stream
once, retains the two phase flags and restores both binary loop controls.
Neither the axis count nor the control word is compiled into finite control. -/
namespace IntegerMultBounds.Machine.RepeatedWeightedPhaseAccumulator
noncomputable section
open WeightedPhaseAccumulator (bank next)
open CountedLoopReuseAlphabet (empty binary)

/-- Phase after the first `i` cells of a runtime block. -/
def scanPhase (w : ZMod 4) (p : Fin 4) (bits : ℕ → Bool) : ℕ → Fin 4
  | 0 => p
  | i+1 => next (scanPhase w p bits i) w (bits i)

def block (w : ZMod 4) :=
  CountedLoopReuseAlphabet.program (WeightedPhaseAccumulator.stepProgram w)

def boundary (p : Fin 4) (g : ℤ → Fin 6) (h : ℤ) (descriptor : List Bool) : Tapes 5 2 :=
  CountedLoopReuseAlphabet.bank (bank p g h) empty (binary descriptor) 1 1

/-- Every axis control is consumed exactly once. The binary runtime count is
copied, decremented with amortized cost, and erased by the actual machine. -/
theorem block_runs (w : ZMod 4) (p : Fin 4) (bits : ℕ → Bool)
    (g : ℤ → Fin 6) (h : ℤ) (descriptor : List Bool) (n : ℕ)
    (hn : Counter.value descriptor=n)
    (hb : ∀ i<n,g (h+i)=bitSymbol (bits i)) :
    HoareTime (block w) (fun v => v=boundary p g h descriptor)
      (fun v => v=boundary (scanPhase w p bits n) g (h+n) descriptor)
      (7*n+7*descriptor.length+16) := by
  have hr := CountedLoopReuseAlphabet.loop_hoare
    (WeightedPhaseAccumulator.stepProgram w) descriptor n
    (fun i => bank (scanPhase w p bits i) g (h+i)) (fun _ => 1) hn
    (fun i hi => by
      simpa only [scanPhase,Nat.cast_add,Nat.cast_one,add_assoc] using
        WeightedPhaseAccumulator.step_runs (scanPhase w p bits i) w (bits i) g (h+i) (hb i hi))
  simp only [scanPhase,Nat.cast_zero,add_zero] at hr
  apply hr.consequence (fun _ hv => hv) (fun _ hv => hv)
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one]
  omega

theorem scanPhase_cast (w : ZMod 4) (p : Fin 4) (bits : ℕ → Bool) (n : ℕ) :
    ((scanPhase w p bits n).val : ZMod 4)=
      (p.val : ZMod 4)+∑ i ∈ Finset.range n,if bits i then w else 0 := by
  induction n with
  | zero => simp [scanPhase]
  | succ n ih =>
    rw [scanPhase,WeightedPhaseAccumulator.next_cast,ih,Finset.sum_range_succ]
    ring

def states : List (ZMod 4) → ℕ
  | [] => 1
  | _::ws => 18+states ws

def program : (ws : List (ZMod 4)) → Program 5 (states ws) 2
  | [] => skip 5 2 (by decide)
  | w::ws => seq (block w) (program ws)

/-- The flat stream has one adjacent runtime-axis block per static weight. -/
def accumulate (p : Fin 4) (ws : List (ZMod 4)) (bits : ℕ → Bool) (n : ℕ) : Fin 4 :=
  match ws with
  | [] => p
  | w::ws => accumulate (scanPhase w p bits n) ws (fun i => bits (n+i)) n

theorem runs (p : Fin 4) (ws : List (ZMod 4)) (bits : ℕ → Bool)
    (g : ℤ → Fin 6) (h : ℤ) (descriptor : List Bool) (n : ℕ)
    (hn : Counter.value descriptor=n)
    (hb : ∀ i<ws.length*n,g (h+i)=bitSymbol (bits i)) :
    HoareTime (program ws) (fun v => v=boundary p g h descriptor)
      (fun v => v=boundary (accumulate p ws bits n) g (h+ws.length*n) descriptor)
      (ws.length*(7*n+7*descriptor.length+17)) := by
  induction ws generalizing p bits h with
  | nil =>
    simpa only [program,states,accumulate,List.length_nil,zero_mul,Nat.cast_zero,add_zero] using
      skip_hoare (by decide : 0<5) (boundary p g h descriptor)
  | cons w ws ih =>
    have hfirst : ∀ i<n,g (h+i)=bitSymbol (bits i) := by
      intro i hi
      apply hb i
      simp only [List.length_cons] ; nlinarith
    have hrest : ∀ i<ws.length*n,g (h+n+i)=bitSymbol (bits (n+i)) := by
      intro i hi
      have hh := hb (n+i) (by simp only [List.length_cons]; nlinarith)
      simpa only [Nat.cast_add,add_assoc] using hh
    have hr := (block_runs w p bits g h descriptor n hn hfirst).seq
      (ih (scanPhase w p bits n) (fun i => bits (n+i)) (h+n) hrest)
    apply hr.consequence (fun _ hv => hv) _ (by simp only [List.length_cons]; nlinarith)
    intro v hv
    simpa only [accumulate,List.length_cons,Nat.add_mul,Nat.cast_add,Nat.cast_mul,
      Nat.cast_one,one_mul,add_mul,add_assoc,add_comm,add_left_comm] using hv

/-- Exact total modulo-four exponent of the single flat traversal. -/
def total (ws : List (ZMod 4)) (bits : ℕ → Bool) (n : ℕ) : ZMod 4 :=
  match ws with
  | [] => 0
  | w::ws => (∑ i ∈ Finset.range n,if bits i then w else 0)+
      total ws (fun i => bits (n+i)) n

theorem accumulate_cast (p : Fin 4) (ws : List (ZMod 4)) (bits : ℕ → Bool) (n : ℕ) :
    ((accumulate p ws bits n).val : ZMod 4)=(p.val : ZMod 4)+total ws bits n := by
  induction ws generalizing p bits with
  | nil => simp [accumulate,total]
  | cons w ws ih =>
    rw [accumulate,ih,scanPhase_cast,total]
    ring

/-- A weight-block-major sum exposes the exact flat-stream phase, allowing
algebraic interchange with the coordinate-axis-major tensor phase sum. -/
theorem total_eq_sum (ws : List (ZMod 4)) (bits : ℕ → Bool) (n : ℕ) :
    total ws bits n=∑ i ∈ Finset.range ws.length,∑ j ∈ Finset.range n,
      if bits (i*n+j) then ws.getD i 0 else 0 := by
  induction ws generalizing bits with
  | nil => simp [total]
  | cons w ws ih =>
    rw [total,ih,List.length_cons,Finset.sum_range_succ']
    simp only [Nat.zero_mul,zero_add,List.getD_cons_zero,List.getD_cons_succ]
    conv_rhs => rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.add_mul,Nat.one_mul]
    have he : n+(i*n+j)=(i*n+n)+j := by omega
    rw [he]

/-- Runtime-axis repetition is paid by the actual selected address width,
without multiplying the coefficient traversal by the number of axes. -/
theorem volume_bound (ws : List (ZMod 4)) (n d : ℕ) (hn : 0<n) (hd : d≤n) :
    ws.length*(7*n+7*d+17)≤31*(ws.length*n) := by
  have h : 7*n+7*d+17≤31*n := by omega
  have hh := Nat.mul_le_mul_left ws.length h
  nlinarith

end
end IntegerMultBounds.Machine.RepeatedWeightedPhaseAccumulator
