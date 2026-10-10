import IntegerMultBounds.Machine.RepeatedWeightedPhaseAccumulator
import IntegerMultBounds.Machine.CountedLoopHeaderClean

/-! Runtime-axis phase scanning directly from an immutable original header.
Both loop scratch tapes begin and end blank, including every sentinel. -/
namespace IntegerMultBounds.Machine.RepeatedWeightedPhaseHeader
noncomputable section
open WeightedPhaseAccumulator (bank)
open RepeatedWeightedPhaseAccumulator (scanPhase accumulate)
open MarkedWordCleanup (one)

def bank4 (p : Fin 4) (g : ℤ → Fin 6) (h : ℤ) (ds : List Bool) : Tapes 4 2 :=
  (bank p g h).append (one (RadixZeroFill.encodedBinary ds) 1)
def boundary (p : Fin 4) (g : ℤ → Fin 6) (h : ℤ) (ds : List Bool) : Tapes 6 2 :=
  CountedLoopHeaderClean.bank (bank4 p g h ds)
def block (w : ZMod 4) := CountedLoopHeaderClean.program
  (extend (WeightedPhaseAccumulator.stepProgram w) 1) (3 : Fin 4)

theorem block_runs (w : ZMod 4) (p : Fin 4) (bits : ℕ → Bool)
    (g : ℤ → Fin 6) (h : ℤ) (ds : List Bool) (n : ℕ)
    (hn : Counter.value ds=n) (hb : ∀ i<n,g (h+i)=bitSymbol (bits i)) :
    HoareTime (block w) (fun v => v=boundary p g h ds)
      (fun v => v=boundary (scanPhase w p bits n) g (h+n) ds)
      (7*n+11*ds.length+35) := by
  have hr := CountedLoopHeaderClean.runs
    (extend (WeightedPhaseAccumulator.stepProgram w) 1) (3 : Fin 4) ds n
    (fun i => bank4 (scanPhase w p bits i) g (h+i) ds) (fun _ => 1)
    ⟨rfl,rfl⟩ hn (fun i hi => by
      have hs := hoare_extend_eq (WeightedPhaseAccumulator.step_runs
        (scanPhase w p bits i) w (bits i) g (h+i) (hb i hi))
        (one (RadixZeroFill.encodedBinary ds) 1)
      simpa only [bank4,scanPhase,Nat.cast_add,Nat.cast_one,add_assoc] using hs)
  simp only [scanPhase,Nat.cast_zero,add_zero] at hr
  apply hr.consequence (fun _ hv => hv) (fun _ hv => hv)
  simp only [CountedLoopHeaderClean.cost,Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one]
  omega

def states : List (ZMod 4) → ℕ
  | [] => 1
  | _::ws => 34+states ws

def program : (ws : List (ZMod 4)) → Program 6 (states ws) 2
  | [] => skip 6 2 (by decide)
  | w::ws => seq (block w) (program ws)

theorem runs (p : Fin 4) (ws : List (ZMod 4)) (bits : ℕ → Bool)
    (g : ℤ → Fin 6) (h : ℤ) (ds : List Bool) (n : ℕ)
    (hn : Counter.value ds=n) (hb : ∀ i<ws.length*n,g (h+i)=bitSymbol (bits i)) :
    HoareTime (program ws) (fun v => v=boundary p g h ds)
      (fun v => v=boundary (accumulate p ws bits n) g (h+ws.length*n) ds)
      (ws.length*(7*n+11*ds.length+36)) := by
  induction ws generalizing p bits h with
  | nil =>
    simpa only [program,states,accumulate,List.length_nil,zero_mul,Nat.cast_zero,add_zero] using
      skip_hoare (by decide : 0<6) (boundary p g h ds)
  | cons w ws ih =>
    have hfirst : ∀ i<n,g (h+i)=bitSymbol (bits i) := by
      intro i hi
      apply hb i
      simp only [List.length_cons]; nlinarith
    have hrest : ∀ i<ws.length*n,g (h+n+i)=bitSymbol (bits (n+i)) := by
      intro i hi
      have hh := hb (n+i) (by simp only [List.length_cons]; nlinarith)
      simpa only [Nat.cast_add,add_assoc] using hh
    have hr := (block_runs w p bits g h ds n hn hfirst).seq
      (ih (scanPhase w p bits n) (fun i => bits (n+i)) (h+n) hrest)
    apply hr.consequence (fun _ hv => hv) _ (by simp only [List.length_cons]; nlinarith)
    intro v hv
    simpa only [accumulate,List.length_cons,Nat.add_mul,Nat.cast_add,Nat.cast_mul,
      Nat.cast_one,one_mul,add_mul,add_assoc,add_comm,add_left_comm] using hv

end
end IntegerMultBounds.Machine.RepeatedWeightedPhaseHeader
