import IntegerMultBounds.Machine.SparseWeightedUnitPhase
import IntegerMultBounds.Machine.UnitPhaseFlagsLifecycle

/-! Sparse address extraction and accumulation, without coefficient arithmetic.
The physical flags are initialized once and retained for a whole polynomial. -/
namespace IntegerMultBounds.Machine.SparsePhaseFlags
noncomputable section
open UnitPhaseNumerator (flags)
open SparseWeightedUnitPhase (selected)
open SelectedSourceBitsCore (payload)
open SelectedSourceBitsScan (word)
open SelectedSourceBitsBank (raw)

def initial (addr : List Bool) (hs : Fin 3 → List Bool) : Tapes 10 2 :=
  (SparseSourceBitsRun.input addr hs).append (SharedBank.empty 2 2)
def input (addr : List Bool) (hs : Fin 3 → List Bool) : Tapes 10 2 :=
  (SparseSourceBitsRun.input addr hs).append (flags 0)
def extracted (addr : List Bool) (hs : Fin 3 → List Bool) (q rho n : ℕ) : Tapes 10 2 :=
  (SparseSourceBitsRun.output addr hs q rho n).append (flags 0)
def output (ws : List (ZMod 4)) (addr : List Bool) (hs : Fin 3 → List Bool) (q rho n : ℕ) : Tapes 10 2 :=
  let bs := selected addr q rho n
  (raw (payload (word addr) (word bs) 0 bs.length) hs).append
    (flags (WeightedPhaseAccumulator.accumulate 0 ws bs))

def flagsPlacement : Fin (2+8) ≃ Fin 10 where
  toFun := ![8,9,0,1,2,3,4,5,6,7]
  invFun := ![2,3,4,5,6,7,8,9,0,1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
def placement : Fin (3+7) ≃ Fin 10 where
  toFun := ![8,9,1,0,2,3,4,5,6,7]
  invFun := ![3,2,4,5,6,7,8,9,0,1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def prepare := Placement.placed UnitPhaseFlagsLifecycle.prepare flagsPlacement
def extractor := extend (SparseSourceBitsRun.program (a := 2)) 2
def accumulator (ws : List (ZMod 4)) := Placement.placed (WeightedPhaseAccumulator.program ws) placement
def program (ws : List (ZMod 4)) := seq (seq prepare extractor) (accumulator ws)

private theorem placed {t u n q B : ℕ} (M : Program t q 2) (e : Fin (t+u) ≃ Fin n)
    (v w : Tapes t 2) (before after : Tapes n 2) (h : HoareTime M (fun x => x=v) (fun x => x=w) B)
    (hb : Placement.active e before=v) (ha : Placement.active e after=w)
    (hf : Placement.extra e before=Placement.extra e after) :
    HoareTime (Placement.placed M e) (fun x => x=before) (fun x => x=after) B := by
  apply (Placement.hoare_at h e before hb).consequence (fun _ h => h) _ le_rfl
  rintro x ⟨small,rfl,rfl⟩
  rw [Placement.replace,hf]
  exact (congrArg (fun z => Placement.combine e z (Placement.extra e after)) ha.symm).trans (Placement.view e after)

theorem prepare_runs (addr : List Bool) (hs : Fin 3 → List Bool) :
    HoareTime prepare (fun z => z=initial addr hs) (fun z => z=input addr hs) 1 := by
  apply placed _ _ _ _ _ _ UnitPhaseFlagsLifecycle.prepares
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem extractor_runs (addr : List Bool) (hs : Fin 3 → List Bool) (q rho n : ℕ)
    (hspan : rho+n*q<addr.length) (hpos : 1≤q)
    (hq : Counter.value (hs 0)=q) (hn : Counter.value (hs 1)=n) (hr : Counter.value (hs 2)=rho)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i)) :
    HoareTime extractor (fun z => z=input addr hs) (fun z => z=extracted addr hs q rho n)
      (400*(addr.length+1)) :=
  hoare_extend_eq (SparseSourceBitsRun.runs_linear addr hs q rho n hspan hpos hq hn hr hc) (flags 0)

theorem accumulator_runs (ws : List (ZMod 4)) (addr : List Bool) (hs : Fin 3 → List Bool)
    (q rho n : ℕ) (hl : n+1=ws.length) :
    HoareTime (accumulator ws) (fun z => z=extracted addr hs q rho n)
      (fun z => z=output ws addr hs q rho n) (2*ws.length) := by
  apply placed _ _ _ _ _ _ (WeightedPhaseAccumulator.word_runs 0 ws (selected addr q rho n)
    (by simpa only [selected,SelectedSourceBitsData.selected_length] using hl))
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem runs (ws : List (ZMod 4)) (addr : List Bool) (hs : Fin 3 → List Bool) (q rho n : ℕ)
    (hl : n+1=ws.length) (hspan : rho+n*q<addr.length) (hpos : 1≤q)
    (hq : Counter.value (hs 0)=q) (hn : Counter.value (hs 1)=n) (hr : Counter.value (hs 2)=rho)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i)) :
    HoareTime (program ws) (fun z => z=initial addr hs) (fun z => z=output ws addr hs q rho n)
      (400*(addr.length+1)+2*ws.length+3) :=
  (((prepare_runs addr hs).seq (extractor_runs addr hs q rho n hspan hpos hq hn hr hc)).seq
    (accumulator_runs ws addr hs q rho n hl)).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.SparsePhaseFlags
