import IntegerMultBounds.Machine.SparseSourceBitsRun
import IntegerMultBounds.Machine.WeightedUnitPhase

/-! Complete physical sparse-address phase application. The extracted tape
is shared directly with the weighted accumulator; no control word or phase
flag is supplied as input. Original address and descriptors are preserved. -/
namespace IntegerMultBounds.Machine.SparseWeightedUnitPhase
noncomputable section
open SelectedSourceBitsCore (payload)
open SelectedSourceBitsScan (word)
open SelectedSourceBitsBank (raw)
open UnitPhaseNumerator (flags coreInput coreOutput)
open WeightedPhaseAccumulator (accumulate)

def selected (addr : List Bool) (q rho n : ℕ) := SelectedSourceBitsData.selected addr q rho (n+1)
def input (addr : List Bool) (hs : Fin 3 → List Bool) (xs : ℕ → List (Fin 2)) : Tapes 16 2 :=
  (SparseSourceBitsRun.input addr hs).append ((flags 0).append (coreInput xs))
def intermediate (addr : List Bool) (hs : Fin 3 → List Bool) (q rho n : ℕ)
    (xs : ℕ → List (Fin 2)) : Tapes 16 2 :=
  (SparseSourceBitsRun.output addr hs q rho n).append ((flags 0).append (coreInput xs))
def output (ws : List (ZMod 4)) (addr : List Bool) (hs : Fin 3 → List Bool) (q rho n : ℕ)
    (xs : ℕ → List (Fin 2)) : Tapes 16 2 :=
  let bs := selected addr q rho n
  (raw (payload (word addr) (word bs) 0 bs.length) hs).append
    ((flags (accumulate 0 ws bs)).append (coreOutput (accumulate 0 ws bs) xs))

def placement : Fin (9+7) ≃ Fin 16 where
  toFun := ![8,9,1,10,11,12,13,14,15,0,2,3,4,5,6,7]
  invFun := ![9,2,10,11,12,13,14,15,0,1,3,4,5,6,7,8]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
def extractor := extend (SparseSourceBitsRun.program (a := 2)) 8
def multiplier (ws : List (ZMod 4)) := Placement.placed (WeightedUnitPhase.program ws) placement
def program (ws : List (ZMod 4)) := seq extractor (multiplier ws)

theorem extractor_runs (addr : List Bool) (hs : Fin 3 → List Bool) (q rho n : ℕ)
    (xs : ℕ → List (Fin 2)) (hspan : rho+n*q<addr.length) (hpos : 1≤q)
    (hq : Counter.value (hs 0)=q) (hn : Counter.value (hs 1)=n) (hr : Counter.value (hs 2)=rho)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i)) :
    HoareTime extractor (fun v => v=input addr hs xs) (fun v => v=intermediate addr hs q rho n xs)
      (400*(addr.length+1)) :=
  hoare_extend_eq (SparseSourceBitsRun.runs_linear addr hs q rho n hspan hpos hq hn hr hc)
    ((flags 0).append (coreInput xs))

theorem multiplier_runs (ws : List (ZMod 4)) (addr : List Bool) (hs : Fin 3 → List Bool)
    (q rho n : ℕ) (hl : n+1=ws.length) (xs : ℕ → List (Fin 2)) (b : ℕ)
    (hw : ∀ j,(xs j).length=b) :
    HoareTime (multiplier ws) (fun v => v=intermediate addr hs q rho n xs)
      (fun v => v=output ws addr hs q rho n xs) (2*ws.length+12*b+46) := by
  have hsmall := WeightedUnitPhase.runs ws (selected addr q rho n)
    (by simpa only [selected,SelectedSourceBitsData.selected_length] using hl) xs b hw
  have ha : Placement.active placement (intermediate addr hs q rho n xs)=
      WeightedUnitPhase.input (selected addr q rho n) xs := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hb : Placement.active placement (output ws addr hs q rho n xs)=
      WeightedUnitPhase.output ws (selected addr q rho n) xs := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hf : Placement.extra placement (intermediate addr hs q rho n xs)=
      Placement.extra placement (output ws addr hs q rho n xs) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  apply (Placement.hoare_at hsmall placement (intermediate addr hs q rho n xs) ha).consequence
    (fun _ h => h) _ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  rw [Placement.replace,hf]
  exact (congrArg (fun z => Placement.combine placement z
    (Placement.extra placement (output ws addr hs q rho n xs))) hb.symm).trans
      (Placement.view placement (output ws addr hs q rho n xs))

theorem runs (ws : List (ZMod 4)) (addr : List Bool) (hs : Fin 3 → List Bool) (q rho n : ℕ)
    (hl : n+1=ws.length) (xs : ℕ → List (Fin 2)) (b : ℕ) (hw : ∀ j,(xs j).length=b)
    (hspan : rho+n*q<addr.length) (hpos : 1≤q)
    (hq : Counter.value (hs 0)=q) (hn : Counter.value (hs 1)=n) (hr : Counter.value (hs 2)=rho)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i)) :
    HoareTime (program ws) (fun v => v=input addr hs xs) (fun v => v=output ws addr hs q rho n xs)
      (400*(addr.length+1)+2*ws.length+12*b+47) :=
  ((extractor_runs addr hs q rho n xs hspan hpos hq hn hr hc).seq
    (multiplier_runs ws addr hs q rho n hl xs b hw)).consequence
      (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.SparseWeightedUnitPhase
