import IntegerMultBounds.Machine.WeightedPhaseAccumulator
import IntegerMultBounds.Machine.UnitPhaseSigned

/-! The actual weighted-control scanner feeds its physical two-bit readout
straight into the four-way signed coefficient kernel. No phase-result flag is
supplied to the composed program. -/
namespace IntegerMultBounds.Machine.WeightedUnitPhase
noncomputable section
open WeightedPhaseAccumulator (accumulate weightedSum)
open UnitPhaseNumerator (flags coreInput coreOutput)
open MarkedWordCleanup (one)

def controlTape (bs : List Bool) (h : ℤ) : Tapes 1 2 :=
  one (putWord (fun _ => blank) 0 (bs.map bitSymbol)) h

def input (bs : List Bool) (xs : ℕ → List (Fin 2)) : Tapes 9 2 :=
  (flags 0).append ((controlTape bs 0).append (coreInput xs))
def intermediate (ws : List (ZMod 4)) (bs : List Bool) (xs : ℕ → List (Fin 2)) : Tapes 9 2 :=
  (flags (accumulate 0 ws bs)).append ((controlTape bs bs.length).append (coreInput xs))
def output (ws : List (ZMod 4)) (bs : List Bool) (xs : ℕ → List (Fin 2)) : Tapes 9 2 :=
  (flags (accumulate 0 ws bs)).append ((controlTape bs bs.length).append (coreOutput (accumulate 0 ws bs) xs))

def accumulator (ws : List (ZMod 4)) := Placement.placed (WeightedPhaseAccumulator.program ws)
  (SharedControlPair.leftPlacement 2 1 6)
def multiplier := Placement.placed UnitPhaseNumerator.program (SharedControlPair.rightPlacement 2 1 6)
def program (ws : List (ZMod 4)) := seq (accumulator ws) multiplier

private theorem placed {t u n q B : ℕ} (M : Program t q 2) (e : Fin (t+u) ≃ Fin n)
    (v w : Tapes t 2) (before after : Tapes n 2) (h : HoareTime M (fun x => x=v) (fun x => x=w) B)
    (hb : Placement.active e before=v) (ha : Placement.active e after=w)
    (hf : Placement.extra e before=Placement.extra e after) :
    HoareTime (Placement.placed M e) (fun x => x=before) (fun x => x=after) B := by
  apply (Placement.hoare_at h e before hb).consequence (fun _ h => h) _ le_rfl
  rintro x ⟨small,rfl,rfl⟩
  rw [Placement.replace,hf]
  exact (congrArg (fun z => Placement.combine e z (Placement.extra e after)) ha.symm).trans (Placement.view e after)

theorem accumulator_runs (ws : List (ZMod 4)) (bs : List Bool) (hl : bs.length=ws.length)
    (xs : ℕ → List (Fin 2)) :
    HoareTime (accumulator ws) (fun v => v=input bs xs) (fun v => v=intermediate ws bs xs) (2*ws.length) := by
  apply placed _ _ _ _ _ _ (WeightedPhaseAccumulator.word_runs 0 ws bs hl)
  · exact SharedControlPair.left_active _ _ _
  · exact SharedControlPair.left_active _ _ _
  · rw [input,intermediate,SharedControlPair.left_extra,SharedControlPair.left_extra]

theorem multiplier_runs (ws : List (ZMod 4)) (bs : List Bool) (xs : ℕ → List (Fin 2))
    (b : ℕ) (hw : ∀ j,(xs j).length=b) :
    HoareTime multiplier (fun v => v=intermediate ws bs xs) (fun v => v=output ws bs xs) (12*b+45) := by
  apply placed _ _ _ _ _ _ (UnitPhaseNumerator.runs (accumulate 0 ws bs) xs b hw)
  · exact SharedControlPair.right_active _ _ _
  · exact SharedControlPair.right_active _ _ _
  · rw [intermediate,output,SharedControlPair.right_extra,SharedControlPair.right_extra]

theorem runs (ws : List (ZMod 4)) (bs : List Bool) (hl : bs.length=ws.length)
    (xs : ℕ → List (Fin 2)) (b : ℕ) (hw : ∀ j,(xs j).length=b) :
    HoareTime (program ws) (fun v => v=input bs xs) (fun v => v=output ws bs xs) (2*ws.length+12*b+46) :=
  ((accumulator_runs ws bs hl xs).seq (multiplier_runs ws bs xs b hw)).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

theorem phase_correct (ws : List (ZMod 4)) (bs : List Bool) (hl : bs.length=ws.length)
    (xs : ℕ → List (Fin 2)) (b n : ℕ) (hw : ∀ j,(xs j).length=b+1)
    (hguard : ∀ j : Fin 2,|ButterflySigned.signedValue b (xs j.val)|<(2^b : ℕ)) :
    ButterflySigned.complexValue
      (ButterflySigned.signedValue b (UnitPhaseNumerator.words (accumulate 0 ws bs) 0 xs))
      (ButterflySigned.signedValue b (UnitPhaseNumerator.words (accumulate 0 ws bs) 1 xs)) n=
      Networks.BinaryPhase.phase (weightedSum ws bs)*
        ButterflySigned.complexValue (ButterflySigned.signedValue b (xs 0)) (ButterflySigned.signedValue b (xs 1)) n := by
  rw [UnitPhaseSigned.words_phase _ xs b n hw hguard,WeightedPhaseAccumulator.accumulate_cast _ _ _ hl]
  simp

end
end IntegerMultBounds.Machine.WeightedUnitPhase
