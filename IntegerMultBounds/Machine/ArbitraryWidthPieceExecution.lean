import IntegerMultBounds.Machine.ArbitraryWidthPieceConsume
import IntegerMultBounds.Machine.ArbitraryWidthPiecePrefix

/-! A concrete fixed digit dispatcher: its body executes actual runtime-counted
slice calls and advances the physical depth and width, with no callback trace
supplied as a hypothesis. Initialization and final control erasure are separate. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthPieceExecution
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveChildQuotientsConstant (bits)
open ArbitraryWidthPieceLoop (remaining digit count state emitted)
open ArbitraryWidthPiecePrefix (offset images)
open ArbitrarySliceCall (bank data)

def payload (v : Descriptor) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (frame : Tapes 1 prime) (x : Fin (volume prime v) → ZMod 2) (i : ℕ) :=
  (bank (data (images 125000 v.width v i le_rfl x)) hs
    (bits (offset 125000 v.width i)) (FixedBasePowerStep.bits 125000 i)
    f p node scalar st frame).append (ArbitraryWidthLevelPlacement.extras 125000 i)

def consumeCost (v : Descriptor) (i : ℕ) :=
  ArbitraryWidthPieceConsume.cost i (volume prime v) (125000^i) (digit 125000 v.width i)
    (bits (offset 125000 v.width i)) (FixedBasePowerStep.bits 125000 i)
    (bits (digit 125000 v.width i))

def program := ArbitraryWidthPieceLoop.loop 125000 ArbitraryWidthPieceConsume.program

theorem dispatches (v : Descriptor) (hs : Fin 6 → List Bool) (k : ℕ)
    (hp : v.Positive) (hv : RecursiveDimensionBank.Headers v hs)
    (hwidth : v.width < 125000^(k+1)) (hrows : Shared50TapeGlobal.roleCount^k ∣ v.rows)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Shared50RecursiveCallReady.Ready f p node scalar st)
    (frame : Tapes 1 prime) (hfree : RecursiveViewFrame.Free hs frame)
    (x : Fin (volume prime v) → ZMod 2) :
    HoareTime program
      (fun z => z = state 125000 v.width 0 (payload v hs f p node scalar st frame x 0))
      (fun z => z = state 125000 v.width (count 125000 v.width)
        (payload v hs f p node scalar st frame x (count 125000 v.width)))
      (ArbitraryWidthPieceLoop.overheadConstant 125000*(v.width+1)+
        ∑ i ∈ Finset.range (count 125000 v.width), consumeCost v i) := by
  apply ArbitraryWidthPieceLoop.loop_linear 125000 v.width (by decide)
    ArbitraryWidthPieceConsume.program _ (consumeCost v)
  intro i hi
  have hik := ArbitraryWidthPiecePrefix.selected_depth 125000 v.width i k (by decide) hi hwidth
  have hr : Shared50TapeGlobal.roleCount^i ∣ v.rows :=
    dvd_trans (pow_dvd_pow Shared50TapeGlobal.roleCount hik) hrows
  have h := ArbitraryWidthPieceConsume.consumes i v hs
    (bits (remaining 125000 v.width (i+1))) (bits (offset 125000 v.width i))
    (FixedBasePowerStep.bits 125000 i) (bits (digit 125000 v.width i))
    (offset 125000 v.width i) (125000^i) (digit 125000 v.width i) hp hv
    (RecursiveChildQuotientsConstant.bits_value _) (FixedBasePowerStep.bits_value _ _)
    (RecursiveChildQuotientsConstant.bits_value _)
    (RecursiveChildQuotientsConstant.bits_canonical _) (FixedBasePowerStep.bits_canonical _ _)
    (ArbitraryWidthPiecePrefix.step_fit _ _ _) rfl hr
    f p node scalar st ready frame hfree (images 125000 v.width v i le_rfl x)
  rw [ArbitraryWidthPieceConsume.advance_bits,← ArbitraryWidthPiecePrefix.offset_succ,
    ← ArbitraryWidthPiecePrefix.images_succ] at h
  exact h

theorem final_payload (v : Descriptor) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (frame : Tapes 1 prime) (x : Fin (volume prime v) → ZMod 2) :
    payload v hs f p node scalar st frame x (count 125000 v.width) =
      (bank (data (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)) hs
        (bits v.width) (FixedBasePowerStep.bits 125000 (count 125000 v.width))
        f p node scalar st frame).append
          (ArbitraryWidthLevelPlacement.extras 125000 (count 125000 v.width)) := by
  unfold payload
  rw [ArbitraryWidthPiecePrefix.offset_count _ _ (by decide),
    ArbitraryWidthPiecePrefix.images_count _ _ _ (by decide) rfl]

theorem dispatches_full (v : Descriptor) (hs : Fin 6 → List Bool) (k : ℕ)
    (hp : v.Positive) (hv : RecursiveDimensionBank.Headers v hs)
    (hwidth : v.width < 125000^(k+1)) (hrows : Shared50TapeGlobal.roleCount^k ∣ v.rows)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Shared50RecursiveCallReady.Ready f p node scalar st)
    (frame : Tapes 1 prime) (hfree : RecursiveViewFrame.Free hs frame)
    (x : Fin (volume prime v) → ZMod 2) :
    HoareTime program
      (fun z => z = ArbitraryWidthConsumePlacement.parent (bits v.width)
        (bank (data x) hs (bits 0) (FixedBasePowerStep.bits 125000 0)
          f p node scalar st frame) (ArbitraryWidthLevelPlacement.extras 125000 0))
      (fun z => z = ArbitraryWidthConsumePlacement.parent (bits 0)
        (bank (data (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)) hs
          (bits v.width) (FixedBasePowerStep.bits 125000 (count 125000 v.width))
          f p node scalar st frame)
        (ArbitraryWidthLevelPlacement.extras 125000 (count 125000 v.width)))
      (ArbitraryWidthPieceLoop.overheadConstant 125000*(v.width+1)+
        ∑ i ∈ Finset.range (count 125000 v.width), consumeCost v i) := by
  have h := dispatches v hs k hp hv hwidth hrows f p node scalar st ready frame hfree x
  have hin : state 125000 v.width 0 (payload v hs f p node scalar st frame x 0) =
      ArbitraryWidthConsumePlacement.parent (bits v.width)
        (bank (data x) hs (bits 0) (FixedBasePowerStep.bits 125000 0)
          f p node scalar st frame) (ArbitraryWidthLevelPlacement.extras 125000 0) := by
    simp only [state,payload,remaining,pow_zero,Nat.div_one,
      ArbitraryWidthPiecePrefix.images_zero,ArbitraryWidthPiecePrefix.offset_zero]
    rfl
  rw [hin] at h
  unfold state at h
  rw [ArbitraryWidthPieceLoop.exit _ _ (by decide),final_payload] at h
  exact h

end
end IntegerMultBounds.Machine.ArbitraryWidthPieceExecution
