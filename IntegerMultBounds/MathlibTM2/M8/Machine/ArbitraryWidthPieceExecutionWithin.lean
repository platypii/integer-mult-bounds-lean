module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieceExecution
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieceConsumeWithin

/-! The actual runtime digit dispatcher shares one root-volume head reserve.
Counter extraction is linear, while nonlinear slice calls use their prefix bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieceExecutionWithin
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveChildQuotientsConstant (bits)
open ArbitraryWidthPieceLoop (remaining digit count state emitted)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPiecePrefix (offset images)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceCall (bank data)

open ArbitraryWidthPieceExecution

def coefficient : ℕ := max (ArbitraryWidthPieceConsumeWithin.coefficient+1)
  (2*ArbitraryWidthPieceCounter.stageConstant Machine.width)

theorem dispatches_within (v : Descriptor) (hs : Fin 6 → List Bool) (k : ℕ)
    (hp : v.Positive) (hv : RecursiveDimensionBank.Headers v hs)
    (hwidth : v.width < Machine.width^(k+1)) (hrows : roleCount^k ∣ v.rows)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : CallReady.Ready f p node scalar st)
    (frame : Tapes 1 prime) (hfree : RecursiveViewFrame.Free hs frame)
    (x : Fin (volume prime v) → ZMod 2) (lo hi : ℤ)
    (hmargin : ∀ j, lo+(coefficient*volume prime v : ℕ) ≤
      (state Machine.width v.width 0 (payload v hs f p node scalar st frame x 0)).head j ∧
      (state Machine.width v.width 0 (payload v hs f p node scalar st frame x 0)).head j+
        (coefficient*volume prime v : ℕ) ≤ hi) :
    HoareWithin program
      (fun z => z = state Machine.width v.width 0 (payload v hs f p node scalar st frame x 0))
      (fun z => z = state Machine.width v.width (count Machine.width v.width)
        (payload v hs f p node scalar st frame x (count Machine.width v.width)))
      (ArbitraryWidthPieceLoop.overheadConstant Machine.width*(v.width+1)+
        ∑ i ∈ Finset.range (count Machine.width v.width), consumeCost v i) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hp
  have hwV : v.width ≤ volume prime v :=
    RecursiveHeaderBounds.values_le_volume Shared50ModularControl.prime_prime.two_le v hp 3
  have hPayload (i : ℕ) : (payload v hs f p node scalar st frame x i).head =
      (payload v hs f p node scalar st frame x 0).head := by
    exact Tapes.append_head_congr _ _ _ _
      (ArbitrarySliceCallWithin.bank_offset_head_eq (images Machine.width v.width v i le_rfl x)
        (images Machine.width v.width v 0 le_rfl x) hs
        (bits (offset Machine.width v.width i)) (FixedBasePowerStep.bits Machine.width i)
        (bits (offset Machine.width v.width 0)) (FixedBasePowerStep.bits Machine.width 0)
        f p node scalar st frame) rfl
  have hParent (ns : List Bool) (i : ℕ) :
      (ArbitraryWidthConsumePlacement.parent ns
        (bank (data (images Machine.width v.width v i le_rfl x)) hs
          (bits (offset Machine.width v.width i)) (FixedBasePowerStep.bits Machine.width i)
          f p node scalar st frame) (ArbitraryWidthLevelPlacement.extras Machine.width i)).head =
      (state Machine.width v.width 0 (payload v hs f p node scalar st frame x 0)).head := by
    exact Tapes.append_head_congr _ _ _ _ (by rfl) (hPayload i)
  have hState (i : ℕ) : (state Machine.width v.width i (payload v hs f p node scalar st frame x i)).head =
      (state Machine.width v.width 0 (payload v hs f p node scalar st frame x 0)).head :=
    hParent (bits (remaining Machine.width v.width i)) i
  have hCBudget : ArbitraryWidthPieceConsumeWithin.coefficient*volume prime v+1 ≤ coefficient*volume prime v := by
    have h := Nat.mul_le_mul_right (volume prime v)
      (show ArbitraryWidthPieceConsumeWithin.coefficient+1 ≤ coefficient from le_max_left _ _)
    nlinarith only [h,hV]
  have hloop := ArbitraryWidthPieceLoop.loop_within Machine.width v.width two_le_width
    ArbitraryWidthPieceConsume.program (payload v hs f p node scalar st frame x) (consumeCost v)
    (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi)
    (by intro j; have hm := hmargin j; omega)
    (by
      intro i hlt
      have ht := hoare_extend_eq (ArbitraryWidthPieceCounter.stage_hoare (a := prime) Machine.width two_le_width
        (bits (remaining Machine.width v.width i))) (payload v hs f p node scalar st frame x i)
      simp only [RecursiveChildQuotientsConstant.bits_value,ArbitraryWidthPieceLoop.remaining_succ] at ht
      have hr : remaining Machine.width v.width i+1 ≤ 2*volume prime v := by
        have h := Nat.div_le_self v.width (Machine.width^i)
        change remaining Machine.width v.width i ≤ v.width at h
        omega
      have hlinear := ArbitraryWidthPieceCounter.stageCost_linear Machine.width (bits (remaining Machine.width v.width i))
        (RecursiveChildQuotientsConstant.bits_canonical _)
      rw [RecursiveChildQuotientsConstant.bits_value] at hlinear
      have hb := Nat.mul_le_mul_left (ArbitraryWidthPieceCounter.stageConstant Machine.width) hr
      have hc := Nat.mul_le_mul_right (volume prime v)
        (show 2*ArbitraryWidthPieceCounter.stageConstant Machine.width ≤ coefficient from le_max_right _ _)
      have hcost : ArbitraryWidthPieceCounter.stageCost Machine.width (bits (remaining Machine.width v.width i)) ≤
          coefficient*volume prime v := by nlinarith only [hlinear,hb,hc]
      apply HoareWithin.of_time_heads ht lo hi
      rintro w rfl j
      change lo+_ ≤ (state Machine.width v.width i (payload v hs f p node scalar st frame x i)).head j ∧
        (state Machine.width v.width i (payload v hs f p node scalar st frame x i)).head j+_ ≤ hi
      rw [hState i]
      have hm := hmargin j
      omega)
    (by
      intro i hlt
      have hik := ArbitraryWidthPiecePrefix.selected_depth Machine.width v.width i k two_le_width hlt hwidth
      have hr : roleCount^i ∣ v.rows := dvd_trans (pow_dvd_pow roleCount hik) hrows
      have h := ArbitraryWidthPieceConsumeWithin.consumes_within i v hs
        (bits (remaining Machine.width v.width (i+1))) (bits (offset Machine.width v.width i))
        (FixedBasePowerStep.bits Machine.width i) (bits (digit Machine.width v.width i))
        (offset Machine.width v.width i) (Machine.width^i) (digit Machine.width v.width i) hp hv
        (RecursiveChildQuotientsConstant.bits_value _) (FixedBasePowerStep.bits_value _ _)
        (RecursiveChildQuotientsConstant.bits_value _)
        (RecursiveChildQuotientsConstant.bits_canonical _) (FixedBasePowerStep.bits_canonical _ _)
        (RecursiveChildQuotientsConstant.bits_canonical _)
        ((ArbitraryWidthPiecePrefix.selected_power_le Machine.width v.width i two_le_width hlt).trans hwV)
        (ArbitraryWidthPiecePrefix.step_fit _ _ _) rfl hr
        f p node scalar st ready frame hfree (images Machine.width v.width v i le_rfl x) lo hi (by
          intro j
          have hc := ArbitraryWidthConsumePlacement.parent_emitted_heads
            (bits (remaining Machine.width v.width (i+1))) (bits (digit Machine.width v.width i))
            (bank (data (images Machine.width v.width v i le_rfl x)) hs
              (bits (offset Machine.width v.width i)) (FixedBasePowerStep.bits Machine.width i)
              f p node scalar st frame)
            _ (ArbitraryWidthLevelPlacement.extras Machine.width i) rfl j
          rw [hParent] at hc
          have hm := hmargin j
          omega)
      rw [ArbitraryWidthPieceConsume.advance_bits,← ArbitraryWidthPiecePrefix.offset_succ,
        ← ArbitraryWidthPiecePrefix.images_succ] at h
      exact h)
  apply HoareWithin.of_time_invariant (dispatches v hs k hp hv hwidth hrows f p node scalar st ready frame hfree x)
  intro c hc
  exact hloop.invariant hc

theorem dispatches_full_within (v : Descriptor) (hs : Fin 6 → List Bool) (k : ℕ)
    (hp : v.Positive) (hv : RecursiveDimensionBank.Headers v hs)
    (hwidth : v.width < Machine.width^(k+1)) (hrows : roleCount^k ∣ v.rows)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : CallReady.Ready f p node scalar st)
    (frame : Tapes 1 prime) (hfree : RecursiveViewFrame.Free hs frame)
    (x : Fin (volume prime v) → ZMod 2) (lo hi : ℤ)
    (hmargin : ∀ j, lo+(coefficient*volume prime v : ℕ) ≤
      (ArbitraryWidthConsumePlacement.parent (bits v.width)
        (bank (data x) hs (bits 0) (FixedBasePowerStep.bits Machine.width 0)
          f p node scalar st frame) (ArbitraryWidthLevelPlacement.extras Machine.width 0)).head j ∧
      (ArbitraryWidthConsumePlacement.parent (bits v.width)
        (bank (data x) hs (bits 0) (FixedBasePowerStep.bits Machine.width 0)
          f p node scalar st frame) (ArbitraryWidthLevelPlacement.extras Machine.width 0)).head j+
        (coefficient*volume prime v : ℕ) ≤ hi) :
    HoareWithin program
      (fun z => z = ArbitraryWidthConsumePlacement.parent (bits v.width)
        (bank (data x) hs (bits 0) (FixedBasePowerStep.bits Machine.width 0)
          f p node scalar st frame) (ArbitraryWidthLevelPlacement.extras Machine.width 0))
      (fun z => z = ArbitraryWidthConsumePlacement.parent (bits 0)
        (bank (data (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)) hs
          (bits v.width) (FixedBasePowerStep.bits Machine.width (count Machine.width v.width))
          f p node scalar st frame)
        (ArbitraryWidthLevelPlacement.extras Machine.width (count Machine.width v.width)))
      (ArbitraryWidthPieceLoop.overheadConstant Machine.width*(v.width+1)+
        ∑ i ∈ Finset.range (count Machine.width v.width), consumeCost v i) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  have hin : state Machine.width v.width 0 (payload v hs f p node scalar st frame x 0) =
      ArbitraryWidthConsumePlacement.parent (bits v.width)
        (bank (data x) hs (bits 0) (FixedBasePowerStep.bits Machine.width 0)
          f p node scalar st frame) (ArbitraryWidthLevelPlacement.extras Machine.width 0) := by
    simp only [state,payload,remaining,pow_zero,Nat.div_one,
      ArbitraryWidthPiecePrefix.images_zero,ArbitraryWidthPiecePrefix.offset_zero]
    rfl
  have h := dispatches_within v hs k hp hv hwidth hrows f p node scalar st ready frame hfree x lo hi
    (by rw [hin]; exact hmargin)
  rw [hin] at h
  unfold state at h
  rw [ArbitraryWidthPieceLoop.exit _ _ two_le_width,final_payload] at h
  exact h

end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieceExecutionWithin
