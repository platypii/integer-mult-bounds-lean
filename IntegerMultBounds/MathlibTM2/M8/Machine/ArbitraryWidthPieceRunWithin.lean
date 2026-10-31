module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieceRun
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieceCost
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieceExecutionWithin

/-! Paid setup and cleanup surround the bounded runtime digit dispatcher.
Preparation uses actual head travel once; recovery uses the exact restored bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieceRunWithin
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveChildQuotientsConstant (bits)
open ArbitraryWidthPieceLoop (count)

open ArbitraryWidthPieceRun

def setupCoefficient : ℕ := RecursiveChildQuotientsConstant.cost Machine.width+
  RecursiveChildQuotientsConstant.cost 1+2*RecursiveChildQuotientsConstant.cost 0+13

def cleanupCoefficient : ℕ := 2*(2*(bits Machine.width).length+20)*Machine.width+14

def coefficient : ℕ := max (setupCoefficient+ArbitraryWidthPieceExecutionWithin.coefficient) (2*cleanupCoefficient)

theorem runs_within (v : Descriptor) (hs : Fin 6 → List Bool) (k : ℕ)
    (hp : v.Positive) (hv : RecursiveDimensionBank.Headers v hs)
    (hwidth : v.width < Machine.width^(k+1)) (hrows : roleCount^k ∣ v.rows)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : CallReady.Ready f p node scalar st)
    (frame : Tapes 1 prime) (hfree : RecursiveViewFrame.Free hs frame)
    (x : Fin (volume prime v) → ZMod 2) (lo hi : ℤ)
    (hmargin : ∀ j, lo+(coefficient*volume prime v : ℕ) ≤
      (ArbitraryWidthPieceSetup.input (ArbitraryWidthPieceSetup.bare
        (ArbitrarySliceCall.rootBank (ArbitrarySliceCall.data x) hs f p node scalar st) frame)).head j ∧
      (ArbitraryWidthPieceSetup.input (ArbitraryWidthPieceSetup.bare
        (ArbitrarySliceCall.rootBank (ArbitrarySliceCall.data x) hs f p node scalar st) frame)).head j+
        (coefficient*volume prime v : ℕ) ≤ hi) :
    HoareWithin program
      (fun z => z = ArbitraryWidthPieceSetup.input
        (ArbitraryWidthPieceSetup.bare (ArbitrarySliceCall.rootBank (ArbitrarySliceCall.data x)
          hs f p node scalar st) frame))
      (fun z => z = ArbitraryWidthPieceSetup.input
        (ArbitraryWidthPieceSetup.bare (ArbitrarySliceCall.rootBank
          (ArbitrarySliceCall.data (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x))
          hs f p node scalar st) frame)) (cost v hs) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  have hs0 := ArbitraryWidthPieceSetup.sets_up v hs hv (ArbitrarySliceCall.data x)
    f p node scalar st frame
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hp
  have hwV : v.width ≤ volume prime v :=
    RecursiveHeaderBounds.values_le_volume Shared50ModularControl.prime_prime.two_le v hp 3
  have hheader := RecursiveRowsNode.header_length v hp hs hv 3
  have hsBound : 2*(hs 3).length+RecursiveChildQuotientsConstant.cost Machine.width+
      RecursiveChildQuotientsConstant.cost 1+2*RecursiveChildQuotientsConstant.cost 0+9 ≤
      setupCoefficient*volume prime v := by
    dsimp only [setupCoefficient]
    nlinarith only [hheader,hV]
  have hreserve : setupCoefficient*volume prime v+ArbitraryWidthPieceExecutionWithin.coefficient*volume prime v ≤
      coefficient*volume prime v := by
    have h := Nat.mul_le_mul_right (volume prime v)
      (show setupCoefficient+ArbitraryWidthPieceExecutionWithin.coefficient ≤ coefficient from le_max_left _ _)
    rwa [Nat.add_mul] at h
  have hprepared : ∀ j, lo+(ArbitraryWidthPieceExecutionWithin.coefficient*volume prime v : ℕ) ≤
      (ArbitraryWidthConsumePlacement.parent (bits v.width)
        (ArbitrarySliceCall.bank (ArbitrarySliceCall.data x) hs (bits 0) (FixedBasePowerStep.bits Machine.width 0)
          f p node scalar st frame) (ArbitraryWidthLevelPlacement.extras Machine.width 0)).head j ∧
      (ArbitraryWidthConsumePlacement.parent (bits v.width)
        (ArbitrarySliceCall.bank (ArbitrarySliceCall.data x) hs (bits 0) (FixedBasePowerStep.bits Machine.width 0)
          f p node scalar st frame) (ArbitraryWidthLevelPlacement.extras Machine.width 0)).head j+
        (ArbitraryWidthPieceExecutionWithin.coefficient*volume prime v : ℕ) ≤ hi := by
    intro j
    have ht := hs0.head_change j
    have hm := hmargin j
    omega
  have hws := HoareWithin.of_time_heads hs0 lo hi (by rintro w rfl j; have hm := hmargin j; omega)
  have hd := ArbitraryWidthPieceExecutionWithin.dispatches_full_within v hs k hp hv hwidth hrows
    f p node scalar st ready frame hfree x lo hi hprepared
  have hc := ArbitraryWidthPieceCleanup.cleans Machine.width (count Machine.width v.width) two_le_width
    (bits 0) (bits v.width) (ArbitrarySliceCall.rootBank
      (ArbitrarySliceCall.data (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x))
      hs f p node scalar st) frame
  have hpower := ArbitraryWidthPieceCost.last_power v.width
  have hpV : Machine.width^(count Machine.width v.width) ≤ 2*Machine.width*volume prime v := by
    have h := Nat.mul_le_mul_left Machine.width (show v.width+1 ≤ 2*volume prime v by omega)
    nlinarith only [hpower,h]
  have hbits : (bits v.width).length ≤ 2*volume prime v := by
    have h := ArbitraryWidthPieceCost.bits_length v.width
    omega
  have hzero : (bits 0).length = 0 := by rfl
  have hcBound : (2*(bits Machine.width).length+20)*Machine.width^(count Machine.width v.width)+
      2*(bits v.width).length+2*(bits 0).length+10 ≤ cleanupCoefficient*volume prime v := by
    have h := Nat.mul_le_mul_left (2*(bits Machine.width).length+20) hpV
    rw [hzero]
    dsimp only [cleanupCoefficient]
    nlinarith only [h,hbits,hV]
  have hcleanup := Nat.mul_le_mul_right (volume prime v)
    (show 2*cleanupCoefficient ≤ coefficient from le_max_right _ _)
  rw [Nat.mul_assoc] at hcleanup
  have hroot := ArbitrarySliceCallWithin.rootBank_head_eq
    (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x) x hs f p node scalar st
  have hbare := Tapes.append_head_congr _ _ ((SharedBank.empty 11 prime).append frame)
    ((SharedBank.empty 11 prime).append frame) hroot rfl
  have hinput := Tapes.append_head_congr (SharedBank.empty 14 prime) (SharedBank.empty 14 prime)
    _ _ rfl (Tapes.append_head_congr _ _ (SharedBank.empty 6 prime) (SharedBank.empty 6 prime) hbare rfl)
  change (ArbitraryWidthPieceSetup.input (ArbitraryWidthPieceSetup.bare
    (ArbitrarySliceCall.rootBank (ArbitrarySliceCall.data (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x))
      hs f p node scalar st) frame)).head =
    (ArbitraryWidthPieceSetup.input (ArbitraryWidthPieceSetup.bare
      (ArbitrarySliceCall.rootBank (ArbitrarySliceCall.data x) hs f p node scalar st) frame)).head at hinput
  have hwc := HoareWithin.of_time_post_heads hc lo hi (by
    rintro w rfl j
    rw [hinput]
    have hm := hmargin j
    omega)
  exact ((hws.seq hd).seq hwc).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega) (fun _ h => h)

end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieceRunWithin
