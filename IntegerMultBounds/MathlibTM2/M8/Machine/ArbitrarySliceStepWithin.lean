module

public import IntegerMultBounds.Machine.SliceOffsetAdvance
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceCallWithin
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceStep
public import IntegerMultBounds.Machine.RecursiveHeaderBounds
public import IntegerMultBounds.MathlibTM2.M8.Machine.CallReady
public import IntegerMultBounds.MathlibTM2.M8.Machine.RootExecution

/-! The physical offset advance reuses the restored slice bank's head margin;
it does not increase the workspace coefficient of a selected-slice call. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceStepWithin
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceCall (bank data)

open ArbitrarySliceStep

theorem step_within (depth : ℕ) (v : Descriptor) (hs : Fin 6 → List Bool) (ts bs : List Bool) (t b : ℕ)
    (hp : v.Positive) (hv : RecursiveDimensionBank.Headers v hs)
    (ht : Counter.value ts = t) (hb : Counter.value bs = b)
    (ct : GrowingCounterData.Canonical ts) (cb : GrowingCounterData.Canonical bs)
    (hfit : t+b ≤ v.width) (hw : b = Machine.width^depth)
    (hr : roleCount^depth ∣ v.rows)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : CallReady.Ready f p node scalar st)
    (frame : Tapes 1 prime) (hfree : RecursiveViewFrame.Free hs frame)
    (x : Fin (volume prime v) → ZMod 2) (lo hi : ℤ)
    (hmargin : ∀ j, lo+(ArbitrarySliceCallWithin.coefficient*volume prime v : ℕ) ≤
      (bank (data x) hs ts bs f p node scalar st frame).head j ∧
      (bank (data x) hs ts bs f p node scalar st frame).head j+
        (ArbitrarySliceCallWithin.coefficient*volume prime v : ℕ) ≤ hi) :
    HoareWithin program (fun z => z = bank (data x) hs ts bs f p node scalar st frame)
      (fun z => z = bank (data (ArbitraryWidthSliceTranspose.array t b hfit x)) hs
        (GrowingCounterData.advance b ts) bs f p node scalar st frame)
      (cost depth (volume prime v) b ts bs) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  have hc := ArbitrarySliceCallWithin.call_within depth v hs ts bs t b hp hv ht hb ct cb hfit hw hr
    f p node scalar st ready frame hfree x lo hi hmargin
  have ha := SliceOffsetAdvance.advances_hoare
    (ArbitrarySliceCall.rootBank (data (ArbitraryWidthSliceTranspose.array t b hfit x)) hs f p node scalar st)
    ts bs frame b hb
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hp
  have hwV : v.width ≤ volume prime v :=
    RecursiveHeaderBounds.values_le_volume Shared50ModularControl.prime_prime.two_le v hp 3
  have htlen := GrowingCounterData.canonical_width ts ct
  have hblen := GrowingCounterData.canonical_width bs cb
  rw [ht] at htlen
  rw [hb] at hblen
  have htlog := Nat.log2_le_self t
  have hblog := Nat.log2_le_self b
  have hcost : 10*b+2*ts.length+7*bs.length+28 ≤ 56*volume prime v := by omega
  have hbudget : 56*volume prime v ≤ ArbitrarySliceCallWithin.coefficient*volume prime v := by
    dsimp only [ArbitrarySliceCallWithin.coefficient]
    nlinarith only [hV]
  have hwa := HoareWithin.of_time_heads ha lo hi (by
    rintro input rfl j
    change lo+(10*b+2*ts.length+7*bs.length+28 : ℕ) ≤
      (bank (data (ArbitraryWidthSliceTranspose.array t b hfit x)) hs ts bs f p node scalar st frame).head j ∧
      (bank (data (ArbitraryWidthSliceTranspose.array t b hfit x)) hs ts bs f p node scalar st frame).head j+
        (10*b+2*ts.length+7*bs.length+28 : ℕ) ≤ hi
    rw [ArbitrarySliceCallWithin.bank_head_eq (ArbitraryWidthSliceTranspose.array t b hfit x) x
      hs ts bs f p node scalar st frame]
    have hm := hmargin j
    omega)
  exact (hc.seq hwa).consequence (fun _ h => h) (fun _ h => h)
    (by unfold cost; omega) (fun _ h => h)

end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceStepWithin
