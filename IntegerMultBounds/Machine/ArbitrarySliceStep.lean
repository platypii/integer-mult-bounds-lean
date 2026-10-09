import IntegerMultBounds.Machine.SliceOffsetAdvance

/-! One actual piece step executes the selected recursive slice, restores
the parent bank, and physically advances its offset to the next piece. -/
namespace IntegerMultBounds.Machine.ArbitrarySliceStep
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open ArbitrarySliceCall (bank data)

def program := seq ArbitrarySliceCall.program
  (SliceOffsetAdvance.program (T := ArbitrarySliceCall.rootCount) (q := prime))

def cost (depth V b : ℕ) (ts bs : List Bool) :=
  Shared50RecursiveRootExecution.rootBudget depth V+1030*V+
    (10*b+2*ts.length+7*bs.length+28)+1

theorem step_hoare (depth : ℕ) (v : Descriptor) (hs : Fin 6 → List Bool) (ts bs : List Bool) (t b : ℕ)
    (hp : v.Positive) (hv : RecursiveDimensionBank.Headers v hs)
    (ht : Counter.value ts = t) (hb : Counter.value bs = b)
    (ct : GrowingCounterData.Canonical ts) (cb : GrowingCounterData.Canonical bs)
    (hfit : t+b ≤ v.width) (hw : b = 125000^depth)
    (hr : Shared50TapeGlobal.roleCount^depth ∣ v.rows)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Shared50RecursiveCallReady.Ready f p node scalar st)
    (frame : Tapes 1 prime) (hfree : RecursiveViewFrame.Free hs frame)
    (x : Fin (volume prime v) → ZMod 2) :
    HoareTime program (fun z => z = bank (data x) hs ts bs f p node scalar st frame)
      (fun z => z = bank (data (ArbitraryWidthSliceTranspose.array t b hfit x)) hs
        (GrowingCounterData.advance b ts) bs f p node scalar st frame)
      (cost depth (volume prime v) b ts bs) := by
  have hc := ArbitrarySliceCall.call_hoare depth v hs ts bs t b hp hv ht hb ct cb hfit hw hr
    f p node scalar st ready frame hfree x
  have ha := SliceOffsetAdvance.advances_hoare
    (ArbitrarySliceCall.rootBank (data (ArbitraryWidthSliceTranspose.array t b hfit x)) hs f p node scalar st)
    ts bs frame b hb
  exact (hc.seq ha).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

theorem offset_value (ts : List Bool) (t b : ℕ) (ht : Counter.value ts = t) :
    Counter.value (GrowingCounterData.advance b ts) = t+b := by
  rw [GrowingCounterData.advance_value,ht]

theorem offset_canonical (ts : List Bool) (b : ℕ) (ct : GrowingCounterData.Canonical ts) :
    GrowingCounterData.Canonical (GrowingCounterData.advance b ts) :=
  GrowingCounterData.advance_canonical b ts ct

end
end IntegerMultBounds.Machine.ArbitrarySliceStep
