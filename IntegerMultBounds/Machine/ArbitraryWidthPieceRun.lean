import IntegerMultBounds.Machine.ArbitraryWidthPieceExecution
import IntegerMultBounds.Machine.ArbitraryWidthPieceCleanup

/-! The entire runtime piece dispatcher, including physical control synthesis
from retained parent headers and complete private-control erasure. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthPieceRun
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveChildQuotientsConstant (bits)
open ArbitraryWidthPieceLoop (count)

def program := seq (seq ArbitraryWidthPieceSetup.program ArbitraryWidthPieceExecution.program)
  ArbitraryWidthPieceCleanup.program

def cost (v : Descriptor) (hs : Fin 6 → List Bool) :=
  (2*(hs 3).length+RecursiveChildQuotientsConstant.cost 125000+
    RecursiveChildQuotientsConstant.cost 1+2*RecursiveChildQuotientsConstant.cost 0+9)+
  (ArbitraryWidthPieceLoop.overheadConstant 125000*(v.width+1)+
    ∑ i ∈ Finset.range (count 125000 v.width), ArbitraryWidthPieceExecution.consumeCost v i)+
  ((2*(bits 125000).length+20)*125000^(count 125000 v.width)+
    2*(bits v.width).length+2*(bits 0).length+10)+2

theorem runs (v : Descriptor) (hs : Fin 6 → List Bool) (k : ℕ)
    (hp : v.Positive) (hv : RecursiveDimensionBank.Headers v hs)
    (hwidth : v.width < 125000^(k+1)) (hrows : Shared50TapeGlobal.roleCount^k ∣ v.rows)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Shared50RecursiveCallReady.Ready f p node scalar st)
    (frame : Tapes 1 prime) (hfree : RecursiveViewFrame.Free hs frame)
    (x : Fin (volume prime v) → ZMod 2) :
    HoareTime program
      (fun z => z = ArbitraryWidthPieceSetup.input
        (ArbitraryWidthPieceSetup.bare (ArbitrarySliceCall.rootBank (ArbitrarySliceCall.data x)
          hs f p node scalar st) frame))
      (fun z => z = ArbitraryWidthPieceSetup.input
        (ArbitraryWidthPieceSetup.bare (ArbitrarySliceCall.rootBank
          (ArbitrarySliceCall.data (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x))
          hs f p node scalar st) frame)) (cost v hs) := by
  have hs0 := ArbitraryWidthPieceSetup.sets_up v hs hv (ArbitrarySliceCall.data x)
    f p node scalar st frame
  have hd := ArbitraryWidthPieceExecution.dispatches_full v hs k hp hv hwidth hrows
    f p node scalar st ready frame hfree x
  have hc := ArbitraryWidthPieceCleanup.cleans 125000 (count 125000 v.width) (by decide)
    (bits 0) (bits v.width) (ArbitrarySliceCall.rootBank
      (ArbitrarySliceCall.data (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x))
      hs f p node scalar st) frame
  exact ((hs0.seq hd).seq hc).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

end
end IntegerMultBounds.Machine.ArbitraryWidthPieceRun
