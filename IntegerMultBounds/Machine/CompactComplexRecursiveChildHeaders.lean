import IntegerMultBounds.Machine.CompactComplexChildHeadersBudget
import IntegerMultBounds.Machine.CompactComplexLeafHeadersData
import IntegerMultBounds.Machine.CompactComplexChildHeaderFrames
import IntegerMultBounds.Networks.ComplexRecursiveCallSchema

/-! Every literal residual-coordinate call uses its actual schema slot for
paid physical child-header preparation. Internal and scalar children have
separate contracts, and both retain the selected role's row count. -/
namespace IntegerMultBounds.Machine.CompactComplexRecursiveChildHeaders
noncomputable section
open CompactComplexRecursiveGeometry
open CompactGadgetReservationShape (Shape)
open Networks.BinaryRowProgram (Op)
open Networks.ComplexRecursiveCallSchema (Call)
variable {a : ℕ} {s : Shape} (rho : Fin s.chunk) {left k : ℕ}
  (hactive : s.active ≤ s.axes) (pair : Op (Fin arity)) (call : Call) (rows : ℕ)

/-- A literal schema occurrence contributes its selected residual slot;
equal label pairs at different occurrences remain distinct calls. -/
def internalProgram (call : Call) := CompactComplexChildHeadersData.placedProgram (a := a) call.slot

theorem internal_runs (visit : Visit s.active left (k+2)) (tail : Tapes 23 a) :
    HoareTime (internalProgram (a := a) call)
      (fun x => x = (ActiveRepairRankHeadersCommands.bank (ActivePrefixStageHeadersData.initial
        (CompactComplexChildHeadersData.parent rho visit hactive pair) rows)).append tail)
      (fun x => x = (ActiveRepairRankHeadersCommands.bank (ActivePrefixStageHeadersData.initial
        (CompactComplexChildHeadersData.child rho visit hactive pair call.slot) rows)).append tail)
      (CompactChildHeadersArithmetic.scheduleCost (CompactComplexChildHeadersData.schedule call.slot)
        (ActivePrefixStageHeadersData.initial
          (CompactComplexChildHeadersData.parent rho visit hactive pair) rows)) :=
  CompactComplexChildHeadersData.runs_framed rho visit hactive pair call.slot rows tail

def leafProgram (call : Call) := CompactComplexLeafHeadersData.placedProgram (a := a) call.slot.val

theorem leaf_runs (visit : Visit s.active left 1) (tail : Tapes 23 a) :
    HoareTime (leafProgram (a := a) call)
      (fun x => x = (ActiveRepairRankHeadersCommands.bank (ActivePrefixStageHeadersData.initial
        (CompactComplexLeafHeadersData.parent rho visit hactive pair) rows)).append tail)
      (fun x => x = (ActiveRepairRankHeadersCommands.bank
        (CompactComplexLeafHeadersData.leaf rho call.slot rows pair left)).append tail)
      (CompactChildHeadersArithmetic.scheduleCost (CompactComplexLeafHeadersData.schedule call.slot.val)
        (ActivePrefixStageHeadersData.initial
          (CompactComplexLeafHeadersData.parent rho visit hactive pair) rows)) :=
  CompactComplexLeafHeadersData.runs_framed rho visit hactive pair call.slot rows tail

end
end IntegerMultBounds.Machine.CompactComplexRecursiveChildHeaders
