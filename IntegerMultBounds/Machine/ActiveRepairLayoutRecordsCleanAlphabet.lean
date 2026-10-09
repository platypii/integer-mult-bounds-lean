import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyCleanEarly
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyCleanLateAfter
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsOriginalEarlyAlphabet
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsOriginalLateAlphabet

/-! Complete original-input repairs with all generated metadata erased run
in the payload prime alphabet, preserving exact literal banks and costs. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsCleanAlphabet
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairLayoutRecordsAlphabet
open Networks.Shared50ModularControl (prime)
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

namespace Early

def program := Alphabet.program encoding ActiveRepairLayoutRecordsAssemblyCleanEarly.program
abbrev input (d : Inputs s p offset rows) (cs : List (List Bool)) := ActiveRepairLayoutRecordsOriginalEarlyAlphabet.input d cs
abbrev chunks (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows) :=
  ActiveRepairLayoutRecordsAssemblyOriginalEarly.chunks d array
def output (d : Inputs s p offset rows) (cs : List (List Bool)) :=
  Alphabet.mapTapes encoding (ActiveRepairLayoutRecordsAssemblyCleanEarly.output d cs)

theorem runs_linear (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows)
    (hfit : offset+p.f*p.q≤p.before) (hq3 : p.b+3≤p.q) (hrows : 0<rows)
    (hR : (ActiveRepairLayoutRecordsHeadersData.repair d).geom.addressBits+1≤s.payload) (D : ℕ)
    (hdensity : VaryingControlRepairDensity.earlyDensity p.q p.b p.n*
      ((ActiveRepairLayoutRecordsHeadersData.repair d).geom.addressBits+1)≤D) :
    HoareTime program (fun v => v=input d (chunks d array))
      (fun v => v=output d (chunks d array))
      ((ActiveRepairLayoutRecordsHeadersBudget.constant+ActiveRepairEarlyOriginalPipelineBudget.volumeConstant D+
        ActiveRepairLayoutRecordsBankBudget.eraseConstant+1017)*
        ActiveRepairLayoutRecordsHeadersBudget.volume s rows) :=
  map_hoare_eq (ActiveRepairLayoutRecordsAssemblyCleanEarly.runs_linear d array hfit hq3 hrows hR D hdensity)

theorem output_ideal (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows)
    (hfit : offset+p.f*p.q≤p.before) (hq3 : p.b+3≤p.q) :
    (output d (chunks d array)).tape 223=putWord (fun _ => blank) 0
      ((List.ofFn (ActiveRepairLayoutRecordsMove.move s (p.n*p.b) (p.n*p.q) p.before p.after rows
        p.compactFits p.activeSize
        (ActiveRepairLayoutPermutation.earlyIdeal s p.q p.b p.n p.before p.after rows p.rho offset
          (p.f*p.q) .before (ActiveRepairLayoutKeysEarly.positive (ActiveRepairLayoutRecordsHeadersData.repair d))) array)).map bitSymbol) := by
  change (fun z => encoding.encode ((ActiveRepairLayoutRecordsAssemblyCleanEarly.output d (chunks d array)).tape 223 z))=_
  rw [ActiveRepairLayoutRecordsAssemblyCleanEarly.output_ideal d array hfit hq3]
  exact map_raw _

theorem output_literal (d : Inputs s p offset rows) (cs : List (List Bool)) :
    output d cs=SharedPlacementAlphabet.setTape (input d cs) 223
      ((ActiveRepairLayoutRecordsOriginalEarlyAlphabet.output d cs).tape 223) 0 := by
  unfold output
  rw [ActiveRepairLayoutRecordsAssemblyCleanEarly.output_literal,ActiveTargetHighestLaterBank.map_setTape]
  rfl

end Early

namespace Late

def program := Alphabet.program encoding ActiveRepairLayoutRecordsAssemblyCleanLateAfter.program
abbrev input (d : Inputs s p offset rows) (cs : List (List Bool)) := ActiveRepairLayoutRecordsOriginalLateAlphabet.input d cs
abbrev chunks (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows) :=
  ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.chunks d array
def output (d : Inputs s p offset rows) (cs : List (List Bool)) :=
  Alphabet.mapTapes encoding (ActiveRepairLayoutRecordsAssemblyCleanLateAfter.output d cs)

theorem runs_linear (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows)
    (hfit : offset+p.f*p.q≤p.after) (hq3 : p.b+3≤p.q) (hrows : 0<rows)
    (hR : (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d).geom.addressBits+1≤s.payload) (D : ℕ)
    (hdensity : VaryingControlRepairDensity.lateDensity p.q p.b p.n*
      ((ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d).geom.addressBits+1)≤D) :
    HoareTime program (fun v => v=input d (chunks d array))
      (fun v => v=output d (chunks d array))
      ((ActiveRepairLayoutRecordsHeadersAfterBudget.constant+ActiveRepairLateOriginalPipelineBudget.volumeConstant D+
        ActiveRepairLayoutRecordsBankAfterBudget.eraseConstant+1017)*
        ActiveRepairLayoutRecordsHeadersBudget.volume s rows) :=
  map_hoare_eq (ActiveRepairLayoutRecordsAssemblyCleanLateAfter.runs_linear d array hfit hq3 hrows hR D hdensity)

theorem output_ideal (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows)
    (hfit : offset+p.f*p.q≤p.after) (hq3 : p.b+3≤p.q) :
    (output d (chunks d array)).tape 232=putWord (fun _ => blank) 0
      ((List.ofFn (ActiveRepairLayoutRecordsMove.move s (p.n*p.b) (p.n*p.q) p.before p.after rows
        p.compactFits p.activeSize
        (ActiveRepairLayoutPermutation.lateIdeal s p.q p.b p.n p.before p.after rows p.rho offset
          (p.f*p.q) .after (ActiveRepairLayoutKeysLate.positive (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d))) array)).map bitSymbol) := by
  change (fun z => encoding.encode ((ActiveRepairLayoutRecordsAssemblyCleanLateAfter.output d (chunks d array)).tape 232 z))=_
  rw [ActiveRepairLayoutRecordsAssemblyCleanLateAfter.output_ideal d array hfit hq3]
  exact map_raw _

theorem output_literal (d : Inputs s p offset rows) (cs : List (List Bool)) :
    output d cs=SharedPlacementAlphabet.setTape (input d cs) 232
      ((ActiveRepairLayoutRecordsOriginalLateAlphabet.output d cs).tape 232) 0 := by
  unfold output
  rw [ActiveRepairLayoutRecordsAssemblyCleanLateAfter.output_literal,ActiveTargetHighestLaterBank.map_setTape]
  rfl

end Late

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsCleanAlphabet
