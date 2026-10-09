import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyOriginalLateAfter
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAlphabet

/-! The complete original-input after-source later repair executes in the fixed prime
alphabet with literal binary tapes and unchanged runtime. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsOriginalLateAlphabet
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairLayoutRecordsHeadersData
open ActiveRepairLayoutRecordsAlphabet
open Networks.Shared50ModularControl (prime)
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

abbrev repair (d : Inputs s p offset rows) := ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d

def program := Alphabet.program encoding ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.program

def input (d : Inputs s p offset rows) (chunks : List (List Bool)) :=
  Alphabet.mapTapes encoding (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.input d chunks)
def output (d : Inputs s p offset rows) (chunks : List (List Bool)) :=
  Alphabet.mapTapes encoding (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.output d chunks)
abbrev chunks (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows) :=
  ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.chunks d array

theorem map_original (d : Inputs s p offset rows) :
    Alphabet.mapTapes encoding (ActiveRepairLayoutRecordsHeadersRun.originalInput (a:=1) d)=
      ActiveRepairLayoutRecordsHeadersRun.originalInput (a:=prime) d := by
  unfold ActiveRepairLayoutRecordsHeadersRun.originalInput
  rw [map_append,map_empty]
  apply congrArg (fun v : Tapes 14 prime => v.append (SharedBank.empty 29 prime))
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i
    exact map_binary (d.hs i)

def rawBank (chunks : List (List Bool)) : Tapes 1 prime :=
  ⟨fun _ => 0,fun _ => putWord (fun _ => blank) 0 (chunks.flatten.map bitSymbol)⟩
theorem map_rawBank (chunks : List (List Bool)) :
    Alphabet.mapTapes encoding (ActiveRepairLayoutRecordsAssemblyCommon.rawBank chunks)=rawBank chunks := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i
    exact map_raw chunks.flatten

theorem input_literal (d : Inputs s p offset rows) (chunks : List (List Bool)) :
    input d chunks=
      (((ActiveRepairLayoutRecordsHeadersRun.originalInput (a:=prime) d).append
        (SharedBank.empty 194 prime)).append (rawBank chunks)).append (SharedBank.empty 6 prime) := by
  unfold input
  rw [ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.input_literal]
  simp only [map_append,map_original,map_empty,map_rawBank]

theorem runs_linear (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows)
    (hfit : offset+p.f*p.q≤p.after) (hq3 : p.b+3≤p.q) (hrows : 0<rows)
    (hR : (repair d).geom.addressBits+1≤s.payload) (D : ℕ)
    (hdensity : VaryingControlRepairDensity.lateDensity p.q p.b p.n*
      ((repair d).geom.addressBits+1)≤D) :
    HoareTime program (fun v => v=input d (chunks d array))
      (fun v => v=output d (chunks d array))
      ((ActiveRepairLayoutRecordsHeadersAfterBudget.constant+
        ActiveRepairLateOriginalPipelineBudget.volumeConstant D+
        ActiveRepairLayoutRecordsBankAfterBudget.eraseConstant+611)*
        ActiveRepairLayoutRecordsHeadersAfterBudget.volume s rows) :=
  map_hoare_eq (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.runs_linear d array hfit hq3 hrows hR D hdensity)

theorem input_array (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows) :
    (input d (chunks d array)).tape 237=putWord (fun _ => blank) 0
      ((List.ofFn (ActiveRepairLayoutRecordsMove.move s (p.n*p.b) (p.n*p.q) p.before p.after rows
        p.compactFits p.activeSize
        (ActiveRepairLayoutPermutation.lateActual s p.q p.b p.n p.before p.after rows p.rho offset
          (p.f*p.q) .after (ActiveRepairLayoutKeysLate.positive (repair d))) array)).map bitSymbol) := by
  change (fun z => encoding.encode ((ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.input d (chunks d array)).tape 237 z))=_
  rw [ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.input_array d array]
  exact map_raw _

theorem output_ideal (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows)
    (hfit : offset+p.f*p.q≤p.after) (hq3 : p.b+3≤p.q) :
    (output d (chunks d array)).tape 232=putWord (fun _ => blank) 0
      ((List.ofFn (ActiveRepairLayoutRecordsMove.move s (p.n*p.b) (p.n*p.q) p.before p.after rows
        p.compactFits p.activeSize
        (ActiveRepairLayoutPermutation.lateIdeal s p.q p.b p.n p.before p.after rows p.rho offset
          (p.f*p.q) .after (ActiveRepairLayoutKeysLate.positive (repair d))) array)).map bitSymbol) := by
  change (fun z => encoding.encode ((ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.output d (chunks d array)).tape 232 z))=_
  rw [ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.output_ideal d array hfit hq3]
  exact map_raw _

theorem original_headers (d : Inputs s p offset rows) (chunks : List (List Bool)) :
    SharedBank.payload (output d chunks) (Fin.castAdd 201)=
      ActiveRepairLayoutRecordsHeadersRun.originalInput (a:=prime) d := by
  unfold output
  rw [←map_payload]
  rw [ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.original_headers,map_original]

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsOriginalLateAlphabet
