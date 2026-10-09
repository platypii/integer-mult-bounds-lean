import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyOriginalEarly
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAlphabet

/-! The complete original-input early repair executes in the fixed prime
alphabet with literal binary tapes and unchanged runtime. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsOriginalEarlyAlphabet
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairLayoutRecordsHeadersData
open ActiveRepairLayoutRecordsAlphabet
open Networks.Shared50ModularControl (prime)
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

def program := Alphabet.program encoding ActiveRepairLayoutRecordsAssemblyOriginalEarly.program

def input (d : Inputs s p offset rows) (chunks : List (List Bool)) :=
  Alphabet.mapTapes encoding (ActiveRepairLayoutRecordsAssemblyOriginalEarly.input d chunks)
def output (d : Inputs s p offset rows) (chunks : List (List Bool)) :=
  Alphabet.mapTapes encoding (ActiveRepairLayoutRecordsAssemblyOriginalEarly.output d chunks)
abbrev chunks (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows) :=
  ActiveRepairLayoutRecordsAssemblyOriginalEarly.chunks d array

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
        (SharedBank.empty 185 prime)).append (rawBank chunks)).append (SharedBank.empty 6 prime) := by
  unfold input
  rw [ActiveRepairLayoutRecordsAssemblyOriginalEarly.input_literal]
  simp only [map_append,map_original,map_empty,map_rawBank]

theorem runs_linear (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows)
    (hfit : offset+p.f*p.q≤p.before) (hq3 : p.b+3≤p.q) (hrows : 0<rows)
    (hR : (repair d).geom.addressBits+1≤s.payload) (D : ℕ)
    (hdensity : VaryingControlRepairDensity.earlyDensity p.q p.b p.n*
      ((repair d).geom.addressBits+1)≤D) :
    HoareTime program (fun v => v=input d (chunks d array))
      (fun v => v=output d (chunks d array))
      ((ActiveRepairLayoutRecordsHeadersBudget.constant+
        ActiveRepairEarlyOriginalPipelineBudget.volumeConstant D+
        ActiveRepairLayoutRecordsBankBudget.eraseConstant+611)*
        ActiveRepairLayoutRecordsHeadersBudget.volume s rows) :=
  map_hoare_eq (ActiveRepairLayoutRecordsAssemblyOriginalEarly.runs_linear d array hfit hq3 hrows hR D hdensity)

theorem input_array (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows) :
    (input d (chunks d array)).tape 228=putWord (fun _ => blank) 0
      ((List.ofFn (ActiveRepairLayoutRecordsMove.move s (p.n*p.b) (p.n*p.q) p.before p.after rows
        p.compactFits p.activeSize
        (ActiveRepairLayoutPermutation.earlyActual s p.q p.b p.n p.before p.after rows p.rho offset
          (p.f*p.q) .before (ActiveRepairLayoutKeysEarly.positive (repair d))) array)).map bitSymbol) := by
  change (fun z => encoding.encode ((ActiveRepairLayoutRecordsAssemblyOriginalEarly.input d (chunks d array)).tape 228 z))=_
  rw [ActiveRepairLayoutRecordsAssemblyOriginalEarly.input_array d array]
  exact map_raw _

theorem output_ideal (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows)
    (hfit : offset+p.f*p.q≤p.before) (hq3 : p.b+3≤p.q) :
    (output d (chunks d array)).tape 223=putWord (fun _ => blank) 0
      ((List.ofFn (ActiveRepairLayoutRecordsMove.move s (p.n*p.b) (p.n*p.q) p.before p.after rows
        p.compactFits p.activeSize
        (ActiveRepairLayoutPermutation.earlyIdeal s p.q p.b p.n p.before p.after rows p.rho offset
          (p.f*p.q) .before (ActiveRepairLayoutKeysEarly.positive (repair d))) array)).map bitSymbol) := by
  change (fun z => encoding.encode ((ActiveRepairLayoutRecordsAssemblyOriginalEarly.output d (chunks d array)).tape 223 z))=_
  rw [ActiveRepairLayoutRecordsAssemblyOriginalEarly.output_ideal d array hfit hq3]
  exact map_raw _

theorem original_headers (d : Inputs s p offset rows) (chunks : List (List Bool)) :
    SharedBank.payload (output d chunks) (Fin.castAdd 192)=
      ActiveRepairLayoutRecordsHeadersRun.originalInput (a:=prime) d := by
  unfold output
  rw [←map_payload]
  rw [ActiveRepairLayoutRecordsAssemblyOriginalEarly.original_headers,map_original]

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsOriginalEarlyAlphabet
