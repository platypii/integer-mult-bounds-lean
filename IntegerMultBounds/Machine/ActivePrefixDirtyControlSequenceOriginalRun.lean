import IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceOriginalHeaders
import IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceOriginalPayload

/-! Original-input later execution: physically synthesize three header banks,
perform the full dirty-control schedule, then erase every generated word. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceOriginalRun
noncomputable section
open ActivePrefixDirtyControlSequenceOriginalData ActivePrefixDirtyControlSequenceOriginalInputs
open ActivePrefixEarlySequenceOriginalInputs (Inputs)
open ActivePrefixDirtyControlConjugationData (FullArray)
open ActivePrefixLayoutShapes
open CompactGadgetReservationShape (Shape)

abbrev count := 53+43+ActivePrefixDirtyControlSequenceStages.count
theorem header_le : 53+43≤count := by unfold count; omega
theorem payload_le : 53+ActivePrefixDirtyControlSequenceStages.count≤count := by unfold count; omega

def targetProgram := SharedBankFamily.padProgram ActivePrefixDirtyControlSequenceOriginalHeaders.targetProgram header_le
def compactProgram := SharedBankFamily.padProgram ActivePrefixDirtyControlSequenceOriginalHeaders.compactProgram header_le
def sourceProgram := SharedBankFamily.padProgram ActivePrefixDirtyControlSequenceOriginalHeaders.sourceProgram header_le
def payloadProgramFor (a b c e : ActivePrefixDirtyControlConjugationData.Kind) := SharedBankFamily.padProgram
  (ActivePrefixDirtyControlSequenceOriginalPayload.programFor a b c e) payload_le
def sourceCleanup := SharedBankFamily.padProgram ActivePrefixDirtyControlSequenceOriginalHeaders.sourceCleanup header_le
def compactCleanup := SharedBankFamily.padProgram ActivePrefixDirtyControlSequenceOriginalHeaders.compactCleanup header_le
def targetCleanup := SharedBankFamily.padProgram ActivePrefixDirtyControlSequenceOriginalHeaders.targetCleanup header_le
def programFor (a b c e : ActivePrefixDirtyControlConjugationData.Kind) := seq (seq (seq (seq (seq (seq targetProgram compactProgram) sourceProgram)
  (payloadProgramFor a b c e)) sourceCleanup) compactCleanup) targetCleanup

variable {s : Shape} {p : Parameters s} {offset rows : ℕ}
def headerCost (d : Inputs s p offset rows) :=
  ActivePrefixDirtyControlHeadersRun.cost .target (layout d)+
  ActivePrefixDirtyControlHeadersRun.cost .compact (layout d)+
  ActivePrefixDirtyControlHeadersRun.cost .source (layout d)+
  ActivePrefixDirtyControlHeadersRun.cleanupCost .source (layout d)+
  ActivePrefixDirtyControlHeadersRun.cleanupCost .compact (layout d)+
  ActivePrefixDirtyControlHeadersRun.cleanupCost .target (layout d)
def costFor (a b c e : ActivePrefixDirtyControlConjugationData.Kind) (hfit : offset+p.f*p.q≤p.after) (hn : 0<p.n) (hb : 2≤p.b) (d : Inputs s p offset rows) :=
  headerCost d+ActivePrefixDirtyControlSequenceRun.costFor a b c e s (geometry hfit hn hb d)+6

theorem runs_for (a b c e : ActivePrefixDirtyControlConjugationData.Kind) (hfit : offset+p.f*p.q≤p.after) (hn : 0<p.n) (hb : 2≤p.b)
    (d : Inputs s p offset rows) (x : FullArray s rows) :
    HoareTime (programFor a b c e) (fun v => v=SharedBankStageInput.raw (base d.gs d.bw d.hs x) count)
      (fun v => v=SharedBankStageInput.raw
        (base d.gs d.bw d.hs (ActivePrefixDirtyControlSequenceRun.laterFor a b c e (geometry hfit hn hb d) x)) count)
      (costFor a b c e hfit hn hb d) := by
  have h₀ := SharedBankFamily.pad_clean_realizes header_le _ _ _
    (ActivePrefixDirtyControlSequenceOriginalHeaders.target_runs d x)
  have h₁ := SharedBankFamily.pad_clean_realizes header_le _ _ _
    (ActivePrefixDirtyControlSequenceOriginalHeaders.compact_runs d x)
  have h₂ := SharedBankFamily.pad_clean_realizes header_le _ _ _
    (ActivePrefixDirtyControlSequenceOriginalHeaders.source_runs d x)
  have h₃ := SharedBankFamily.pad_clean_realizes payload_le _ _ _
    (ActivePrefixDirtyControlSequenceOriginalPayload.runs_for a b c e hfit hn hb d x)
  have h₄ := SharedBankFamily.pad_clean_realizes header_le _ _ _
    (ActivePrefixDirtyControlSequenceOriginalHeaders.source_cleans d
      (ActivePrefixDirtyControlSequenceRun.laterFor a b c e (geometry hfit hn hb d) x))
  have h₅ := SharedBankFamily.pad_clean_realizes header_le _ _ _
    (ActivePrefixDirtyControlSequenceOriginalHeaders.compact_cleans d
      (ActivePrefixDirtyControlSequenceRun.laterFor a b c e (geometry hfit hn hb d) x))
  have h₆ := SharedBankFamily.pad_clean_realizes header_le _ _ _
    (ActivePrefixDirtyControlSequenceOriginalHeaders.target_cleans d
      (ActivePrefixDirtyControlSequenceRun.laterFor a b c e (geometry hfit hn hb d) x))
  exact ((((((h₀.seq h₁).seq h₂).seq h₃).seq h₄).seq h₅).seq h₆).consequence
    (fun _ h => h) (fun _ h => h) (by unfold costFor headerCost; omega)

def program := programFor .tPure .tNegative .uPure .uNegative
def cost (hfit : offset+p.f*p.q≤p.after) (hn : 0<p.n) (hb : 2≤p.b) (d : Inputs s p offset rows) :=
  costFor .tPure .tNegative .uPure .uNegative hfit hn hb d

theorem runs (hfit : offset+p.f*p.q≤p.after) (hn : 0<p.n) (hb : 2≤p.b)
    (d : Inputs s p offset rows) (x : FullArray s rows) :
    HoareTime program (fun v => v=SharedBankStageInput.raw (base d.gs d.bw d.hs x) count)
      (fun v => v=SharedBankStageInput.raw
        (base d.gs d.bw d.hs (ActivePrefixDirtyControlSequenceData.later (geometry hfit hn hb d) x)) count)
      (cost hfit hn hb d) := runs_for .tPure .tNegative .uPure .uNegative hfit hn hb d x

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceOriginalRun
