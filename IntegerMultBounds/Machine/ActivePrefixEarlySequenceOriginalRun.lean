import IntegerMultBounds.Machine.ActivePrefixEarlySequenceOriginalHeaders
import IntegerMultBounds.Machine.ActivePrefixEarlySequenceOriginalPayload

/-! End-to-end physical preparation, all four early loads and header cleanup.
Only original geometry/stage words and the original array are supplied. -/
namespace IntegerMultBounds.Machine.ActivePrefixEarlySequenceOriginalRun
noncomputable section
open ActivePrefixEarlySequenceOriginalData ActivePrefixEarlySequenceOriginalInputs
open ActivePrefixEarlySequenceData (Array)
open ActivePrefixLayoutShapes
open CompactGadgetReservationShape (Shape)
open Networks.Shared50ModularControl (prime)

abbrev count := 43+43+ActivePrefixEarlySequenceRun.count
theorem header_le : 43+43≤count := by unfold count; omega
theorem payload_le : 43+ActivePrefixEarlySequenceRun.count≤count := by unfold count; omega

def targetProgram := SharedBankFamily.padProgram ActivePrefixEarlySequenceOriginalHeaders.targetProgram header_le
def compactProgram := SharedBankFamily.padProgram ActivePrefixEarlySequenceOriginalHeaders.compactProgram header_le
def payloadProgram := SharedBankFamily.padProgram ActivePrefixEarlySequenceOriginalPayload.program payload_le
def compactCleanup := SharedBankFamily.padProgram ActivePrefixEarlySequenceOriginalHeaders.compactCleanup header_le
def targetCleanup := SharedBankFamily.padProgram ActivePrefixEarlySequenceOriginalHeaders.targetCleanup header_le

def program := seq (seq (seq (seq targetProgram compactProgram) payloadProgram) compactCleanup) targetCleanup

def overhead := 2*ActivePrefixLayoutHeadersBudget.constant+2*ActivePrefixLayoutHeadersBudget.cleanupConstant
def cost (s : Shape) (p : Parameters s) (rows : ℕ) :=
  overhead*(rows*s.recordWidth)+ActivePrefixEarlySequenceRun.cost s p rows+4

variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

theorem runs (hfit : offset+p.f*p.q≤p.before) (d : Inputs s p offset rows) (x : Array s rows) :
    HoareTime program (fun v => v=SharedBankStageInput.raw (base d.gs d.bw d.hs x) count)
      (fun v => v=SharedBankStageInput.raw
        (base d.gs d.bw d.hs (ActivePrefixEarlySequenceData.result s p offset hfit rows x)) count)
      (cost s p rows) := by
  have h₀ := SharedBankFamily.pad_clean_realizes header_le _ _ _
    (ActivePrefixEarlySequenceOriginalHeaders.target_runs hfit d x)
  have h₁ := SharedBankFamily.pad_clean_realizes header_le _ _ _
    (ActivePrefixEarlySequenceOriginalHeaders.compact_runs hfit d x)
  have h₂ := SharedBankFamily.pad_clean_realizes payload_le _ _ _
    (ActivePrefixEarlySequenceOriginalPayload.runs hfit d x)
  have h₃ := SharedBankFamily.pad_clean_realizes header_le _ _ _
    (ActivePrefixEarlySequenceOriginalHeaders.compact_cleans hfit d
      (ActivePrefixEarlySequenceData.result s p offset hfit rows x))
  have h₄ := SharedBankFamily.pad_clean_realizes header_le _ _ _
    (ActivePrefixEarlySequenceOriginalHeaders.target_cleans hfit d
      (ActivePrefixEarlySequenceData.result s p offset hfit rows x))
  exact ((((h₀.seq h₁).seq h₂).seq h₃).seq h₄).consequence (fun _ h => h) (fun _ h => h)
    (by unfold cost overhead; simp only [Nat.add_mul,Nat.mul_assoc]; omega)

end
end IntegerMultBounds.Machine.ActivePrefixEarlySequenceOriginalRun
