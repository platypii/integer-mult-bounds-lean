import IntegerMultBounds.Machine.ActiveRepairLateKeyOriginalValid

/-! Actual header synthesis, full-rank later-key computation, and generated
header erasure share ninety-one blank tapes. Original inputs are retained. -/
namespace IntegerMultBounds.Machine.ActiveRepairLateKeyOriginalRun
noncomputable section
open ActiveRepairLateKeyOriginalData ActiveRepairLateKeyOriginalValid

def headerProgram (side : ActiveRepairRankHeadersData.SourceSide) := extend
  (ActiveRepairRankHeadersPlaced.program (a := 1) side headerFocus header_injective) 48
def keyProgram := ActiveRepairLateKeyPlaced.program keyFocus key_injective
def cleanupProgram := extend
  (ActiveRepairRankHeadersPlaced.cleanupProgram (a := 1) headerFocus header_injective) 48
def program (side : ActiveRepairRankHeadersData.SourceSide) :=
  seq (seq (headerProgram side) keyProgram) cleanupProgram

theorem pad (v : Tapes 43 1) :
    (CleanSubbank.bank (s := 43) v).append (SharedBank.empty 48 1)=
      CleanSubbank.bank (s := 91) v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem header_runs (d : Data) (h : Valid d) :
    HoareTime (headerProgram d.side) (fun z => z=CleanSubbank.bank (s := 91) d.input)
      (fun z => z=CleanSubbank.bank (s := 91) d.generated)
      (ActiveRepairRankHeadersData.constant*(d.geom.addressBits+1)) := by
  have hh := ActiveRepairRankHeadersPlaced.produces d.input headerFocus header_injective
    d.side d.geom h.hw d.originals (input_payload d) h.hv h.hc h.bounded
  rw [produced_eq d h.hv h.hc] at hh
  have hp := hoare_extend_eq hh (SharedBank.empty 48 1)
  simpa only [headerProgram,pad] using hp

theorem key_runs (d : Data) (h : Valid d) :
    HoareTime keyProgram (fun z => z=CleanSubbank.bank (s := 91) d.generated)
      (fun z => z=CleanSubbank.bank (s := 91) d.written) (61000*(d.geom.addressBits+1)) := by
  have hh := ActiveRepairLateKeyPlaced.runs d.generated keyFocus key_injective
    d.key (key_valid d h) (key_payload d)
  rw [key_result] at hh
  exact hh

theorem cleanup_runs (d : Data) (h : Valid d) :
    HoareTime cleanupProgram (fun z => z=CleanSubbank.bank (s := 91) d.written)
      (fun z => z=CleanSubbank.bank (s := 91) d.output)
      (ActiveRepairRankHeadersRun.cleanupConstant*(d.geom.addressBits+1)) := by
  have hh := ActiveRepairRankHeadersPlaced.cleans d.written headerFocus header_injective
    d.side d.geom d.originals (written_payload d h.hv h.hc) h.hv h.hc h.bounded
  rw [restored_eq] at hh
  have hp := hoare_extend_eq hh (SharedBank.empty 48 1)
  simpa only [cleanupProgram,pad] using hp

def constant := ActiveRepairRankHeadersData.constant+61000+
  ActiveRepairRankHeadersRun.cleanupConstant+2

private theorem budget (C D A : ℕ) :
    C*(A+1)+1+61000*(A+1)+1+D*(A+1)≤(C+61000+D+2)*(A+1) := by
  nlinarith

theorem runs_linear (d : Data) (h : Valid d) :
    HoareTime (program d.side) (fun z => z=CleanSubbank.bank (s := 91) d.input)
      (fun z => z=CleanSubbank.bank (s := 91) d.output) (constant*(d.geom.addressBits+1)) := by
  exact (((header_runs d h).seq (key_runs d h)).seq (cleanup_runs d h)).consequence
    (fun _ h => h) (fun _ h => h)
    (budget ActiveRepairRankHeadersData.constant ActiveRepairRankHeadersRun.cleanupConstant d.geom.addressBits)

end
end IntegerMultBounds.Machine.ActiveRepairLateKeyOriginalRun
