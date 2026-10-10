import IntegerMultBounds.Machine.FixedHeaderSparseBankCopy
import IntegerMultBounds.Machine.AllAxisPhaseStageMetadata
import IntegerMultBounds.Machine.ActivePrefixStageNativePairSchedule

/-! Physically copy the actual native caller's original13 descriptors into a
fresh67-tape phase bank, preserving the full native source and workspace.
Cleanup erases all copied originals after computed phase metadata is released.
Coefficient sharing and immutable polynomial precision installation are separate. -/
namespace IntegerMultBounds.Machine.AllAxisPhaseOriginalPorts
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageNativeRows (Rows)
open Networks.Shared50ModularControl (prime)
variable {s : Shape} {B : ℕ}

abbrev tapes := ActivePrefixStageNativePairSchedule.count

def focus (i : Fin 13) : Fin tapes := Fin.castAdd 1 ⟨i.val,by
  have hp := ActivePrefixStageNativeCore.public_le
  have hi := i.isLt
  omega⟩
def destination (i : Fin 13) : Fin 67 := Fin.castAdd 24 (Fin.castAdd 15 (Fin.castAdd 15 i))
theorem destination_injective : Function.Injective destination := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun x : Fin 67 => x.val) h
  simpa only [destination,Fin.val_castAdd] using hv
def words (d : Inputs s) (i : Fin 13) :=
  RecursiveChildQuotientsConstant.bits (ActivePrefixStageHeadersData.originalValues d.stage d.rows i)
def phaseInitial (d : Inputs s) : Tapes 67 prime :=
  (ActiveRepairRankHeadersCommands.bank (ActivePrefixStageHeadersData.initial d.stage d.rows)).append
    (FixedHeaderBankCopy.empty 24)
theorem room : 0<tapes+13 := by omega

def setup := FixedHeaderSparseBankCopy.program (a := prime) room focus destination destination_injective (by decide : 13≤67)
def cleanup := FixedHeaderSparseBankCopy.cleanup (a := prime) room destination destination_injective (by decide : 13≤67)

theorem source_headers (d : Inputs s) (xs : Rows d B) (i : Fin 13) :
    (ActivePrefixStageNativePairRun.bank d xs).tape (focus i)=RadixZeroFill.encodedBinary (words d i) ∧
    (ActivePrefixStageNativePairRun.bank d xs).head (focus i)=1 := by
  have h66 : i.val<66 := by have := i.isLt; omega
  have h28 : i.val<28 := by have := i.isLt; omega
  simp only [ActivePrefixStageNativePairRun.bank,focus,Tapes.append,Fin.addCases_left,
    ActivePrefixStageNativeRows.bank,SharedBankStageInput.raw,dite_eq_left h66]
  change (ActivePrefixStageNativeRows.core d xs).tape (Fin.castAdd 1 (Fin.castAdd 52 i))=_ ∧
    (ActivePrefixStageNativeRows.core d xs).head (Fin.castAdd 1 (Fin.castAdd 52 i))=1
  simp [ActivePrefixStageNativeRows.core,Tapes.append,ActivePrefixStageHeadersRouting.caller,
    ActivePrefixStageHeadersPlaced.lift,ActivePrefixStageHeadersData.initial,words,i.isLt,h28]

theorem phase_initial (d : Inputs s) :
    phaseInitial d=FixedHeaderSparseBankCopy.headerBank destination (words d) := by
  apply FixedHeaderSparseBankCopy.headerBank_eq destination destination_injective (words d)
  · intro i
    simp [phaseInitial,ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,
      ActiveRepairRankHeadersCommands.caller,ActivePrefixStageHeadersData.initial,
      destination,words,Tapes.append,i.isLt]
  · intro j hj
    have h13 : 13≤j.val := by
      by_contra h
      have hlt : j.val<13 := by omega
      exact hj ⟨j.val,hlt⟩ (Fin.ext rfl)
    induction j using (Fin.addCases (m:=43) (n:=24)) with
    | left j =>
      induction j using (Fin.addCases (m:=28) (n:=15)) with
      | left j =>
        have hn : ¬j.val<13 := by simpa only [Fin.val_castAdd] using (show ¬(Fin.castAdd 24 (Fin.castAdd 15 j)).val<13 by omega)
        simp [phaseInitial,ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,
          ActiveRepairRankHeadersCommands.caller,ActivePrefixStageHeadersData.initial,Tapes.append,hn]
      | right j =>
        simp [phaseInitial,ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,Tapes.append,SharedBank.empty]
    | right j => simp [phaseInitial,Tapes.append,FixedHeaderBankCopy.empty]

theorem setup_runs (d : Inputs s) (xs : Rows d B) :
    HoareTime setup
      (fun z => z=(ActivePrefixStageNativePairRun.bank d xs).append (FixedHeaderBankCopy.empty 67))
      (fun z => z=(ActivePrefixStageNativePairRun.bank d xs).append (phaseInitial d))
      (FixedHeaderBankCopy.cost (FixedHeaderBankCopy.ops 13) (words d)) := by
  have h := FixedHeaderSparseBankCopy.constructs room focus destination destination_injective (by decide : 13≤67)
    (ActivePrefixStageNativePairRun.bank d xs) (words d)
    (fun i => (source_headers d xs i).1) (fun i => (source_headers d xs i).2)
  rwa [←phase_initial] at h

theorem cleanup_runs (d : Inputs s) (xs : Rows d B) :
    HoareTime cleanup
      (fun z => z=(ActivePrefixStageNativePairRun.bank d xs).append (phaseInitial d))
      (fun z => z=(ActivePrefixStageNativePairRun.bank d xs).append (FixedHeaderBankCopy.empty 67))
      (FixedHeaderBankCopy.cleanupCost (t := tapes) (words d)) := by
  have h := FixedHeaderSparseBankCopy.cleans room destination destination_injective (by decide : 13≤67)
    (ActivePrefixStageNativePairRun.bank d xs) (words d)
  rwa [←phase_initial] at h


/-- Descriptor copying and erasure are charged against original record volume. -/
theorem setup_bound (order : ActivePrefixStageHeadersData.Order) (d : Inputs s)
    (ho : ActivePrefixStageHeadersSchedule.Ordered order d.stage) :
    FixedHeaderBankCopy.cost (FixedHeaderBankCopy.ops 13) (words d) ≤
      130*(d.rows*s.recordWidth) := by
  have hv := (ActivePrefixStageHeadersBudget.original_bounds order d.stage d.rows
    d.hG d.hGK ho d.hr d.hrecord).1
  have hp : 0<s.payload := by have := d.hrecord; omega
  have hr := d.hr
  have hV : 0<d.rows*s.recordWidth := by unfold Shape.recordWidth; positivity
  simpa using FixedHeaderBankCopy.cost_linear (words d) (d.rows*s.recordWidth) hV
    (fun i => RecursiveChildQuotientsConstant.bits_canonical _)
    (fun i => by simpa [words,RecursiveChildQuotientsConstant.bits_value] using hv i)

theorem cleanup_bound (order : ActivePrefixStageHeadersData.Order) (d : Inputs s)
    (ho : ActivePrefixStageHeadersSchedule.Ordered order d.stage) :
    FixedHeaderBankCopy.cleanupCost (t := tapes) (words d) ≤
      117*(d.rows*s.recordWidth) := by
  have hv := (ActivePrefixStageHeadersBudget.original_bounds order d.stage d.rows
    d.hG d.hGK ho d.hr d.hrecord).1
  have hp : 0<s.payload := by have := d.hrecord; omega
  have hr := d.hr
  have hV : 0<d.rows*s.recordWidth := by unfold Shape.recordWidth; positivity
  simpa using FixedHeaderBankCopy.cleanup_cost_linear (t := tapes) (words d)
    (d.rows*s.recordWidth) hV (fun i => RecursiveChildQuotientsConstant.bits_canonical _)
    (fun i => by simpa [words,RecursiveChildQuotientsConstant.bits_value] using hv i)

end
end IntegerMultBounds.Machine.AllAxisPhaseOriginalPorts
