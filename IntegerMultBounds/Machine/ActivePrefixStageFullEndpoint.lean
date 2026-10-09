import IntegerMultBounds.Machine.ActivePrefixStageFullEarlyRun
import IntegerMultBounds.Machine.ActivePrefixStageFullLateRun

/-! Literal full-stage endpoints retain only the original thirteen descriptors
and raw array. Every synthesized, copied and private word has been erased. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageFullEndpoint
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData
open Networks.Shared50ModularControl (prime)
variable {s : Shape}

theorem original_blank (d : Inputs s) (x : ActiveRepairLayoutRecordsData.Array s d.rows)
    (i : Fin 66) (hl : 13 ≤ i.val) (hn : i.val≠65) :
    (original d x).head i=0 ∧ (original d x).tape i=fun _ => blank := by
  induction i using Fin.addCases (m := 65) (n := 1) with
  | left j =>
    simp only [Fin.val_castAdd] at hl hn
    have hj : ¬j.val<13 := by omega
    by_cases h28 : j.val<28
    all_goals simp [original,caller,ActivePrefixStageHeadersRouting.caller,
      ActivePrefixStageHeadersPlaced.lift,ActivePrefixStageHeadersData.initial,hj,h28,Tapes.append]
  | right j => have := j.isLt; simp only [Fin.val_natAdd] at hn; omega

theorem original_raw (d : Inputs s) (x : ActiveRepairLayoutRecordsData.Array s d.rows) :
    (original d x).head (65 : Fin 66)=0 ∧ (original d x).tape (65 : Fin 66)=ActiveTargetRotation.word x := by
  constructor <;> rfl

theorem original_header (d : Inputs s) (x : ActiveRepairLayoutRecordsData.Array s d.rows) (i : Fin 13) :
    (original d x).head (Fin.castAdd 53 i)=1 ∧
      (original d x).tape (Fin.castAdd 53 i)=RadixZeroFill.encodedBinary
        (RecursiveChildQuotientsConstant.bits (ActivePrefixStageHeadersData.originalValues d.stage d.rows i)) := by
  have h13 := i.isLt
  have h28 : i.val<28 := by omega
  have h65 : i.val<65 := by omega
  simp [original,caller,ActivePrefixStageHeadersRouting.caller,ActivePrefixStageHeadersPlaced.lift,
    ActivePrefixStageHeadersData.initial,Tapes.append,Fin.addCases,h13,h28,h65]

 theorem bank_blank {k : ℕ} (d : Inputs s) (x : ActiveRepairLayoutRecordsData.Array s d.rows)
    (i : Fin (66+k)) (hl : 13 ≤ i.val) (hn : i.val≠65) :
    (CleanSubbank.bank (s := k) (original d x)).head i=0 ∧
      (CleanSubbank.bank (s := k) (original d x)).tape i=fun _ => blank := by
  induction i using Fin.addCases with
  | left j =>
    have h := original_blank d x j hl hn
    simpa only [CleanSubbank.bank,Tapes.append,Fin.addCases_left] using h
  | right j => simp [CleanSubbank.bank,Tapes.append,SharedBank.empty]

def earlyRaw : Fin ActivePrefixStageFullEarlyRun.count :=
  Fin.castAdd ActivePrefixStageFullEarlyRun.privateCount (65 : Fin 66)
def lateRaw : Fin ActivePrefixStageFullLateRun.count :=
  Fin.castAdd ActivePrefixStageFullLateRun.privateCount (65 : Fin 66)

theorem early_raw (d : Inputs s) (x : ActiveRepairLayoutRecordsData.Array s d.rows) :
    (ActivePrefixStageFullEarlyRun.bank d x).head earlyRaw=0 ∧
      (ActivePrefixStageFullEarlyRun.bank d x).tape earlyRaw=ActiveTargetRotation.word x := by
  constructor <;> rfl

theorem late_raw (d : Inputs s) (x : ActiveRepairLayoutRecordsData.Array s d.rows) :
    (ActivePrefixStageFullLateRun.bank d x).head lateRaw=0 ∧
      (ActivePrefixStageFullLateRun.bank d x).tape lateRaw=ActiveTargetRotation.word x := by
  constructor <;> rfl

end
end IntegerMultBounds.Machine.ActivePrefixStageFullEndpoint
