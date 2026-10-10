import IntegerMultBounds.Machine.NativeEndpointCharacterOriginalBudget

namespace IntegerMultBounds.Machine.NativeEndpointCharacterCanonical
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open ButterflyAxisHeadersArithmetic
open ButterflyAxisHeadersData (cmd)
open ActiveRepairRankHeadersCommands (bank)
variable {s : Shape} {t : ℕ}

theorem two_slots (v : Stage s) : 2≤v.slots := by
  have hs := v.source.isLt
  have ht := v.target.isLt
  by_contra h
  have he : v.source=v.target := Fin.ext (by omega)
  exact v.distinct he

def stage (v : Stage s) : Stage s :=
  let h := two_slots v
  { v with
    source := ⟨0,by omega⟩
    target := ⟨1,by omega⟩
    distinct := by
      intro he
      have hh := congrArg Fin.val he
      change 0=1 at hh
      omega }

theorem ordered (v : Stage s) :
    ActivePrefixStageHeadersSchedule.Ordered .early (stage v) := by
  change 0<1
  omega

def schedule : List Op :=
  [cmd (.erase 11),cmd (.erase 12),.base (.constant 11 0),.base (.constant 12 1)]
def normalize := extend (compile (a:=2) schedule).2 24

theorem valid (v : Stage s) (rows ell p : ℕ) :
    validSchedule schedule (NativeEndpointCharacterPrepare.raw v rows ell p) := by
  simp [schedule,validSchedule,ButterflyAxisHeadersArithmetic.valid,eval,
    CompactChildHeadersArithmetic.valid,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,
    ActiveRepairRankHeadersCommands.put,Function.update,
    NativeEndpointCharacterPrepare.raw,CompactSpectatorLeafSetup.raw]

theorem execute_eq (v : Stage s) (rows ell p : ℕ) :
    execute schedule (NativeEndpointCharacterPrepare.raw v rows ell p)=
      NativeEndpointCharacterPrepare.raw (stage v) rows ell p := by
  funext i
  fin_cases i <;> simp [schedule,execute,eval,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,
    ActiveRepairRankHeadersCommands.put,Function.update,
    NativeEndpointCharacterPrepare.raw,CompactSpectatorLeafSetup.raw,stage]

theorem normalize_runs (v : Stage s) (rows ell p : ℕ) :
    HoareTime normalize (fun z => z=NativeEndpointCharacterPrepare.input v rows ell p)
      (fun z => z=NativeEndpointCharacterPrepare.input (stage v) rows ell p)
      (scheduleCost schedule (NativeEndpointCharacterPrepare.raw v rows ell p)) := by
  have hh := schedule_runs (a:=2) schedule (NativeEndpointCharacterPrepare.raw v rows ell p)
    (valid v rows ell p)
  rw [execute_eq v] at hh
  exact hoare_extend_eq hh (FixedHeaderBankCopy.empty 24)

theorem phase_eq (v : Stage s) (ell p m : ℕ) (ws : List (ZMod 4)) (i : ℕ) :
    AllAxisPolynomialLiteralEndpoint.phase (NativePolynomialStageShape.stage (stage v) ell p) m ws i=
      AllAxisPolynomialLiteralEndpoint.phase (NativePolynomialStageShape.stage v ell p) m ws i := rfl

theorem result_eq (v : Stage s) (ell p m : ℕ) (ws : List (ZMod 4))
    {N R : ℕ} (xs : Fin (N*R) → ButterflyStreamData.Coefficient) :
    AllAxisPolynomialLiteralEndpoint.result (NativePolynomialStageShape.stage (stage v) ell p) m ws xs=
      AllAxisPolynomialLiteralEndpoint.result (NativePolynomialStageShape.stage v ell p) m ws xs := rfl


end
end IntegerMultBounds.Machine.NativeEndpointCharacterCanonical
