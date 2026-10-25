module

import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardLine
import IntegerMultBounds.MathlibTM2.Mult.ChirpLinePlacement
import IntegerMultBounds.MathlibTM2.Mult.ChirpSelectedFixedLine
import IntegerMultBounds.MathlibTM2.Mult.ChirpLineTables
import IntegerMultBounds.MathlibTM2.Mult.ChirpLinePrepared
import IntegerMultBounds.MathlibTM2.Mult.ChirpLineSetup
import IntegerMultBounds.MathlibTM2.Mult.ChirpLineBankSetup
import IntegerMultBounds.MathlibTM2.Mult.ChirpLineSourcePrepare
import IntegerMultBounds.MathlibTM2.Mult.ChirpLineInitialize
import IntegerMultBounds.MathlibTM2.Mult.ChirpInitializedLine
import IntegerMultBounds.MathlibTM2.Mult.ChirpLineRelease
import IntegerMultBounds.MathlibTM2.Mult.ChirpClosedLine
import IntegerMultBounds.MathlibTM2.Mult.ChirpGroupLineSymbols
import IntegerMultBounds.MathlibTM2.Mult.ChirpGroupArchive
import IntegerMultBounds.MathlibTM2.Mult.ChirpGroupStep
import IntegerMultBounds.MathlibTM2.Mult.ChirpPreparedGroup
import IntegerMultBounds.MathlibTM2.Mult.ChirpClosedGroup
import IntegerMultBounds.MathlibTM2.Mult.ChirpGroupControls
import Lean.Util.CollectAxioms

/-! Integrity audit of the actual raw-line correlation/output composition. -/

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpForwardLine_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpForwardLine_exec

open Lean in
run_cmd do
  for name in #[`IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.stageLine_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.collectLine_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.finishGroup_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.group_roundTrip,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.lineSymbolsSetup_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.released_lineResult_R,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.released_lineResult_eq,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.closedLine_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpBankFamilyClear_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.clearPrepared_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.clearPrepared_lineResult,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.clearBanks_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.clearBanks_cost,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.release_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.release_lineResult_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.releasedStack_readOutput,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.preparedStack_off,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.preparedStack_bank,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.initialized_product_clean,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.initializedLine_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.lineResult_error,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.initialize_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.initialized_prepared,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.consumers_pairwise,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.consumer_state,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.coefficientState_owned,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.bankSetup_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.outside_banks,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.prepare_from_source,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.counters_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.counters_prepared,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.arithmetic_bank,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.prepare_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.prepare_state,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.arithmeticSetup_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.readiness_coefficient,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.tables_prepared,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.arithmeticSetup_prepared,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.readiness_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.readiness_ready,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.readiness_bank,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.tables_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.tables_off,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpForwardCaller_tableBounds,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.producer_registers,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.dimensions_bank,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.program_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.selected_program_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.LineData.frame,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.LineData.stage,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.SelectedLineData.exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.groupStep_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.groupLoop_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.preparedGroup_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.initialized_lineData,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.initializedGroup_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.releasedStack_eq_of_frame,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.groupRelease_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.closedGroup_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.take_drop_flatten_map,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.readGroupLine_published,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.publishedGroup_error,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.groupInputBatch_length,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.groupOutputBatch_length,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.groupLineCost_sum,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.groupRunCost_eq,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.selectedGroupCost_affine,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpRingSize_le,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpBlockCount_volume,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpBatchProductCost_le_volume,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpRawGatherSharedCost_le,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpMakeXSetupCost_le_linear,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputCompleteCost_le_linear,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpForwardUnitCost_le,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.selectedGroupUnitCost_le,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.selectedGroupCost_le_fast,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpGatherMode_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpRawGatherWith_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpGatherFromDimensionsMode_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpGatherFromDimensionsModeCost_split,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.controlsSetup_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.LineData.transport,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.LineData.shareControls,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.controlsRelease_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.controlsReleaseR_collect,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.tblUnaryCopies_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.unaryCopiesCost_eq,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpControlEmit_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpBlockCountSetup_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.LineData.clearPreparedCost,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.clearPreparedCost_update_high,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.groupStepR_low,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.LineData.groupStep,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.output,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.ringLayout,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.batchLayout,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.raw_inj,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.empty_dimensions,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.dimensions_operands,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.private_dimensions,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement.bank_raw,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.ChirpOutputState.supplyInput,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.ChirpOutputLayout.consumeInput,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpForwardLine_exec] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Chirp raw-line composition and restoration axiom audit passed."
