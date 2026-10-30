module

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellQueuedHaloCore
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellQueuedHaloFrame
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedCoreGather
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedCoreGather
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreCountedHost
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedHaloCore
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloCoreRelease
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloCore
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloPublication
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloSolve
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRecovery
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryFinish
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryReadAccuracy

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryInteriorReady

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryInterior

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloRecoveryBoundaryFormat

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryHaloRecoveryPrecision
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloRecoveryAccuracy

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRecoveryRhs

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRecoveryInputs

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRecoveryField
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryRhsInput

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryBoundaryPublish

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRecoveryUnfold

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRealUnfold
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundarySolutionInput

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundarySolutionField

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloBoundarySolve

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryHaloPrecision

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryFactoryGeometry

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCouplingIntervalMetadata

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoutedPackedBoundaryFactoryRelease

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryFactoryRelease

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryFactory
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedPackedHaloRealBoundaryData

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloRealBoundaryData
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryNormalize
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloResidualSolve

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloBoundaryData

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloResidual

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloInteriorCoefficients

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedCouplingCoefficientInterval

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSolvePackedHaloInteriorField

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSolvePackedHaloInterior

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRunGeneratedPackedHaloKeys

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloKeyLoop

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellKeyedPackedHaloPublish

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedLengthKey

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedGroupHeaders

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLocalHaloClassController
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloPhaseRangeCode

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedPackedHaloInputBank

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetunedPackedCellBatchPublish

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReusablePackedCellBatchPublish

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloGroupAccuracy

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloResidualNormalization

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellFoldedBoundaryRhs

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedPackedBoundaryRhsFold

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparePackedBoundaryFold

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryCount

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellBoundaryRhs

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMetadataPackedBoundaryRhs

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedPackedBoundaryRhs

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundarySelection

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBinaryLengthCouplingCoefficientInterval
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedPackedPageSpatialCouplingRowLoop
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareMaskedGatheredRibbon
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseCouplingRibbon
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedRestoredPackedCouplingInterval
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGatheredCouplingInterval
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGatheredFeedCouplingInterval
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCompletedGatheredFeedCouplingInterval
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedCouplingMetadata
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorCouplingInterval
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreHaloPacketHost
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCoreHaloPackets
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGatherPackedCellInputs
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellControlledPackedCellInputs
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawPackedCellInputs
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellRows
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellBatch
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedPackedCellBatch
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellPublish
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellPublicationFromDimensions
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellControlledPublishingPackedCellInputs
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishingPackedCellBatchPublish
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedPackedCellBatchPublish
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLocalFeedCouplingInterval
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellFieldAccuracy
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedSharedLocalFeedCouplingInterval
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResidualReadyPackedCellBatch
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellResidual

/-! Audit interval setup, generated local source construction, restored packed
arithmetic and paid source release. The gathered caller composes these
steps; complete inverse and S4 tensor integration remain separate gates. -/

open Lean in
run_cmd do
  for name in #[
      `IntegerMultBounds.MathlibTM2.Host.extendStacks_updateR,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.allocateZeroLine_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.prepareHaloBuffer_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.prepareHaloBuffer_input,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.preparedHaloCore_spec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.haloBufferRelease_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedHaloCoreRelease_spec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedHaloInput.run,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedHaloCore_spec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.preparedPackedSlice_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.preparedCorePublication_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedHaloPublication_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.boundaryFactorStock_of_bounds,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedFactorRelease_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedTableRelease_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedRecoveryRelease_exec,
      `IntegerMultBounds.MathlibTM2.Host.exec_extendStacks,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedHaloSolve_spec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedRecoveryInteriorReady_after_rhs,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundaryRecovery_spec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedRecoveryFinish_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedRecovery_read_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.haloRecovery_boundary_range,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.haloPackedOffsets_interior,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.haloGroup_scatter_off_interior_word,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedHaloWordFrame.read,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedHaloWordFrame.error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedRecoveryInteriorReady_of_retained,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedRecoveryInteriorReg_avoids_retained,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedRecoveryInteriorReg_avoids_factors,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedRecoveryInterior_field_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.haloRecovery_boundary_format_spec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.boundaryHaloRecoveryTarget_allowance,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.boundaryHaloRecoveryTarget_sizing,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.boundaryHaloRecovery_format,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.boundaryHaloRecovery_error_budget,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.haloRecoveryRhs_spec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.haloRecovery_interior_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedRecoveryCoupling_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundaryRecoveryRhs_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundaryRecoveryInputs_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.CouplingMasterHeaders.of_frame,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.CouplingMasterHeaders.ready,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundaryRecoveryField_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedRecoveryRhsInput_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedRecoveryDestination_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.maskedPackedBoundaryPublish_exec,
      `IntegerMultBounds.MathlibTM2.Host.spreadRecordStep_exec,
      `IntegerMultBounds.MathlibTM2.Host.spreadRecords_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedRecoveryBoundaryBuffer_exec,
      `IntegerMultBounds.MathlibTM2.Host.embStk_extendStacks,
      `IntegerMultBounds.MathlibTM2.Host.extendStacks_fresh,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundaryRecoveryUnfold_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundaryRecoveryUnfold_extended_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedBoundarySolveWorkspace.publish,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundaryRecovery_clean,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundaryRecovery_width,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundarySolutionUnfold_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundaryRealUnfold_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundarySolutionInput_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.haloResidual_error_bound,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.haloResidualError_le,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.haloResidual_budget_of_target,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.boundaryHaloTarget_residual_budget,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.boundary_unscaled_solve_target_of_rhs_budget,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.haloBoundary_solution_accuracy,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.boundaryFoldedRead_eq,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.boundaryFoldedRead_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundary_scatter_solution,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.boundarySolutionField_packed_read,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.boundarySolutionField_packed_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedCell_left_eq,
      `IntegerMultBounds.MathlibTM2.Host.embOvr_left_of_eq,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedHaloBoundarySetup_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedHaloBoundarySolve_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.executionSizing_of_allowance,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.boundaryHaloTarget_accuracy,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.boundaryHaloTarget_sizing,
      `IntegerMultBounds.MathlibTM2.Host.embOvr_right_left,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.placedRetainedCouplingIntervalMetadata_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundaryGeometry_factorState,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundaryGeometry_native,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.routedPackedBoundaryFactory_header_frame,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedBoundaryFactoryGeometry_spec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.prepareRetainedCouplingMetadata_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.prepareRetainedCouplingIntervalMetadata_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.retainedCouplingIntervalMetadataR_off,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundaryFactorReg_ne_table,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundaryTableRouting_state,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundaryTableRouting_native,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundaryTableRouting_left,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.routedPackedBoundaryFactoryRelease_spec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.releasePackedBoundaryRuntime_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.releasedPackedBoundaryRuntime_native,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.releasedPackedBoundaryRuntime_factorState,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedBoundaryFactoryRelease_spec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedBoundaryFactory_spec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundaryFactorState_of_high_frame,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundarySolveReady_of_high_frame,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundarySolveReady_halo,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.placedPackedHaloRealBoundaryData_exec,
      `IntegerMultBounds.MathlibTM2.Host.embOvr_updateR_updateR,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.haloResidual_norm_bound,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedPreparedResidualSolve_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedPreparedResidualSolve_ready,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedHaloResidualSolve_exec,
      `IntegerMultBounds.MathlibTM2.Host.mapOwnedLine_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedHaloRealBoundaryData_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundaryFactorReg_injective,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundaryFactorReg_avoids_metadata,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundaryNormalize_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.releasedHaloClass_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.binaryHaloClass_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.metadataHaloClass_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.naturalGroupInputBank_packed_halo_controls,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.metadataHaloClass_inputBank_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.replaceUnary_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.retunedPackedCellBatchPublish_sized_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.retireProductLine_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.reusablePackedCellBatchPublish_sized_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.haloPackedOffsets_fit,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.haloPackedOffsets_disjoint,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedHaloGroups_cover,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.haloGroup_scatter_preserves,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.haloInterior_error_of_packed_outputs,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.haloInterior_stable_norm_of_packed_outputs,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloCellInterval_spec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.haloInterior_error_of_cells,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedHaloCell_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.haloInterior_stable_norm_of_cells,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.haloResidual_normalization_bound_of_cells,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedCellFoldedBoundaryRhs_sized_exec,
      `IntegerMultBounds.MathlibTM2.Stack.Exec.frame,
      `IntegerMultBounds.MathlibTM2.Host.exec_withLeft,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.framedBoundaryRhsFold_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundaryRhsFold_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.closedPackedBoundaryRhsFold_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.moveCountedLine_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundaryFoldCounters_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.preparePackedBoundaryFold_exec,
      `IntegerMultBounds.MathlibTM2.Host.countSelectors_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundaryMask_count,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundaryCount_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedCellBoundaryRhs_sized_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.binaryIntervalStreamHost_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.binaryCouplingSourceIntervalMask_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.metadataBoundaryMask_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.metadataPackedBoundaryRhs_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generatedPackedBoundaryRhs_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundaryRhsMask_flags,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.couplingSourceIntervalMaskHost_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedCellResidual_sized_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.preservePackedRhs_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.prepareSharedCouplingRows_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.batchInputBank_update_result,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.residualReadyPackedCellBatch_sized_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.sharedCouplingReg_injective,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.sharedCouplingHeaders_ready,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.sharedCouplingCounters_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.sharedLocalFeedCouplingInterval_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.preparedSharedLocalFeedCouplingInterval_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedField_get,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedInterval_packedField,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedField_property,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedField_read,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedCellField_word,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedCellOutputSpec_field_at,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.couplingInputWords_property,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.couplingInputWords_fits,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.localRibbon_active_index,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.maskedLine_localCouplingRibbon,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.zeroPadLocalPrefix_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.prepareLocalCouplingRibbon_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.buildMaskedGatheredRibbon_data_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.buildMaskedLocalRibbon_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.buildPreparedLocalRibbon_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.localCouplingInterval_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.localFeedCouplingInterval_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedCellGaps_scale,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedCellScatter_cstream,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.preparePackedCellDestination_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.generatedPackedCellBatchPublish_sized_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedCellScatter_word_append,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedPublishedCell_accuracy,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.rawPublishingPackedCellInputs_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.publishingPackedCellInputBank_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.publishingPackedCellBatch_sized_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.publishingPackedCellBatchPublish_sized_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.gatherPublishingPackedCellInputs_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.controlledPublishingPackedCellInputs_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedCellPublicationControls_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedCellPublicationFromDimensions_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.binaryLengthCouplingCoefficientInterval_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.retainedPageSpatialCouplingRowLoop_interval_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.retainedPageSpatialCouplingRowLoop_packed_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.prepareMaskedGatheredRibbon_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.generatedRestoredPackedCouplingInterval_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.releaseCouplingRibbon_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.gatheredCouplingInterval_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundaryRhsOrderedGather_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundaryRhs_select_folded,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.feedPackedCouplingResult_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.gatheredFeedCouplingInterval_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CouplingIntervalMetadata.guard,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CouplingIntervalMetadata.ribbon,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.completeCouplingIntervalMetadata_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.completedGatheredFeedCouplingInterval_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.binaryHeaderBank_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.prepareSharedCouplingMetadata_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.loadCouplingIntervalDescriptor_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.releaseCouplingIntervalDescriptor_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.descriptorCouplingInterval_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.tablePacketHost_list_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generatedCoreHaloPacketCode_do,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generatedCoreHaloPacketHost_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.preparedCoreHaloPackets_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundaryData_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedHaloBoundaryData_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.sharedCouplingPage_native,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedHaloResidual_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.haloResidual_guarded_normalization_bound,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.preservePackedRhsFrom_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.sharedCouplingPage_core,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedHaloInteriorCoefficients_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.couplingIntervalMetadata_shared,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedHaloReady.coupling,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.sharedCouplingCoefficientInterval_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedHaloReady.coefficient_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedCellScatter_range,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.encodedRange_packedField,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.haloResidual_normalization_bound,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.solvePackedHaloInterior_field_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.initializePackedHaloKeys_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.solvePackedHaloInterior_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedCellOrigin_local_index,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.haloInterior_error_of_packed_reads,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.runGeneratedPackedHaloKeys_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedHaloReady.of_publication,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedHaloReady.update_count,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedHaloReady_publish,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedHaloKeyLoop_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.emptyPackedHaloGroup_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.conditionalPackedHaloPublish_sized_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.keyedPackedHaloInput_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.keyedPackedHaloPublish_sized_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.takeBinaryUnaryKey_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedLengthKey_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedGroupHeaders_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedHaloGroupInput_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.scatterRows_slice_off,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.haloGroup_scatter_word_preserves,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedHaloGroupOutputSpec_scatter,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedHaloGroupOutputs_scatter,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.localHaloClassCode_do,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.localHaloClassController_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.preparedOriginAdvanceControls_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.originAdvances_coreControls,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.preparedCoreAdvanceControls_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generatedCoreControls_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generatedCoreGather_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.coreGatherLoad_cost,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.preparedCoreGather_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.prepareCoreGatherHeaders_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.initializedCoreGather_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.initializedCoreGather_packed_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedHaloFrame.hready,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedHaloSetup.update_source,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedHaloSetup.with_source,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.takeCountedLine_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.attachQueuedHalo_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.attachQueuedHalo_frame,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.queuedHaloCore_spec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.countedOriginListHost_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generatedCoreCountedHost_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.countedOriginHost_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.haloPhaseRangeCode_do,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedGatherControls_eq,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedInterval_eq_cellSourceRows,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.gatherPackedCellInputs_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.restoredLocalAdvanceControls_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.placedLocalAdvanceControls_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.controlledPackedCellInputs_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.preparedPackedCellInputs_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.rawPackedCellInputs_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedCellRows_eq_sourceRows,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedCellOrigin_packets,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedCellInputBank_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedCellBatch_sized_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.cachedPackedCellBatch_spec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedCellScatter_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedCellScatter_word,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedCellPublish_exec ] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Coupling interval execution axiom audit passed."
