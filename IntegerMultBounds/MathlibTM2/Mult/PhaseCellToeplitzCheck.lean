module

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightHost

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderGeneratorRelease

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNumericalGeneratorRelease

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSizedGeneratorSetup

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratorSetupAccuracy

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReversedColumnAccuracy

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedColumn

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellColumnEncoding

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerColumnAccuracy

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerColumn

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerStepRhs

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerStepSetup

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerRowData

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeedExec

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSetupFits

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerWords

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGroupedExecution

import IntegerMultBounds.NLogN.PhaseCellLengthGroups

import IntegerMultBounds.NLogN.PhaseCellGeneratedVolume

import IntegerMultBounds.NLogN.PhaseCellGeneratedCover

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedAccuracy

import IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStagedExecution

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPayloadBank

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedAccuracy

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSizedExecution

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellQuarterCount

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedIndex

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedExecution

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishSetup

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishRows

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConstructedExecution

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArithmetic

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFetchOutputTable

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedInterior

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOutputFromHeaders

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOutputHeader

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComplementHeader

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUpperBatch
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUpperCropSetup
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUpperOperand
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTriangularPair
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTriangularPairRestore
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLowerCrop
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRingRelease
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairFinish
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairScale
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBranchInput
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMergeWord
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMergeStream
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMergeSetup
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMergeRange
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarRange
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarUnary
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarPrepare
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarCanonical
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInteriorProducts
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStageValues
import IntegerMultBounds.NLogN.PhaseCellGeneratorData
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellEncodedGenerators
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedInterior
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInteriorRun
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNumericalRun
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightedInput
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightedInputClose
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOutputClose
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedRun
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizationHeader
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutionSizing
import Lean.Util.CollectAxioms

/-! Integrity audit of the executed S3 triangular stages and its stream interpretation. -/

open Lean in
run_cmd do
  for name in #[
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.unarySize_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.coefficientWorkspaceWidth_bound,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generateCoefficientWidth_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.initializeCoefficientBank_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.loadCoefficientList_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.loadCoefficientHeaders_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.prepareCoefficientHeaders_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.coefficientHeaderState_fits,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.headerGeneratorSetup_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.headerGeneratorRelease_exec,
      `IntegerMultBounds.NLogN.PhaseCellIntegerGenerators.expPiNat_ratio,
      `IntegerMultBounds.NLogN.PhaseCellIntegerGenerators.coefficientNumerator_gaussian,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.correctExpEmit_do,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.coefficientExpCode_do,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.coefficientBody_do,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.coefficientStreamCode_do,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.coefficientHost_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.rowFactorWords_from_distances,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.constructFactorRow_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.factorRowStep_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.constructFactorPage_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.factorFactory_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.releaseFactorPage_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.numericalGeneratorSetup_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.numericalGeneratorRelease_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packGenerators_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.releaseGeneratorPage_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generateSetupWidth_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.integerSetupWidth_generator,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.generatePackedGenerators_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.generatorPage_length,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.generatorPage_reads,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.releasePackedSetup_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedGeneratorBank_accuracy,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.sizedGeneratorSetup_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.sizedGeneratorRelease_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.realWord_bits,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.bits_realWord,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.copyRealBits_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.divideRealWords_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generateReciprocalNumerator_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.cropReciprocal_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generateReciprocal_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.generateIntegerReciprocal_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.generateGenerators_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.generatorBank_accuracy,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.shiftReverse_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.reversedColumnWords_eq,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generateReversedColumn_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.reversedColumn_decode,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.reversedColumn_error_precision,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.generateEncodedColumn_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.encodedColumnBank_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generateColumnEncoding_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.encodedColumn_decode,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.encodedColumn_error_precision,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.IntegerRowContext.decode,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.rowColumnWords_getD,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.IntegerGeneratorContext.column_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.IntegerGeneratorContext.corner_pos,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.replaceColumn_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.copyFactorPage_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generatorRowJobs_factor_length,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.IntegerRowContext.replaceColumn,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.preparedIntegerStep_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.integerIteration_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.IntegerGeneratorContext.update,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.IntegerGeneratorContext.next,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.integerIterations_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.prepareIntegerIterations_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.initializeIntegerColumn_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.generateIntegerColumn_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.reversedSeedStream,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generateReverseSeed_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generateRhsPage_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generateIterationRhs_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.generateRhsIntegerStep_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.stageIntegerRow_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.finishIntegerRow_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.integerRowCall_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.consumeIntegerRow_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.IntegerRowContext.update,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.integerRows_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generatorRowJobs_results,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generatorRowJobs_factors,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generatorRowJobs_rhs,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generatorRowJobs_fits,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.integerGeneratorStep_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.prepareIntegerStep_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.realWeightStream_exec_of_fits,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.tdivN_precision_zero,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.unarySetup_room_of_width,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.loadBank_exec_of_width,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.counterSetup_exec_of_width,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.prepare_exec_of_width,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.counterR_ready_of_work,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.integerProducts_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.subtractRowStep_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.subtractRow_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.integerRow_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.integerRowPrepared_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.coefficientNumerator_fits,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.rowColumnWords_eq,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.rowProducts_eq,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.rowResult_eq,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.generatorRow_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.csyms_power_two,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.seedWords_eq_column,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.seedStream,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generateSeed_exec,
      `IntegerMultBounds.NLogN.PhaseCellIntegerGenerators.coefficientNumerator_abs_le,
      `IntegerMultBounds.NLogN.PhaseCellIntegerGenerators.columnNumerators_one,
      `IntegerMultBounds.NLogN.PhaseCellIntegerGenerators.rowTerms_sum,
      `IntegerMultBounds.NLogN.PhaseCellIntegerGenerators.rowTerms_abs_le,
      `IntegerMultBounds.NLogN.PhaseCellIntegerGenerators.rowPartial_abs_le,
      `IntegerMultBounds.NLogN.PhaseCellIntegerGenerators.rowAccumulator_abs_le,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.rowProduct_fits,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.rowPartial_fits,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.rowAccumulator_fits,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.integerSetupWidth_bounds,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.integerSetupWidth_mono,
      `IntegerMultBounds.NLogN.PhaseCellIntegerGenerators.columnNumerators_corner_pos,
      `IntegerMultBounds.NLogN.PhaseCellIntegerGenerators.columnNumerators_abs_le,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.integerReciprocalWord_eq,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.columnNumerator_fits,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.reciprocalNumerator_fits,
      `IntegerMultBounds.NLogN.ToeplitzInverse.generatorOffDiag_scale,
      `IntegerMultBounds.NLogN.ToeplitzInverse.generatorOffDiag_int_div,
      `IntegerMultBounds.NLogN.ToeplitzInverse.dyadicGeneratorIter_spec,
      `IntegerMultBounds.NLogN.PhaseCellIntegerGenerators.coefficient_eq,
      `IntegerMultBounds.NLogN.PhaseCellIntegerGenerators.columnNumerators_spec,
      `IntegerMultBounds.NLogN.PhaseCellIntegerGenerators.columnNumerators_getD,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.dyadicWord_eq,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.integerColumnWords_eq,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.integerReversedColumnWords_eq,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.lengthGroup_sized_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.lengthGroup_accuracy,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.mem_lengthKeys,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.mem_lengthGroup,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.lengthKeys_nodup,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.lengthGroup_nodup,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.lengthKey_pos,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.lengthGroup_pos,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.lengthGroups_volume,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.lengthGroups_list_volume,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.lengthGroups_volume_le,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.lengthGroup_solver_geometry,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.coordinateSet_eq_filter,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.activePhases_toFinset,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.physicalInterior_card,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.intervalLength_eq_card,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.sum_intervalLength,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.sum_intervalLength_le,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.activePhases_volume,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.activePhases_volume_le,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.mem_activePhases,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.activePhases_nodup,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.activePhases_length_le,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.activePhase_interval,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.generatedIntervals_cover,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.generatedIntervals_unique,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.generatedIntervals_cover_iff,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.mem_coordinateSet,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.generatedInterval_spec,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.intervalLength_pos_iff,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.generatedInterval_solver_geometry,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generatedCell_accuracy,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.phaseIndex_eq,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.isInterior_spec,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.mem_interiorIndices,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.interiorIndices_nodup,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.interiorIndices_lt,
      `IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.mem_interiorSet,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.emptyInputBank_output_frame,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.stagedCell_sized_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.copyRepeated_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.pageAddress_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.fetchPage_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.stagePayload_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.stagePayloadBank_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.publishedCell_accuracy,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.publishedCell_sized_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.quarterCount_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.execution_error_bits,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.execution_stage_bound,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.cell_error_budget,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.execution_cell_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.reversedRows_getD,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.publishedWords_getD,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.publishedWords_read,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.executedRun_y_published,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.outputRows_spec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.publishedWords_length,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.publishWords_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.executedOutputWords_length,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.publishedCell_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.publishFromDimensions_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.publishRows_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.constructedCell_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.preparedOutput_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.cellArithmetic_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.fetchOutputTable_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.closedInputInterior_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.outputFromHeaders_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.extendOutputShift_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.outputShiftHeader_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.outputHeaders_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.complementHeader_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.zipWith_flatMap_rows,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.weightedInputNumerators_flatMap,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.executedInputRows_flatMap,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.installInput_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.inputInstallBank_frame,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.inputInstallBank_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.inputSourceBank_frame,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.inputStage_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.inputInterior_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.execution_precision_bound,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.execution_width_bound,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.execution_input_width,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.executedRun_sized_valid,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.prepareNormalization_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.inputInteriorFromPrecision_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.cellIndex_row,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.cellIndex_coordinate,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.reversedRowTable_getD,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.cellSourceRows_length,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.cellWeightRows_length,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.cellSourceRows_getD,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.cellWeightRows_getD,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.cellWeightRows_bounds,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.executedInputRows_length,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.executedInputRows_disk,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.executedInputRows_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.executedInteriorWords_length,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.executedInteriorWords_norm,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.executedRun_valid,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.scalar_product_norm,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.scalar_products_norm,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.scaled_output_norm,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.scaled_output_fits,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.output_weight_norm,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.weightedOutputNumerator_fits,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.weightedOutputNumerator_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.output_weight_precision,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.cell_output_scale,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.cell_output_weight_precision,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.outputWeightWords_norm,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.weightedOutputNumerators_length,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.weightedOutputNumerators_block,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.weightedOutputNumerators_word_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.scaleOutputPrefix_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.closedOutputWeights_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.routeWeights_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.runWeights_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.prepareWeights_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.releaseWeightCounters_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.applyWeights_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.closedWeights_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.closedWeightedInput_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.normalized_weight_precision,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.weightedInputNumerators_error_precision,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.value_normalized_product,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.normalized_product_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.normalized_product_norm,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.normalized_product_disk,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.normalized_product_real_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.fits_of_value_power,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.normalized_product_fits,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.realWeightStream_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.realWeightStream_output_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.reciprocalWeightWords_norm,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.weightedInputNumerators_length,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.weightedInputNumerators_disk,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.weightedInputNumerators_block,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.weightedInputNumerators_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.weightedInputStream_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.finish_stream_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.rationalValue_cast,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.weightData,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.weightData_cast,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.reciprocalWeightWord_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.weightedInputWord_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.weightedOutputWord_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.reciprocalWeightWord_bounds,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.weightedInput_argument_bound,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.weightedInputWord_disk,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.weightData_bounds,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.weight_stage_precision,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.weightedInputRows,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.weightedInputRows_length,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.rationalOutputValue,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.rationalOutputValue_cast,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.numericalRun,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.numericalRun_valid,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.preparedInterior_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.interiorRun,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.interiorRun_valid,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.preparedRun,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.preparedRun_valid,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.rationalWord,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.rationalWord_value_re,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.rationalWord_bounds,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.rationalWord_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.rationalWord_nonneg,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.rationalWord_abs_le_one,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.rationalWord_disk,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.rationalWord_zero,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.rationalWord_norm,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.normalizedWords_block,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.normalizedWords_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.normalizedWords_disk,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.columnWords_disk,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.reversedColumnWords_disk,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.reciprocalWord_norm,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.columnWords_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.reversedColumnWords_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.reciprocalWord_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.normalizedWords_real,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.encoded_setup_precision,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.columnWords_error_precision,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.reversedColumnWords_error_precision,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.reciprocalWord_error_precision,
      `IntegerMultBounds.NLogN.PhaseCellGeneratorData.column_abs_le,
      `IntegerMultBounds.NLogN.PhaseCellGeneratorData.reversedColumn_abs_le,
      `IntegerMultBounds.NLogN.ToeplitzInverse.generatorOffDiag_eq,
      `IntegerMultBounds.NLogN.ToeplitzInverse.generatorOffDiag_map,
      `IntegerMultBounds.NLogN.ToeplitzInverse.generatorIter_map,
      `IntegerMultBounds.NLogN.ToeplitzInverse.generator_fixed_point,
      `IntegerMultBounds.NLogN.ToeplitzInverse.generatorStep_error,
      `IntegerMultBounds.NLogN.ToeplitzInverse.generatorIter_error,
      `IntegerMultBounds.NLogN.ToeplitzInverse.generatorIter_column_error,
      `IntegerMultBounds.NLogN.ToeplitzInverse.rationalGenerator_column_error,
      `IntegerMultBounds.NLogN.PhaseCellGeneratorData.column_error,
      `IntegerMultBounds.NLogN.PhaseCellGeneratorData.reversedColumn_error,
      `IntegerMultBounds.NLogN.PhaseCellGeneratorData.column_corner_lower,
      `IntegerMultBounds.NLogN.PhaseCellGeneratorData.reciprocal_bounds,
      `IntegerMultBounds.NLogN.PhaseCellGeneratorData.reciprocal_error,
      `IntegerMultBounds.NLogN.PhaseCellGeneratorData.iteration_error_precision,
      `IntegerMultBounds.NLogN.PhaseCellGeneratorData.column_error_precision,
      `IntegerMultBounds.NLogN.PhaseCellGeneratorData.reciprocal_error_precision,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.cellIndex,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.pairNumerator_word,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.upperNumerator_real_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.pairNumerator_real_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.branchScalar_real_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.cell_stage_precision,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.copyAfterPrefix_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.fetchScalar_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.rawRows_length,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.fetchCanonical_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.applyCanonical_with_x_tail_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.interiorProducts_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.scaled_scalar_real_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.inputBankWithTails_update_y,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.startWithTails_update_y,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.startWithTails_update_output,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.reverseInput_with_x_tail_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.upper_batch_with_x_tail_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.upper_crop_stage_with_x_tail_frame,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.staged_input_release_with_x_tail_frame,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.upperToLowerInput_with_x_tail_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.triangularPair_with_x_tail_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.releaseUpperInput_with_x_tail_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.triangularPairRestored_with_x_tail_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.finishTriangularPair_with_x_tail_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.compactTriangularPair_with_x_tail_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.twoBranches_with_x_tail_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.branch_input_with_x_tail_frame,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.twoBranchesFromSingleInput_with_x_tail_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.fixedBranchMerge_with_x_tail_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.mergedBranches_with_x_tail_exec,

      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.takeFromWords_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.route_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.routeR_ready,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.routeR_clean,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.finish_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.run_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.applyScalar_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.applyCanonical_exec,

      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.bank_injective,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.bank_lt,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.loadBank_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.loadedR_off,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.loadBank_holds,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.counterSetup_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.bank_covers,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.loadedR_length,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.setupPorts_nodup,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.prepare_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.prepareCanonical_exec,

      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.cr_injective,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.mul_injective,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.cr_range,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.cr_mul,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.cr_fresh,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.mul_clean,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.counterR_ready,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.unarySetup_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.table_room,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.unarySetup_room,

      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.realScalarStream_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.realScalar_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.realScalar_output_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.realScalar_product_fits,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.realScalar_output_error_bounded,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.pairNumerator_norm,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.branchDifference_norm,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.branchScalar_output_error,

      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.halfCount_loop_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.halfCount_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.branchWords_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.fixedBranchMerge_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.pairRows_length,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.pairNumerator_stream,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.mergedBranches_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.pairNumerator_disk,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.fits_of_disk,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.branchDifference_word,

      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.takePrefix_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.mergePair_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.mergeFromWords_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.mergeStream_exec,
      `IntegerMultBounds.MathlibTM2.Fast.subWord_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.fits_sub,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.value_sub,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.mergeWord_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.rowBank_flatMap,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.pairRows_rowBank,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.rowBank_length,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.rowBank_disk,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.twoBranches_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.duplicateStream_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.branch_input_frame,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.twoBranchesFromSingleInput_exec,

      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.lower_scale,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.upper_scale,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.upperOperand_block,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.upperOperand_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.scale_stage_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.scaledUpper_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.scaledPair_output_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.lower_re,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.upper_re,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.lower_real_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.upper_real_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.scaledUpper_real_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.scaledPair_real_output_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.value_block_im_zero,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.upper_cell_scale,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.lower_cell_scale,

      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.publishPairResult_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.finishTriangularPair_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.compactTriangularPair_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.lower_records_disk,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.lowerRows_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.lowerCropFromDimensions_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.releaseRingBatch_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.releasePrefix_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.releaseFromDimensions_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.releaseRows_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.staged_input_release_frame,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.releaseUpperInput_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.triangularPairRestored_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.upper_crop_stage_frame,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.upperToLowerInput_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.triangularPair_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.upperRows_flatMap,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.upperOperand_length,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.upperOperand_disk,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.coefficientTableHost_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.weightStreamCode_do,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.weightHost_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.correctExpValue_do,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.correctedExpCode_do,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.weightArgument_do,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.weightEmit_do,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.weightBody_do,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.similarityGridNumerator_fits,
      `IntegerMultBounds.NLogN.PhaseCellRationalArgs.similarity_ratio,
      `IntegerMultBounds.NLogN.PhaseCellRationalArgs.similarityNumerator_le,
      `IntegerMultBounds.NLogN.PhaseCellRationalArgs.similarity_sample,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.weightData_output_word,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.weightData_reciprocal_word,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.Fixed.exec_with_tails,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.lower_batch_with_tails_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.packLoop_prefix_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.packBatch_prefix_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.packBatch_coeffs_prefix_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.batchProgram_prefix_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.batchFromUnary_prefix_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.lower_convolution,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.upper_convolution,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.block_reverse,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.lower_output_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.upper_output_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.lower_batch_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.reverseRowsInPlace_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.reverseRowsFromDimensions_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.inputBank_update_y,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.start_update_y,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.start_update_output,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.reverseInput_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.upper_batch_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.sliceCoeffs_get,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.sliceCoeffs_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.sliceNext_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.sliceLoop_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.sliceBatch_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.sliceStream_eq,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.sliceStream_get,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.sliceBatch_rpStream_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.sliceStream_disk,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.sliceStream_word,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.upper_coeff_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.upper_records_disk,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.upperRows_disk,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.upperRows_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.upper_crop_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.upperCropFromDimensions_exec ] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Phase-cell Toeplitz stage axiom audit passed."
