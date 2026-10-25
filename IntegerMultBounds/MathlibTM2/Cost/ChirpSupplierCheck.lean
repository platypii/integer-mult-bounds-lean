module

import IntegerMultBounds.MathlibTM2.Cost.ChirpCallerSizing
import Lean.Util.CollectAxioms

/-! Integrity audit of the chirp supplier and fixed-startup comparisons. -/

open Lean in
run_cmd do
  for name in #[
      `IntegerMultBounds.MathlibTM2.Cost.chirp_size_quadratic,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_size_cube_factor,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_packed_log_factors_le,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_ringBound_le,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_rmul_le,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_selected_packed_bounds,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_selected_rpRec_le,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_selected_work_le,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_selected_group_work_le,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_product_fixed_quadratic,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_line_fixed_quadratic,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_selected_fixed_le,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_size_sq_le,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_address_sq_le,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_selected_fast_le,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_selected_long_line_le,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_selected_group_le,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_selected_long_group_le,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_bank_load_cost,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_consumer_banks_cost,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_counters_cost,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_tables_setup_le,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_initialize_cost_le,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_selected_setup_le,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_selected_setup_cubic,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_selected_total_le,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_selected_amortized_le,
      `IntegerMultBounds.MathlibTM2.Cost.chirpForwardCostConstant_nonneg,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_selected_allowance_le,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_selected_amortized_budget,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_caller_size_gates,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_source_half,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_complement_ge,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_runtime_axis_bounds,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_runtime_size_gates,
      `IntegerMultBounds.MathlibTM2.Cost.chirp_runtime_group_cost ] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Chirp supplier and startup axiom audit passed."
