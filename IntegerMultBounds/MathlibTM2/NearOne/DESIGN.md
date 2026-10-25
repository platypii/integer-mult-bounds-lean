# Near-one dimensions: what still pins ε ≤ 1/2

The selected route (plan `plan/D-sharper-bound.md`, §§8–9, M8b) runs at a dimension exponent
`ε` close to `1` (`ε = (1-η)/(1+q)`, about `0.998` at the selected witness): its binding margin
is the compact layer `εq`, so moving `ε` from `31/64` to near `1` doubles the saving for any
supplier. The moduli no longer limit `ε` (`Primes/DESIGN.md`) and the prefix margin is `1 - ε`
(`Balanced/DESIGN.md`, M5a). This note covers what remains:

* (a) the sizing, which no longer uses `d² ≤ b`;
* (b) the remaining M7 items, the faster rounded Gaussian inverse and its execution;
* (c) the exposure margin `(1 - ε)(1 - τ)`;
* (d) staged estimates.

Notation: `b = ⌈log₂ n⌉`, `p = 6b`, `d = ⌊b^ε⌋` (`d^64 ≤ b^31` at `ε = 31/64`), `ℓ ≈ b/d`
(`b ≤ 2dℓ`, `3dℓ ≤ p`), `K` the compact chunk, `a_b = 1 - τ = 296/10^11`,
`a_c = 1 - σ = 418/10^12`, `1 - λ' = 21/2^33`, `δ = 2^-7`.

## (a) The sizing without `d² ≤ b`

At `ε > 1/2` the fact `d² ≤ b` is false, and so is every fact equivalent to it: `d ≤ ℓ` means
`d² ≲ b`, since `ℓ ≈ b/d`. `Mult/Sizes.lean` no longer states either; its sizing rests on two
facts valid for every `ε < 1`, `d^64 ≤ b^31` (`d_pow_le`) and `b^33 ≤ (2ℓ)^64` (`b_pow_le_ℓ`,
from `b ≤ 2dℓ`), and on the regime facts below.

**The regime.** `Big n : 2 ≤ n ∧ 2^192 + bigDim ≤ d n`. `bigDim` is `d` at the threshold of the
eventual bundle `BigFacts` plus one, so `d` monotone (`d_mono`) turns every bundled eventual fact
into a deterministic `Big.*` fact (`bigFacts_of_bigDim_le`). The bundle:

| fact | statement | consumers |
| --- | --- | --- |
| prime supply | `PrimeSupply n` (including `4 ≤ ℓ`) | `Big.good`, `Big.srcLen_eq`, `Big.four_le_ℓ`, `Big.two_le_ℓ` |
| chunk room | `2^8 d^7 < ℓ^8` (`Big.chunk_room`) | `CompactSizes.two_Kroot_lt_ℓ`, hence `K_eq_unif`, `mod_K_succ_le`, `K_succ_le_ℓ`; `Big.K_succ_le_ℓ` for the legacy chunk |
| Gaussian width room | `64 d (⌈log₂ p⌉ + 3) ≤ b` | `Big.sixteen_d_alpha_sq_le_b` (through `α² < 4u`), `Big.four_gamma_le_b`, `Big.gamma_le_real`, `Big.band_budget`, `SmallGapSizes.uSG_mul_d_le` |
| dimension below the axis | `d ≤ 2^(ℓ-1)` (`Big.d_le_two_pow_pred_ℓ`) | `DistWidth.ds_d_le_r`, `ds_d_mul_r_le`, `ds_lay_widths`, `DistCost.ds_sum_t`, `DistCostSrc.ds_r_le_T` |
| precision below the axis | `8p ≤ r` (`Big.eight_p_le_r`) | `PrepA.pre_p_le_s` |

Facts that follow without the bundle: `d ≤ b` (`d_le_b`), `F d ≤ b` for `F^64 ≤ b^33`
(`mul_d_le_b`; `Big.eight_d_le_b`, `CompactCallerOverheadR.compactCallerR_eventually_width`),
`ℓ → ∞` (`tendsto_ℓ`), `p^C ≤ r` eventually (`eventually_pow_p_le_r`, hence
`MatchSynPipe.mr_b_pow_le_r`), the prime supply with `d^33 ≤ (2ℓ)^31 ≤ (ℓ - 1)^62`.

The exponent sum of the compact caller's reservation pieces is at most `D (m + G)`
(`synE_zero_le_radix`: the lowest base-`m` digit is below `m`, every other level scale is `G`), so
the working width needs only `(cG + G + m + 30) d ≤ b`.

**What stays tied to the exponents.**

* The proofs of the bundle (`eventually_chunk_room`, `eventually_gauss_room`, the prime supply's
  `B = 2`) and of `b_pow_le_ℓ`, `d_pow_le_ℓ` use the numbers `64`, `31`, `33`. For `ε = N/M` they
  become `d^M ≤ b^N`, `b^(M-N) ≤ (2ℓ)^M`, with the same structure.
* The chunk room encodes the chunk exponent `7/8`: it holds eventually exactly when
  `(7/8) ε < 1 - ε`, i.e. `ε < 8/15`. Near one the chunk exponent `c` must satisfy
  `εc < 1 - ε`; with `c → 0` the chunk exchanges cost `ε c a_b`, which makes M5b's routing
  (margin `a_b`) necessary (`Balanced/DESIGN.md`).
* `b_lt_d_succ_pow` (`b < (d+1)^8`, needs `ε ≥ 1/8`) and its users `Big.alphaU_le_d`, `clog_p_le`,
  `CompactCallerGuardPower` (`cExp · upperPower`).
* The machine computes `d = iroot 64 (b^31)`: `ParamProg.pm_s3`,
  `Fast/CompactDyadicParamStageCore.lean`, `Fast/CompactDyadicDimension.lean`,
  `Mult/CompactDyadicRootRoom.lean`.
* `DistWidth.parameter_width_small_r` uses `d^64 ≤ b^31` numerically for `b ≤ 2 → d = 1`.
* The real-exponent envelopes (`CompactStageGrowth`, `CompactInterim`) rewrite with
  `epsilon_eq`.

## (b) M7: the faster Gaussian inverse and its execution

**Status** (`PLAN.md`, M7 row; plan §8, M7a/M7b). Paused. Done and checked, off the main route
(nothing in `mulInTime` uses them): b1, b2, b3a and b5a, and the math of b3s with the ring
arithmetic of b5 (items 1–5 below; files `NLogN/SchurPerturbSolve`, `PhaseCellRoundedSchur`,
`PhaseCellRoundedInterior`, `PhaseCellRoundedInverse`, `PhaseCellBoundaryOrder`,
`PhaseCellBoundaryFold`, `PhaseCellConcreteInterior`, `PhaseCellConcreteSolve`, `ChirpForward`,
`Mult/PhaseCellB0Line`, `Mult/ShortConv`, `Mult/ChirpRing`). What remains is machine work, and
its payoff needs the bit supplier: near one the binding margins are the supplier-driven layer,
chunk and exposure margins (the table in (c)).

**Resume point.** The b3s machine glue: a generic wrapper around `ldRpStage` (`Fast/LoadRing`) on
its own register enum, placed by a layout in the manner of `RpLayout`/`RpRuns`
(`Fast/RingProdRegs`), so that the b3 and b5 line machines share it. It pads `M` blocks of `A`
input records and `M` kernels of `B` records into the stream format `rpStream M X` with records of
`2^l` coefficients (zero beyond `A`, resp. `B`), runs the stage, and keeps a range of coefficients of
each output record; its contract is stated against `rpOut_recOf`, its cost against `rpCost_le`.
After it: b5b against `chirpAR` and `chirpAR_approx` (setup tables from the exponential evaluators
of `Fast/TableExp` and `NLogN/PhaseCellExpSample`, the line machine with overlapping block windows
on a periodically extended line, the replacement of the window line of `Fast/ResampA*`, costs in
`Cost/MatchResampA`), then b3b and b3c against `pcSolve` and `phase_resampB₀_spec`.

**Checked pieces on the main route** (they serve the banded `B̃₀` of the present multiplier,
`Mult/BandSpec`, `ConcreteB0`, `Fast/BandFits`): `NLogN/PhaseCellFactorization`
(`smallgap_factorization`), `PhaseCellMatrix`, `PhaseCellOperator` (operator error `2^(-45p)`),
`PhaseCellSharpInverse` (inverses `4p`, rounded `8p`), `PhaseCellBoundary` (margin `1/(8p)`),
`PhaseCellBandSolve`, `PhaseCellFold`, `PhaseCellFoldSolve`, `PhaseCellPerturb`,
`PhaseCellMachMatrix`, and the `Schur*`, `Row*`, `Band`, `Tail*`, `Scan`, `Intervals` support.

**Checked pieces of the phase-cell inverse, off the main route:**

* `ToeplitzInverse` (`gohberg_semencul`), `ToeplitzDominant`, `PhaseCellToeplitz`
  (`block_inverse`), `ToeplitzApply`, `ToeplitzRounded` (`rounded_apply`), `ToeplitzScaled`;
* `PhaseCellInteriorSolve` (`cell_solve`), `PhaseCellRoundedCell`, `PhaseCellInteriorCover`,
  `PhaseCellWeightRange`;
* `SchurIdentify` (`schurOp_eq_run`), `SchurBlockSolve` (`four_step`), `SchurBlockError`,
  `PhaseCellBoundaryLU` (`rounded_boundary`), `PhaseCellRoundedSolve` (`rounded_four_step`);
* the files of b1–b5 listed under **Status**.

`PhaseCellFourStep` and `PhaseCellBandFill` are imported by no module and not by the root, so the
default build does not check them.

**The remaining items and what each builds on:**

1. **Rounded boundary factorization** (`NLogN/SchurPerturbSolve.lean`,
   `PhaseCellRoundedSchur.lean`, `PhaseCellRoundedInterior.lean`, `PhaseCellRoundedInverse.lean`).
   The reduced boundary matrix has the Schur complement entries `A_ij - A_iI R(A_Ij)`
   (`run_entry`). The computed boundary matrix takes these entries on a band containing the
   support of the exact one from computed interior responses within `eR`, with one rounding
   `η`, and is zero elsewhere; each row is within `|B| (η + eR)` of the exact one (`rounded_schur_rows`). The
   machine-faithful solve `bandSolveG` of a computed matrix within row mass `ε` of a dominant
   one adds `ε` to the backward error of the factors (`bandSolveG_perturbed_error`), so the
   boundary values are within `e₃ = 2^16 p³ N (N η + eR + θ) (1 + ρ)` of the exact Schur
   solution for `N ≥ |B|` and `2^13 p² N (N η + eR + θ) ≤ 1` (`rounded_schur_solve`, in any
   elimination order); the backward route needs no forward bounds on the factors, so the factor
   hypotheses of `rounded_boundary` are not used. Valid rounded cell runs on every cell
   interval give the interior errors `η + 64 s η V + 2(η + C η)` (`rounded_interior`, from
   `rounded_cell` and `interior_cover`), and `rounded_inverse` composes the five stages through
   `rounded_four_step`: boundary values within `e₃ + 8p (e₁ + e₂)`, interior values within
   `e₅ + 8p (e₄ + e₃ + 8p (e₁ + e₂))`, with `ρ = (1 + 8p) β + e₁ + e₂` for `|b| ≤ β`.
2. **Boundary ordering** (`NLogN/PhaseCellBoundaryOrder.lean`). The boundary `univ \ I` has at
   most `2w (t - s + 1)` vertices (`boundary_card`: a non-interior vertex lies within `w` of an
   array end or of one of the at most `t - s` cell starts). In physical rank order every coupling
   of the boundary system lies in the bordered band `RankRel B (4w)`: ranks within `4w`, or a
   vertex among the last `4w` ranks for the wrap-around entries (`schur_rankRel`). The band is
   closed under fill, so every exact or rounded LU factor entry in that order stays in it
   (`boundary_factors`, `boundary_factors_r`), and a row outside the last `4w` ranks meets at most
   `12w + 1` boundary vertices (`rankRel_row_card`).
3. **Tape costs.** The phase-cell line replaces the banded line of `B̃₀`. It plugs into the
   existing interface `Mult/ConcreteB0.concrete_resampB₀_specX`: any real line solver of
   `realMatrix` within `e` on right-hand sides at most `1/2` gives the pipeline interface of
   `B̃₀`. Its per-line cost is `O(t p^(1+δ) (1 + w²/d))` against the banded line's
   `O(t w p^(1+δ))` (source: `downstream-phase-cell-inverse.md` of the pinned CrocSwap
   references), which turns the tensor exponent `ε + δ + (1 - r)/2` into
   `max(ε + δ, 1 - r + δ)`. Three parts:
   * **b3a, the concrete solve** (math only; `NLogN/PhaseCellBoundaryFold.lean`,
     `PhaseCellConcreteInterior.lean`, `PhaseCellConcreteSolve.lean`). The boundary system is a
     cyclic band of half width `4w` in boundary rank (`schur_cycRel`); the folded boundary order
     `bFoldOrder` makes it a plain band of half width `8w + 1` closed under fill
     (`cycRel_foldBRel`, `boundary_factors_fold`), the format of `Fast/BandLine`. The cell
     interval of an interior vertex runs between the extreme interior vertices of its cell
     (`cell_interval`); the concrete cell runs round every stage once (`cellRunOf`, valid by
     `cellRunOf_valid`, scaled inputs at most `(C + 1) 2^(8p+2)` since the similarity weights lie
     in `[2^-(8p+1), 1]`), and `pcInterior_error` bounds the interior solve. `pcSolve` composes
     the cell runs, the two rounded couplings, the machine solve `bandSolveG` with the rules
     `machMul`, `newtonR` (Newton at `β = 1/(32p)`) of the computed boundary matrix in folded
     order, and the recovery; it is within `2^(8p+46) p⁷ s² η` of the exact solution for
     `|b| ≤ 1/2` and `2^(8p+46) p⁷ s² η ≤ 1/2` (`pcSolve_error`). Through
     `concrete_resampB₀_specX` the line map `bandJtX p j (pcSolve …)` has the pipeline
     interface of `B̃₀` (`Mult/PhaseCellB0Line.phase_resampB₀_spec`). Its working precision is
     about `9p + 46 + 7 log₂ p + 2 log₂ s` bits against the banded line's `5p`.
   * **b3b, the machines.** A per-axis loader (the `prep` of the generic driver `rsbAllG`):
     cell and boundary masks from the phase generator (`PhaseCellScan`), reciprocal weights,
     Gohberg–Semencul generators per cell length, coupling tables, the computed boundary matrix
     and its folded factor tables by the existing factor machine (`Fast/BandFactor`). A line
     machine: split the line into cells, per cell four triangular Toeplitz products as negacyclic
     products of size at least `2L` on the vendored ring product (`Fast/RingProd`), the coupling
     scans, the boundary solve by the passes of `Fast/BandLine` on the boundary records, the
     second interior pass, and the merge.
   * **b3c, the costs.** The line cost `O(t p^(1+δ) (1 + w²/d))` plus a polynomial setup per
     axis, matched into `rsbAllCostG` as `Cost/MatchBandB.lean` does for the banded line.
4. **Bulk execution (M7b).** Ordered core/halo windows of the same rounded matrix
   (core `L = 2^⌈8 log₂ p⌉`, halo `A = 4096 p³`, Neumann depth `J = 512 p²`, locality error
   below `2^(-16p)`), period cuts kept in every window, tensor errors in row norm without a volume
   factor, then the tape transfer: source halos fit `L ≥ 64 d A`, target halos of total volume
   below `2T`, alternating overlap tapes, factor-page reuse, cropping after each axis, final
   prime-box order. Nothing exists yet.
5. **The forward map.** `totResamp` charges the `Ã` window of `2m + 1 ≤ 4α√p` lines per
   output (`Cost/MatchResampA.lean`); with `α² ≍ p^r` this grows with `r`. The selected route
   replaces it by a chirped-correlation forward map in `O(M(p))` per output
   (`notes/fast-gaussian-resampling.tex`). Without it the Gaussian margin stays below `1/2 - ε`.
   * **b5a, the math** (`NLogN/ChirpForward.lean`). Outputs in blocks of `m`; the block starting
     at `k₀` reads the `3m + 1` inputs from `⌊s k₀/t⌋ - m`, which contain the truncation window
     of each of its outputs (`truncWindow_subset_block`), so its sums are within `3/(α 2^p)` of
     `S u` (`resampS_superset_err`, `chirpBlock_err`). The chirp identity splits each weight
     into an output factor `exp(πλθ b²)`, an input factor and a correlation kernel
     (`chirp_weight`, `chirpBlock_split`). `chirpA` computes a block from tables within `η` of
     the factors: the scaled inputs rounded once, the exact correlation (`chirpCorr`), the
     output factor over `2^Γ`, the shift, the factor `1/(2α)` and the `p`-grid rounding. With
     `exp(πλθ b²) ≤ 2^Γ` on a block (`chirpE_le_two_pow` from `πλθ m² ≤ Γ log 2`) and
     `2^(p+Γ) (12m + 7) η ≤ 1/2`, it approximates `Ã` with scaled error `4` independently of
     `m` (`chirpA_approx`; clamped, the pipeline interface, `chirpA_clamp`), against the
     window's `(4(2m + 1) + 3)/2`. The output stage `chirpAG` takes any computed correlation
     within `ζ` of the exact one (`chirpAG_approx`).
   * **b3s, the shared convolution** (`Mult/ShortConv.lean`, math part). Zero-padded records of
     size `r ≥ A + B - 1` have the linear convolution as negacyclic product
     (`negacyclicMul_recOf`); the ring product's output numerators on records of size `2^l` are
     the truncated divisions of the integer convolution by `2^(p+l)` (`rpOut_recOf`), and the
     rescaled output is within `2r/2^p` of the convolution (`pwC_recOf_err`). The block
     correlation of b5 has `A = 3m + 1` inputs and `4m` kernel values, so `r ≥ 7m`; the cell
     products of b3 have `A = B = L`, `r ≥ 2L`.
   * **The shared block machine** (`Mult/ShortConvUnary.lean`). `fromUnary_exec` starts
     with raw Gaussian-integer coefficient blocks and unary `p,l,w`, generates both
     symbol-padding counters and the header, packs the zero-padded records, invokes
     the existing ring-product program, and clears every generated word. Only the
     full output stream changes; all inputs, left stacks, private scratch and user
     state are restored. `ShortConvExec.coeff_err` links the returned numerators to
     the `2r/2^p` error bound. `unaryCost_le` prices every phase by one packed-product
     bound plus linear stream and header work. `ShortConvCheck` audits the bridge.
     `ShortConvBatchProgram.batchProgram_exec` now also packs two raw equal-block
     streams, runs one product call and clears the packed banks, restoring all other
     registers, at most `M (rpRecBound + 44rw + 50) + rpFixCost + 20` steps. Its reusable
     symbol/padding/record counters and header are explicit shared setup inputs.
     `ShortConvBatchUnary.batchFromUnary_exec` now generates both block-symbol counts,
     both padding counts and the header from unary `p,l,w,a,b`, runs the batch and
     clears every generated word. Its complete bound is
     `M (rpRecBound + 44rw + 50) + rpFixCost + 46rw + 8w + 18l + ldrHeaderCost +
     2|header| + 63`: the setup and cleanup costs are independent of the record count.
     The unary record count remains an input dimension; binary dimension conversion
     is still caller work.
     `ShortConvSlice.copySlice_coeffs_exec` copies a coefficient interval with the
     complete source and scratch restored; `slice_coeff_err` retains the rounding bound.
     `ShortConv.reverseWords_coeffs_exec` (in `ChirpReverse`) now copies a coefficient prefix in reverse
     coefficient order while preserving the low-bit-first bits of each word. The source,
     width/count words, spectator suffix and workspace are restored; its cost is
     `len (16w + 19) + 6`. `ShortConv.correlationCoeffs_exec` (in `ChirpExtract`) skips the first `3m`
     coefficients and returns the next `m` in reverse order, at cost `34mw + 19m + 12`,
     restoring every register except the destination. Output offset `b` therefore reads
     coefficient `4m - 1 - b`; `correlationTape_coeff` proves exact signed decoding and
     `correlationTape_err` gives the rescaled `8r/2^p` error directly on returned symbols.
     `ChirpExtractCheck` audits the bridge.
     `ShortConv.correlationFromUnary_exec` (in `ChirpSetup`) now generates the `3mw`
     skip count from unary `m,w`, extracts, and clears both generated words at cost
     at most `52mw + 56m + 24`. `ShortConv.chirpProduct_exec` (in `ChirpProduct`)
     composes the raw-block S1 call with that extractor, clears the temporary full
     product, and changes only the destination register. For raw operand lengths
     `3m+1,4m`, `m ≥ 1` and `7m ≤ r`, it costs at most
     `unaryCost p l w (3m+1) (4m) + 52mw + 56m + 2rw + 26`.
     `chirpProductCost_le` replaces `unaryCost` with its proved packed-product bound.
     `ShortConv.correlationTape_chirpRingCorr` (in `ChirpProductMath`) identifies the decoded output
     with the analytic ring correlation when the input numerator records represent
     the halved chirp input and kernel; `correlationTape_chirpCorr_err` then transfers
     the analytic `8·2^l/2^p` correlation error to the returned tape. Those representation
     hypotheses remain obligations of operand production. `ChirpProductCheck` audits
     the full shared namespace, including setup, execution and the analytic bridge.
     `ShortConv.correlationBatch_rpStream_exec` (in `ChirpBatch`) now selects all blocks
     from S1's shared `rpStream` result, preserving block order and word bit order. It
     restores the full source (including spectator suffixes), counters and scratch,
     changing only the destination, at cost `M (38mw + 19m + 6rw + 23) + 8`.
     `correlationStream_get` identifies output position `n m + b` as coefficient
     `4m - 1 - b` of record `n`. `correlationBatchFromUnary_exec` (in `ChirpBatchUnary`)
     generates both shared counters and clears all three generated words, at total cost
     `M (38mw + 19m + 6rw + 23) + 18mw + 37m + 4w + 6rw + 9l + 35`.
     Empty batches and zero-length selected blocks are included. `ChirpBatchCheck`
     audits all shared declarations in its import closure.
     `ShortConv.chirpBatchProduct_exec` (in `ChirpBatchProduct`) now composes raw-batch
     S1 multiplication with generated-counter extraction and full-product cleanup.
     It calls the shared ring product once, returns `M m` selected coefficients in
     forward block/output order, and changes only the destination. Its public bound is
     `M (rpRecBound + 52rw + 38mw + 19m + 73) + rpFixCost + 52rw + 18mw + 37m +
     12w + 27l + ldrHeaderCost + 2|header| + 100` (`chirpBatchProductCost_le`).
     `ShortConv.correlationBatchTape_chirpRingCorr` (in `ChirpBatchProductMath`) identifies every
     decoded word with its record's analytic correlation, under the explicit operand
     representation interface. `correlationBatchTape_chirpCorr_err` retains the
     `8·2^l/2^p` bound independently of batch size. `ChirpBatchProductCheck` audits
     the full imported shared namespace.
     `ChirpTableArgs` gives computable integer numerators/denominators for all three
     chirp exponentials, including the exact natural-division block start. `ChirpTables`
     defines their natural Taylor/Machin numerators and proves the common `2/2^q` table
     error for `q ≥ 13` (with the positive evaluator's explicit exponent-range condition).
     Reading the output numerator at precision `q+Γ` normalizes its factor by `2^Γ`
     without another rounding. `chirpTable_records_norm` proves that these computed
     input/kernel factors and `rhoC q` yield unit-disk ring records.
     `ShortConv.tblChirpDistance_do` (in `ChirpTableDistance`) executes the shared squared-distance
     argument in nine table-machine atoms under explicit arithmetic overflow bounds,
     preserving dimensions, the pi/precision variables and the emitted stream. The
     same routine handles the shifted kernel with offset `2m-1`. `ChirpTablesCheck`
     audits the table arguments, error bounds and distance routine.
     `ChirpTableMachineArgs` and `ChirpTableOutputArgs` now compute all exponential
     arguments and sign bits in 17 and 8 atoms respectively. `ChirpTableEntry` composes
     those programs with evaluation and word emission. `ChirpTableBounds` discharges
     every argument/evaluator overflow check from a common envelope and proves the
     explicit width `W = 13q + 8 + 8 size(B) + 4` sufficient. One natural positive-exponent
     gate supplies both the machine branch guard and the analytic error condition.
     `ChirpTablePi` computes pi once per stream; `ChirpTableRows` and `ChirpTableStreams`
     execute rows with no supplied coefficient, exponent-argument or pi values.
     Negative rows cost `N (310q + 122) + 150q + 404` atoms; output rows cost
     `N (310q + 113) + 150q + 404`. `ChirpTableHost` lowers them to actual tape programs
     at cost `atoms · tblC W w + 2 Nw + 2`, with forward output order, preserved native
     and spectator stacks, and an exact resulting table-bank contract. `ChirpTableWordBounds`
     proves numerator bounds and exact signed decoding of emitted words with the stated
     guard bits. `ChirpTableMachineCheck` audits the entire imported shared namespace.
     `ChirpTableCleanup`, `ChirpTableRestored` and `ChirpTableRestoredHost` now clear
     the owned variables and restore the entire initial bank: only the destination stack
     changes. This adds 37 atoms per row, with the same compiler cost formula.
     `ChirpTableBlocks`, `ChirpTableShape`, `ChirpTableSchedule` and `ChirpTableBlockHost`
     now compute the row offset and length from `m`, generate every row at origin `j*m`
     in one host invocation, and restore the full bank. For row length `N`, the schedule
     costs `M (N (310q + 122) + 150q + 445) + 8 + S` atoms, where `S = 4` for
     input rows (`N = 3m+1`) and `S = 7` for kernel rows (`N = 4m`); lowering adds
     `2 MNw + 2` tape steps to the atom cost times `tblC W w`.
     `ChirpWindows` proves the cyclic extension and exact analytic input indices for
     `3m+1` windows without requiring `m ≤ s`; centres advance at most `m`, and
     advances telescope to the final centre. `ChirpGather` and `ChirpGatherControl`
     execute one fixed sweep step from a delimited unary advance packet, saving both
     consumed source and control prefixes for restoration. Its exact cost is
     `12L + 8D + 21` for window/advance symbol lengths `L,D`; its temporary counter,
     copy workspace, native stacks and user state are restored. `ChirpGatherLoop` and
     `ChirpGatherBatch` now execute the entire fixed sweep and restore both source and
     control streams: only the destination changes, at exact cost `M (14L+25) + 12D + 8`,
     where `D` is total symbol advance. `ChirpGatherWindows` and `ChirpGatherExec`
     specialize it to the actual cyclic chirp windows, in block order with coefficient
     words intact. Total advance is `chirpCenter s t m M · w`, at most `(s+m)w` for
     valid block starts. `ChirpControlArgs`, `ChirpControlEmit`, `ChirpControlHost`,
     `ChirpControlLoop`, `ChirpControlCleanup` and `ChirpControlBatch` now generate
     the control stream from binary dimension words `s,t,m,w` and a preserved unary
     block count. Six checked arithmetic atoms per block compute its next advance;
     actual binary-to-unary conversion emits a delimited packet. The generator restores
     its complete bank, counter and scratch, with bound
     `M (6C+11W+14) + (4W+4)D + 6C+6`, where `C = tblC W e` and `D` is total
     symbol advance. `ChirpGatherSetup` composes generation, the sweep and control cleanup,
     changing only the window destination, at bound
     `M (6C+11W+14L+41) + (4W+18)D + 6C+16`, with `L = (3m+1)w`.
     `ChirpControlCheck` audits the complete imported namespace. `ChirpRotate`,
     `ChirpRepeat`, `ChirpRepeatPrefix`, `ChirpCyclicMath`, `ChirpCyclicCopy` and
     `ChirpCyclicExec` now build the exact cyclic extension from the raw coefficient
     line: rotate to offset `(s-m%s)%s`, repeat `C = (s+3m-1)/s+1` whole periods,
     copy exactly `N = (s+3m)w` symbols, discard overshoot, and rotate the source back.
     Only the extension destination changes. The bound is
     `C (8sw+9) + 10N + 10sw + 38`; overshoot is less than one source period,
     with no `m ≤ s` restriction. `ChirpCyclicCheck` audits this path.
     `ChirpCyclicArgs`, `ChirpUnaryCopies`, `ChirpCyclicCounters` and `ChirpCyclicSetup`
     now generate the forward/inverse rotation counts, repetition count, selected length
     and gathering-window length from the retained binary `s,m,w` words. Nineteen
     checked arithmetic atoms compute the counts; a structural conversion-list theorem
     executes binary-to-unary conversion, and six clearing atoms restore the full bank.
     Only the five counter destinations change, with exact count values and bound
     `25C + (4W+2)K + 55W+31`, where `C = tblC W e` and
     `K = sw + chirpPeriods s m + (s+3m)w + (3m+1)w`. `ChirpCyclicSetupCheck` audits it.
     `ChirpRawGatherData` and `ChirpRawGather` now compose counter setup, cyclic
     construction, gathering and erasure of the five counters and extension stream,
     retaining only the ordered windows. The shared role layout permits scratch reuse
     between phases. `ChirpBlockCount` and `ChirpBlockCountSetup` compute
     `M = (t-1)/m+1` from binary dimensions and restore the bank; `ChirpGatherFromDimensions`
     composes this with the raw-line gather and erases the generated block count.
     Its public contract requires the retained binary dimension bank and width templates,
     with no supplied geometry counters, extension or control schedule. All phase costs
     and cleanup are included in `chirpGatherFromDimensionsCost`; only the destination
     changes. `ChirpRawGatherCheck` audits the complete imported namespace.
     S2/S3 still need table reuse across lines,
     initial dimension/width-bank setup and operand/output arithmetic,
     followed by the complete forward-resampling contract and cost comparison.
   * **The ring arithmetic of b5** (`Mult/ChirpRing.lean`). Per block, the reversed halved
     computed inputs and the shifted halved kernel are one disk record pair of size `2^l ≥ 7m`
     (`norm_chirpRec_le`); coefficient `4m - 1 - b` of their convolution is the correlation
     (`chirpCorr_conv`), and the rescaled ring output at precision `q` is within `8·2^l/2^q` of
     it (`chirpRingCorr_err`). `chirpAR` is the output stage on it, within scaled error `4` of
     `Ã` (`chirpAR_approx`): the exact arithmetic the b5b line machine implements.
6. **Integration.** `Fast/ResampA*`, `Fast/ResampB*`, `Mult/Sizes`, `Cost/MatchResampA`,
   `Cost/MatchResampB`; the Gaussian conjunct of `exp_facts`
   (`ε + ε c₀/2 + (1/2 + δ) ≤ 1 - κ`, from `totResamp = d T √p α M(p)`) becomes
   `min(1 - ε - δ, r - δ)` with `α² ≍ p^r`, `ε + r < 1`, `ε > (1 - r)/2`. The `√p α` window of
   `Ã` is the bottleneck of `totResamp`; the banded `B̃₀` is overcharged by about `α²`.

## (c) The exposure margin

**Where it comes from.** `exp_facts`' conjunct `ε(1-τ) + τ ≤ 1 - κ`, i.e.
`κ ≤ (1 - ε)(1 - τ)`, pays `totDirectCRT = T p d (1 + ℓ^τ)` (`Cost/DirectScale.lean`) through
`d ℓ^τ = d^(1-τ) (dℓ)^τ ≤ 2 b^(ε(1-τ)+τ)` (`Cost/DirectGrowth.lean`). The charge is `d`
exposures of an `ℓ`-bit axis field at `ℓ^τ` each:

* the direct CRT routing with distant exposure (`Cost/CRTDirectFull`, `CRTDirectMachine`,
  `CRTControlTarget`);
* the `2(d - 1)` last-axis interchanges of `Ã` (`Cost/MatchResampA.lean`) and of the banded
  `B̃₀` (`Cost/MatchBandB.lean`, `mt_band_stage_le_linear`).

At `ε → 1` it tends to zero.

**What delivers the margin `a_b`.** The selected bulk tape transfer
(`notes/structured-bulk-assembly.tex` of the pinned CrocSwap revision, "Bulk locality and fixed
tapes") costs `O(Tp [p^τ polylog p + d polylog p + d p^δ + w² p^δ + d w² p^δ / L]) + n^(o(1))`.
Its exposure moves one short field at a time with temporary binary padding, so the movement
costs `p^τ polylog p` once for all axes. It needs:

* M7b's core/halo windows (item 4 above), which make every axis a short field;
* M5b's arbitrary-source coordinate routing (`Balanced/DESIGN.md`, cost `V p^τ polylog p`) for the
  field movement;
* the direct CRT routing, kept as it is.

The other terms are `d polylog p` (margin `1 - ε`) and `p^δ` terms (margins `1 - ε - δ` and
`r - δ`).

**Which margins bind near one.**

| margin | today, `ε = 31/64` | today's suppliers, `ε → 1` | selected suppliers |
| --- | --- | --- | --- |
| compact layer `ε(1 - λ')` | `1.18·10^-9` (binds) | `→ 2.44·10^-9` | `ε q`, binds (`g`) |
| chunk exchanges `ε c a_b` | `1.25·10^-9` | `≤ (1 - ε) a_b` without M5b; `a_b` with M5b | `a_b` |
| exposure | `(1 - ε) a_b = 1.53·10^-9` | `→ 0`; `a_b` with bulk exposure | `a_b` |
| Gaussian | `1/2 - δ - ε - εc₀/2 = 7.8·10^-3` | `min(1 - ε - δ, r - δ)` with M7 | same |
| prefix | `1 - ε = 0.52` (M5a) | `1 - ε` | `1 - ε(1 + c)` or `1 - ε` |
| scalar, dimension | `1 - ε - δ`, `ε` | same | same |

With today's suppliers the near-one route is worth about one bit: the layer margin goes from
`ε(1 - λ') = 2^-29.65` to `(1 - λ') ε` at `ε ≈ 0.99`, about `2^-28.6`, provided M7, the bulk
exposure, M5b and (a) are in place. Without M5b and bulk exposure the best compromise is
`ε ≈ a_b/(a_b + 1 - λ') ≈ 0.55`, worth about `0.2` bits. With the selected suppliers the
selected assembly has all seven margins at or above `g = εq`: about `1.25·10^-5` (`2^-16.3`)
in `notes/structured-bulk-assembly.tex`, and `a/(1 + a)` with the bootstrapped `a` of M8
(`2^-9.2`), against `ε c a ≈ 2^-10.4` on the present layout.

## (d) Staged estimates

Conservative, agent time, on the shared lock and the 24 GB machine.

| stage | content | lines | time |
| --- | --- | --- | --- |
| a1 | `Big` from the eventual bundle `BigFacts`; `d_le_b`, `b_pow_le_ℓ`, `mul_d_le_b` | 350 | done |
| a2 | consumers of `d ≤ ℓ`, `d ≤ 2ℓ`, `b ≤ 4ℓ²`, `F d² ≤ b` (the `Dist*` width lemmas now take `Big`) | 200 changed | done |
| a3 | Gaussian and small-gap widths from the width room | 60 | done |
| a4 | the `synE` exponent sum, linear in `D` | 40 | done |
| a5 | the chunk exponent as a parameter with `εc < 1 - ε` | 150–300 | 3–6 days |
| a6 | the machine dimension `iroot M (b^N)`, its root rooms, and the exponent arithmetic of the bundle for a general `ε = N/M` | 600–1200 | 2–3 weeks |
| b1 | rounded boundary factorization | 668 | done |
| b2 | boundary ordering | 457 | done |
| b3a | the concrete phase-cell solve and its `B̃₀` interface | 924 | done |
| b3s | the shared short-convolution layer on the ring product (also for b5): math and the b5 ring arithmetic done (150 + 176); the machine glue | 1–2k | 3–5 weeks |
| b3b | the phase-cell machines: the per-axis loader (masks, weights, generators, boundary matrix, factor tables) and the line machine | 6–10k | 3–5 months |
| b3c | the costs of b3b, matched into `rsbAllCostG` | 1–2k | 4–6 weeks |
| b4 | bulk core/halo execution and tape transfer (M7b) | 6–12k | 3–6 months |
| b5a | the chirped-correlation forward map for `Ã`: chirp identity, blocks, rounding errors | 588 | done |
| b5b | its machine on b3s, the exponential tables, specs and costs | 3–5k | 2–3 months |
| b6 | integration into `ResampA/B`, `MatchResampA/B`, the Gaussian conjunct | 2–4k | 1–2 months |
| c | bulk exposure on b4 and M5b (M5b: 9–15k, 3–5 months, `Balanced/DESIGN.md`) | 1–2k beyond b4 and M5b | 3–6 weeks |
| r | the retune to a near-one `ε` | 1–2k | 2–4 weeks |

a1–a4, b1, b2, b3a and b5a are done: no proof uses `d² ≤ b`. a5 and a6 belong to the retune. The
rest of (b) is about 20–37k lines and 11–19 months of agent time; (c) with M5b adds 10–17k lines
and 4–6 months. b5 alone, with the banded `B̃₀` at `α² ≍ p^r`, `r < 1 - ε`, keeps the Gaussian
margin `(1 + r)/2 - ε - δ` positive up to `ε < 2/3` (plan, the `2^-33` route); b3 is needed
above that.

The generated integer chirp operands now have a closed mathematical interface:
`ChirpOperands` identifies the weighted window with the real stream multiplier's
aligned `zipWith` output, reverses coefficient order, and proves exact decoded
agreement with `chirpRecIn` and `chirpRecK` at precision `q+1`.
`ChirpOperandBounds` derives integer disk bounds from the generated table estimates.
`chirpOperandBatch_err` discharges the representation, length and disk hypotheses of
the shared batch tape error theorem. This closes operand semantics. `chirpWeighted_exec` now executes multiplication
of the complete gathered window stream against the generated G-table stream in one
traversal, costing at most `M*(3m+1)*(rmulCost w+6w+2)+8` tape steps. Only the
weighted-row destination changes; the window/table streams, counter templates,
multiplier bank, native stacks and user state are restored. Its signed fit hypotheses
follow from unit-disk inputs and generated-table bounds with `q+3 ≤ w`.
`ChirpOperandStreams` also identifies the generated K-table with the complete S1
kernel operand tape. `chirpOperandX_exec` now executes row reversal into the exact raw X operand stream,
retaining batch order and all low-bit-first words, at cost
`M*(26*(3m+1)*w+19*(3m+1)+17)+8`. The structural `reverseRows_exec` theorem
restores the weighted source, batch/row/word counters, native stacks and all scratch,
including arbitrary source and destination tails. `chirpMakeX_exec` now composes
weighting, row reversal and weighted-stream erasure, retaining only the final X operand
destination change and charging all three stages. `chirpOperandCountSetup_exec`
separately computes and emits the batch, row and symbol counters from `t,m,w`, restoring
the entire binary bank. `chirpMakeXSetup_exec` now composes this setup with operand
production and counter erasure from initially blank geometry tapes. It proves the exact
X operand output, changes only its destination, and charges setup, multiplication,
reversal and all intermediate-stream/counter cleanup in `chirpMakeXSetupCost`.
The retained inputs still include the binary dimension bank, unary multiplier templates,
gathered window stream and generated G-table stream. Composing gathering, generation,
multiplication and the shared batch call remain required, along with output arithmetic,
cropping and the final cost contract.

`chirpGeneratedBatch_exec` specializes the actual shared S1 program to the produced
chirp X operands and the emitted shifted K-table stream. Operand lengths and integer
disk conditions are derived from the original input bound and generated table estimates.
`chirpGeneratedBatch_correct` attaches the decoded correlation error
`8*2^l/2^(q+1)` to the actual returned destination tape, with a full stack equation,
user-state restoration and the shared program's cost. This is a prepared-operand
execution contract: composing the operand/table producers and generating its unary
S1 dimension tapes remain open, as do output arithmetic, cropping and the final
forward precision/cost theorem.

`chirpInputBatch_exec` now joins `chirpMakeXSetup` to the actual shared S1 program
and erases the temporary X operand stream afterward. Only the correlation destination
changes. `ChirpBatchState` contains tape-data preconditions, with a structural frame
lemma under operand writes; `ChirpBatchLayout` contains only static register facts.
Neither assumes an execution oracle. `chirpInputBatchCost` charges input production,
the one shared batch call/extraction, and X erasure. The contract starts with gathered
windows, generated G/K table streams and unary S1 dimensions. Raw gathering and table
generation still need composition into this caller, and those unary dimensions still
need installation from the retained binary bank.

`chirpS1DimensionSetup_exec` now provides the missing unary-dimension installer as a
separate executable stage. A dedicated binary bank retains `q,t,m,w,l` in slots 0–4;
thirteen checked arithmetic instructions compute `p=q+1`, `3m+1`, `4m` and `ceil(t/m)`.
Seven conversions emit `p,l,w,3m+1,4m,M,m`, and five clearing instructions restore the
working words. `chirpS1Dimensions_at` identifies each installed dimension, while
`chirpS1Dimensions_cost` gives the exact conversion bound. Installation costs
`18*tblC W e + (4W+2)*sum(dimensions) + 77W+43`. Composing this installer and
its unary cleanup around `chirpInputBatch` remains open. The dedicated binary inputs
and multiplier templates still need initialization from the original caller inputs.

`chirpDimensionBatch_exec` now composes unary-dimension installation, shared S1 execution,
extraction and dimension erasure. Its inputs contain prepared X/K operand streams, the
retained binary `q,t,m,w,l` bank and blank dimension tapes. Only the correlation destination
changes. `ChirpBatchWorkspace.install` derives the caller's readiness from scratch
emptiness and exact installed counts, with no supplied unary-dimension assumptions.
`chirpDimensionBatchCost` charges setup, one shared batch call and all seven erasures.
Joining this path with X production and raw gathering/table generation remains open;
original-input bank/template installation and output arithmetic/cropping also remain open.

`chirpStreamCorrelation_exec` now joins X production (including generated geometry) with
S1-dimension installation, the one shared batch call/extraction, dimension cleanup and
X erasure. Only the correlation destination changes; all stages are charged by
`chirpStreamCorrelationCost`. The prepared inputs are gathered windows, generated G/K
streams, retained binary banks and multiplier templates. `ChirpBatchWorkspace.update_operand`
proves that producing X preserves the scratch preconditions of the installed-dimension
caller. Joining raw gathering/table generation, initializing banks/templates, and output
arithmetic/cropping remain open, along with the full forward precision/cost contract.

`chirpRawCorrelation_exec` now composes raw-line gathering with the stream correlation
caller and erases the gathered windows afterward. The raw line is retained; only the
correlation destination changes. All geometry counters, weighted/X/window streams,
S1 dimensions, private banks and scratch are restored. `chirpRawCorrelationCost`
charges gathering, operand production, installed-dimension shared S1 execution and
window erasure. Initial generated G/K table streams, binary banks and multiplier
templates remain supplied data. Table generation must still be composed, followed by
original-input bank/template initialization, output arithmetic/cropping and the full
forward correctness, precision and cost comparison.

`chirpTablePair_exec` now executes the G and K schedules consecutively on the same
restored table bank, with exact two-destination output and the sum of both schedule
costs. `ChirpTablePairFrame` proves the input/kernel outputs, spectator frame,
multiplier register-file frame and exact consumer stream shapes. This is the table
preparation stage for `chirpRawCorrelation`; composing it and erasing temporary table
streams still remain open. It retains supplied binary dimension/precision inputs,
not coefficient or pi oracles.

`chirpTableCorrelation_exec` now joins the paired table generator to raw-line gathering,
operand production, generated S1 dimensions, one shared correlation call/extraction,
and table erasure. Only the correlation destination changes. Its complete cost is
`chirpTableCorrelationCost`, including both table schedules and both table erasures.
No coefficient, pi, window, X operand or S1 unary dimension tapes are supplied.
The remaining prepared data are retained binary banks (including table block count)
and multiplier templates. Initial installation of those banks/templates and subsequent
output arithmetic/cropping still need execution, followed by the full forward
correctness, precision and cost comparison and reusable setup across lines.

The output arithmetic now has an exact integer model. `chirpOutputWord_chirpAR`
identifies postprocessing of each actual shared correlation tape word with `chirpAR`,
including every original output index in the final partial block. The q+1 ring numerator
is shifted by l+1 to recover the correlation at precision q; two real products and the
Γ shift follow, then signed truncation lowers precision to p. E is generated at q-Γ
and interpreted at q; normalization is `2^q/(2α)` in natural arithmetic, with error at
most one q-grid unit. `chirpComputed_approx` discharges all factor-error hypotheses of
the analytic forward theorem under its explicit window and precision gates.
This is an arithmetic/analytic bridge, not output tape execution. Executing shifts,
products, normalization/E setup, rounding and cropping, proving signed intermediate
widths, choosing precision to close the gates and the final execution/cost comparison
remain required.

`chirpScale_exec` now specializes the existing actual shift program to Gaussian streams:
the source is multiplied by `2^d`, all other tapes are restored, and the exact cost is
`N*(6w+4d+14)+4`. Its representation statement remains valid modulo the word width;
exact signed decoding additionally needs shifted numerators to fit. `ChirpOutputBounds`
proves decoded-norm-to-signed-fit conversion and a uniform final numerator bound
`8*2^(l+Γ)`, giving the envelope `q+l+Γ+5 ≤ w`. Computed normalization and normalized
E have absolute values at most 1 and 2. Output product/shift composition, final rounding,
cropping and remaining intermediate fit obligations still need execution proofs.

`chirpOutputETable_exec` now executes the first output shift and the normalized E product.
One E row is reused across every equal-length correlation block. The actual cost is
`N*(6w+4(l+1)+14)+4 + N*(rmulCost w+6w+8)+6`, where N is the total coefficient count.
The source becomes the scaled correlation stream; the destination gains exact truncated
E products; the E table, unary counts, multiplier bank and scratch are restored.
Both multiplier input fits follow from decoded correlation norm ≤1, factor magnitude ≤2
and `q+l+4 ≤ w`. Remaining output execution includes the Γ shift, normalization product,
final signed precision reduction and crop, plus their setup/cleanup and intermediate fits.

`chirpOutputNormalize_exec` now executes the Γ shift and normalization multiplication,
reusing one real normalization word across the entire stream. It retains the scaled
source and normalization word, emits exactly `chirpOutputNormalize` numerators and
restores counters and private scratch. Its cost is
`N*(6w+4Γ+14)+4 + N*(rmulCost w+6w+8)+6`. Shifted input fits follow from the uniform
`8*2^l` E-product bound and `q+l+Γ+5 ≤ w`; normalization-word fits follow from magnitude
≤1. `chirpOutputEBlocks_norm` proves that every emitted E product satisfies the required
bound, structurally over arbitrary rows. The composition/routing of E and normalization
stages, intermediate cleanup, final rounding/cropping and generated output setup remain open.

`chirpOutputProducts_exec` now connects the executed E stage directly to the executed
normalization stage through an identified intermediate tape. It produces exactly the
modeled `chirpOutputNumerator` stream and charges both shifts and both products.
The E and normalization tables, unary counts and private multiplier scratch are retained;
the correlation source and intermediate product source contain their shifted versions
as owned working data. The structural E-product norm lemma discharges the next stage's
input-bound precondition. Cleanup of those working streams, final precision reduction,
cropping, generated output setup and composition with the correlation caller remain open.


`chirpOutputFinish_exec` executes the final signed q-to-p precision reduction and
crops the padded final block in one composed program. `chirpRound_exec` reuses the
existing signed word pass over arbitrary lists; `chirpOutputRound_exec` derives
its input fit from the product norm bound. `chirpRounded_norm` and
`chirpRounded_fits` preserve the norm envelope and prove five guard bits suffice
for the reduced output. `chirpCrop_stream_exec` erases the padded suffix and
restores the retained prefix in order, including empty outputs. Both passes have
exact step counts and restore every register except the stream. This supersedes
the missing precision-reduction/cropping execution items above. Generation of the
finishing counters, connection to product execution, intermediate cleanup and the
complete original-input forward contract remain open.


`chirpOutputComplete_exec` now composes both shifts/products with the checked
rounding/cropping finish and erases both shifted intermediate streams. It changes
only the consumed correlation source and final output; `chirpOutputCompleteCost`
charges all phases. `chirpOutputNumerators_norm` supplies the finishing bound
structurally over arbitrary equal-length rows. `chirpOutputFinished_coeff` and
`chirpOutputFinished_value` read each retained word without signed aliasing.
This supersedes the missing product/finish composition and intermediate-erasure
items above; correlation-to-output composition is still required.

`chirpOutputFactorSetup_exec` generates the E row and normalization word from a
retained binary bank. It computes at q-Γ for E, restores q, computes 2^q/(2α)
with the existing doubling/division programs and restores all evaluator work.
`chirpOutputFactors_stream` identifies the generated E representation with the
real-table multiplier input; `chirpOutputFactors_bound` derives its factor bound.
`chirpOutputDimensionSetup_exec` computes and installs all nine shift/round/crop
counters from p,q,l,Γ,w,t, then restores its binary work. Both setup contracts
charge all arithmetic, output and restoration. `tblComputedUnaryCopies_exec`
shares the structural bank-restoration proof with the existing S1 setup, removing
its duplicated host proof. These supersede missing output-factor and counter
computation, but initial binary-bank installation, multiplier templates and the
full caller's setup/cleanup composition remain open. Precision/window choices,
reuse across lines and the final forward error/cost theorem also remain required.

The changed output/setup modules pass individual guarded checks (largest measured
peak 1921.0 MiB). `ChirpOutputCompleteCheck` audits composition, factor generation,
counter generation/restoration and final decoding against the standard three
axioms; it passes. The refactored existing `ChirpS1DimensionCheck` also passes its
guarded dependency build and axiom audit. This checkpoint is component validation,
not the complete S2 forward contract or a stronger multiplication bound.


The generated-data semantics and numerical gates are now closed structurally.
`chirpCorrelationRows` describes the exact shared-correlation rows, and
`chirpGeneratedCorrelationRows_norm` derives their unit-disk bound from the
computed operands. `chirpOutputNumerators_getElem` proves periodic E lookup in
flattened output order. The generic `chirpOutputTape_word` and specialized
`chirpForwardTape_value` identify each actual returned signed word with `chirpAR`.
`chirpForwardOutput_length` proves exactly t outputs after the final partial block.

`chirpForwardSelected_error` proves scaled error at most 4 for that exact integer
output representation under only s<t, α≥1, α²≤p and unit-disk input. Its explicit
choices are m=α(⌊√p⌋+1), Γ=32p, l=⌈log₂(7m)⌉ and q=p+2Γ+l+13.
`chirpForwardPrecision_gates` closes all three accumulated-error inequalities;
`chirpForwardGrowth_good` and `chirpForwardWindow_machineGate` close the growing
factor and integer evaluator gates. The working precision and signed input/output
widths are bounded by 83p, 125p and 43p respectively. The table word choice
13q+8 size(B)+16 satisfies both evaluator-precision envelopes; the caller still
needs a common B and all volume/address fits.

`tblChirpForwardWindow_do` executes the selected window from binary p and α:
its root-search loop stops at ⌊√p⌋+1 and multiplies by α, in at most
4(⌊√p⌋+1)+7 table atoms, with all intermediate fits derived. It supplies no
square-root or window-value input. These facts supersede the missing returned-tape
identification and mathematical precision/window choices above. They do not close
initial bank/template installation, complete caller composition, shared-setup reuse,
or the final actual cost comparison. S2 remains open until those machine obligations
and the full forward contract are verified.

The twelve new correlation/indexing/forward-sizing modules pass individual guarded
checks; the largest measured peak is 1921.6 MiB. The guarded
`ChirpForwardCheck` build and standard-axiom audit pass, covering the exact output
data, tape semantics, selected error theorem, table word sizes and root-search
execution. The active PLAN summary and whitespace checks also pass.


The output-side caller is now assembled from binary banks.
`chirpOutputGenerated_exec` installs all nine counters, executes the connected
arithmetic and clears the counters, charging every conversion and erased symbol.
`chirpOutputFromBanks_exec` also generates E and normalization, establishes both
multiplier interfaces, invokes that caller and erases both factor tapes. Its
exact final bank changes only the consumed correlation source and final output;
all generated factors, counters, shifted intermediate streams and scratch are
restored. The full bound is `chirpOutputFromBanksCost`, and the program text is
independent of numerical dimensions. Binary bank installation and multiplier
readiness are still caller preconditions.

`ChirpOutputLayout` packages wiring and the shared E-product intermediate.
`ChirpOutputState.install`, `ChirpOutputBase.installFactors` and
`ChirpOutputLayout.clearFactors` prove the interface and cleanup structurally in
arbitrary streams. `OutputPlacement.layout` and `layout_cross` give an explicit
146-tape arithmetic allocation; they do not yet allocate the complete caller's
additional table and correlation banks. `chirpOutputRun_exec` retains counters
and factors so a future line batch can scope their setup once. The from-banks
single-call wrapper currently generates and clears them for each invocation.
This supersedes output-side factor/counter composition gaps above. Raw-line
correlation integration, initial bank/readiness construction, full finite allocation,
shared setup across lines and the final cost comparison remain open.

The seven output-layout/caller modules pass individual guarded checks, with a
largest measured peak of 1953.7 MiB. `ChirpOutputCallerCheck` passes its guarded
build and standard-axiom audit, including the from-banks execution, full cleanup
and concrete register allocation. PLAN consistency and whitespace checks pass.

Caller bank initialization and release now have executed generic contracts.
`chirpBankLoad_exec` copies the two caller length counters and pads raw binary
words into all variable slots, preserving the sources. Repeated input sources
are allowed, so all zero variables can share one empty source. Its `_holds`
theorem establishes every evaluator role. `chirpBankClear_exec` clears the
owned words and headers with exact symbol cost; `chirpBankClear_load` proves
that loading then releasing a fresh bank restores the full register function.

`tblChirpMultiplierDimensions_do` computes topN(w) by doubling to the first
power strictly above 2w. `chirpMultiplierSetup_exec` installs w, q and topN(w)
while restoring its binary bank. `chirpOutputMultiplierSetup_exec` reuses that
bank for both output multipliers; its `_base` theorem establishes full readiness
from fresh arithmetic registers. `ChirpInitializationCheck` passes the guarded
build and standard-axiom audit for these initialization and release contracts.
The complete caller still needs selected-parameter installation, concrete bank
placement, correlation/output composition, shared setup and final total costs.

`tblChirpForwardParameters_do` now combines the principal scalar generation in
one 13-variable table program, from p and α alone. Its three stages reuse the
proved root search, compute l by doubling from 1 until the power covers 7m, and
compute Γ=32p, q=p+2Γ+l+13 and the two signed word widths with 36 fixed atoms.
No selected window, logarithm, growth, precision or word-width value is supplied.
All intermediate fits follow from 125p < 2^W, p≥1, α≥1 and α²≤p. The full
atom bound is 4(⌊√p⌋+1)+7 + (4l+9+36). The three modules pass guarded
checks at peaks 1833.0, 1953.2 and 1853.2 MiB. Consumer-bank installation,
all volume/address fits and complete caller composition still remain.

`chirpBankClone_exec` now executes consumer-bank installation from a computed
source bank, retaining both headers and all source variables, with an exact
copy cost and a complete spectator frame. `chirpForwardOutputBank_exec` composes
selected-parameter generation with installation of the entire fresh 14-variable
output-dimension bank. The source bank initially supplies p, α, zero and t;
the generated bank contains p,q,l,Γ,w,t followed by eight zero workspace words.
All generated parameter words now have proved fits in the selected-program postcondition.
The source bank is retained with the computed parameters, and every register
outside the two banks is preserved. Individual guarded checks pass at 1762.4 MiB
for cloning, 1881.6 MiB for the strengthened parameter program and 1834.4 MiB
for their output-bank composition. Initial loading of the source bank, the
remaining consumer banks, full allocation, correlation/output composition,
shared setup and the final cost bound remain open.

`tblChirpForwardCallerParameters_do` adds the binary block count `(t-1)/m+1`
to scalar selection, at five extra table atoms, reusing ring-search workspace.
Its postcondition retains p,α,s,t and zero and proves all sixteen words fit.
`chirpBankFamily_exec` structurally installs a list of disjoint consumer banks;
`chirpForwardConsumers` supplies the five forward assignments. The coefficient
bank receives q,s,t,α,M,m,Γ in slots 19,34,35,36,43,45,46, with all other
variables copied from zero. `chirpForwardConsumerSetup_exec` composes scalar
selection and family installation, retaining the source bank and all spectators
and charging the whole execution. The four added modules pass guarded file
checks below 1.9 GiB. `chirpBankEmissionSetup_exec` now replaces the source emission header by the
computed w before cloning any consumer bank; the composed setup charges both
clearing the old header and the linear binary-to-unary conversion. Its file
check passes at 1312.4 MiB and the strengthened consumer setup at 1821.3 MiB.
The family still requires concrete disjoint placement, initial source-bank
loading and initial length counters. Full correlation/output composition,
shared setup and the final forward cost contract remain open.

`ForwardBankPlacement` provides a concrete 193-tape allocation for the source
and all five consumer banks, with complete injection and separation proofs.
It is independent of dimensions and does not include the arithmetic/correlation
workspace. `chirpForwardSourceLoad_exec` now loads the complete fresh source
bank from raw p,α,s,t words and a shared empty source, in exactly
100W+8b+137 steps for b-bit inputs padded to W bits. It establishes both
headers, all variables, accumulator and scratch and preserves every register
outside the source bank. Its only separate length input is the W-length counter.
The two file checks pass at 1822.0 and 1776.8 MiB. Full setup composition,
raw-input/arithmetic/correlation placement, shared line setup and total caller
costs remain open.

`chirpForwardRawSetup_exec` now composes original-word loading and full consumer
setup in one execution theorem, retaining computed scalar semantics, all bank
contracts and the complete spectator frame. Its bound includes every loading,
selection, header-conversion and consumer-installation step. The initial W-length
counter remains a caller input. `chirpForwardCaller_fits` selects the common
base B=max(s,t+125p), reuses W=13q+8 size(B)+16, and discharges raw-word,
window/address/volume, output-crop, S1 and multiplier-size fit gates structurally.
A generic quadratic envelope proves these fits; table evaluator bounds already
use the same B and W. The two new checks pass at 1828.4 and 1870.1 MiB.
Complete correlation/arithmetic allocation and composition, setup reuse across
lines and the final actual total-cost comparison remain open.

`chirpForwardLine_exec` now executes the actual raw-line correlation program
followed by the output run and returns exactly the tape for `chirpForwardOutput`.
Generated correlation-row length and disk bounds discharge the output stage's
input interface. `ChirpOutputState.supplyInput` proves that supplying correlation
rows preserves the prepared multiplier/factor state; `ChirpOutputLayout.consumeInput`
proves the correlation input returns to its original empty state. The line changes
only its final output tape, retaining raw input, factors, counters and all scratch.
The cost is the sum of the actual correlation and output execution bounds.
The two modified/new file checks pass at 1910.7 and 1930.4 MiB. This theorem
retains the existing setup/layout preconditions: connecting the generated setup
to the line in a full concrete allocation, grouped iteration/setup reuse and
the final total-cost comparison remain open.

`LinePlacement` embeds the output, table and shared-product banks in a fixed
640-tape space, reusing their existing injection/layout proofs. A separate
30-role processor shares the multiplier bank with sequential output arithmetic.
Raw gathering and correlation extraction use separate private ranges; the
extraction destination is the output input. Proved interfaces include output
cross-separation, RpLayout, ChirpBatchLayout, raw injection/link, correlation
dimension injection, dimension/scratch/operand support separation, private-bank
separation and table/raw separation. The file check peaks at 1977.8 MiB.
Remaining producer/control layout facts and the full instantiated line/setup
execution are still required, together with shared-line iteration and total costs.

`LinePlacement.program` now names the actual fixed 640-tape line program.
`program_exec` supplies every static layout argument to the connected correlation/
output theorem. `selected_program_exec` also removes all caller-selected
numerical fit/window/E-factor conditions, deriving them from p,α,s,t with s<t,
α≥1 and α²≤p. Both contracts emit exactly the forward output tape and retain
setup while changing only the final output register. `ChirpLineControls`,
`ChirpFixedLine` and `ChirpSelectedFixedLine` pass file checks at 1928.1,
1948.7 and 1951.6 MiB. Prepared table streams, counters, binary banks and
multiplier readiness remain genuine data preconditions. Establishing them from
the raw setup around this fixed line, grouped iteration, final cleanup and total
cost comparison remain open.

`LinePlacement.readiness_exec` installs the operand producer's and both output
multipliers' counters from the same retained q,w bank, charging three setup
costs. Its `_ready` theorem derives the actual producer Ready and output-base
contracts from fresh data banks, and `_bank` proves every source-bank slot
restores. `tables_exec` generates G,K,E and normalization with one reused
coefficient evaluator bank; only the four table destinations change.
The padded table schedule exposed a missing bound in the former common base:
M*m can exceed t. The base is now max(s,t+125p), and
`chirpForwardCaller_tableBounds` proves M≤B, M*m≤B and 4m+1≤B, while the
existing fit theorem still passes. The three file checks peak at 1927.3,
1920.7 and 1869.6 MiB. Full generated-bank/readiness/table/counter composition
around the fixed line, grouped reuse, cleanup and total-cost comparison remain open.

`arithmeticSetup_exec` now executes the readiness and retained-table programs
as one stage, with both source banks retained and a complete phase cost.
`arithmeticSetup_prepared` derives the producer Ready, exact G/K streams and
complete output factor/readiness state from fresh data banks and a clean
multiplier bank. `tables_prepared` supplies the structural frame argument for
all four table writes, preserving the already installed interfaces. Generic
bank/processor and bank/output separation now centralizes those range proofs.
The readiness, composition and prepared-state checks peak at 1926.9, 1914.3
and 1919.3 MiB. Composing raw-bank setup, output counter installation and the
fixed line, then grouped reuse, cleanup and the total-cost comparison remain open.

`LinePlacement.prepare_exec` now executes readiness, all four retained tables
and all nine output counters as one stage, with a full phase cost and exact
final register state. `prepare_state` derives the producer Ready, G/K tapes,
output factor/readiness interface, nine counter lengths and empty output work
registers from fresh arithmetic/control banks. `counters_prepared` preserves
the arithmetic state while installing dimensions. Generic bank frames show
readiness/tables retain every binary bank and output control needed later.
The new counter and complete-preparation checks peak at 1935.5 and 1920.5 MiB.
Connecting the generated raw scalar/consumer-bank setup to these bank hypotheses,
then fixed-line execution, grouped reuse, final cleanup and cost comparison remain open.

`bankSetup_exec` now instantiates raw scalar/consumer-bank setup in the fixed
640-tape layout with concrete raw scalar and width-counter positions.
`consumer_state` derives all five bank schemas; coefficient-owned zeros and
variable fits follow from the computed source. `prepare_from_source` feeds
those schemas directly to complete arithmetic/counter preparation, deriving
all table/numeric conditions from selected sizing and source semantics.
Default proof limits are preserved through direct inequalities and source-fit
transport. The three new checks peak at 1952.7, 1919.7 and 1940.7 MiB.
`outside_banks` supplies the workspace spectator condition. Chaining raw setup
and preparation with fresh-state frames, then fixed-line execution, grouped
reuse, cleanup and the final total-cost comparison remain open.

`LinePlacement.initialization` now chains raw source/consumer-bank setup with
full readiness/table/counter preparation. `initialize_exec` constructs and
prepares everything from raw scalar words and the stated width counter, with
an explicit bound for all phases and a retained bank-stage/frame witness.
`initialized_prepared` transports the fresh initial arithmetic state through
that frame and derives the exact final producer Ready, G/K tapes, output state,
nine counter lengths and empty output scratch. The check peaks at 1933.1 MiB.
Raw/product workspace and input-data frames still need transport to fixed-line
execution, followed by grouped reuse, final cleanup and total-cost comparison.

`initializedLine_exec` is now the first complete initialized single-line
execution contract in the fixed 640-tape allocation: raw scalar words, raw line,
the stated W-length counter and fresh workspace feed initialization and the
selected fixed-line program. No prepared bank/table/readiness/layout/numerical
oracle remains. `readOutput` decodes the actual returned output tape, and the
execution theorem also proves scaled resampling error at most 4 for that decoded
result. The full initialization/correlation/output cost is charged. Setup remains
allocated for reuse, so grouped execution and final cleanup are still required.
`preparedStack_off` proves the exact 22-register write footprint and transports
all raw/product/producer/control frames, including private product cleanliness.
The source accumulator's empty-state fact is retained for subsequent bank cleanup.
The frame and initialized-line checks peak at 1978.8 and 1942.4 MiB. Grouped
reuse, complete setup cleanup/restoration and final actual cost comparison remain
open; the W-length counter remains a stated caller input.

`clearPrepared_exec` releases the 22 preparation tapes, charging twice their
symbol volume plus 45. `clearPrepared_lineResult` proves restoration of their
fresh original values while retaining output. `chirpBankFamilyClear_exec`
releases a structural family of disjoint banks; the fixed six-bank release costs
exactly 218W+12w+243 and makes every owned role empty. `release_exec` composes
both phases, and `release_lineResult_exec` accepts the initialized-line bank
witness directly. `releasedStack_readOutput` preserves actual output decoding.
Fresh support is derived from the original fresh arithmetic state and raw-bank
frame. The four release file checks peak at 1939.7, 1801.9, 1927.6 and 1924.2 MiB.
Composing the release into a complete restored caller, grouped reuse and the final
actual cost comparison remain open.

`closedLine_exec` now executes raw initialization, the selected line and full
release, restoring exactly the original state except the returned output tape.
The actual decoded output has scaled error at most 4, and every phase is charged.
The original bank-stage spectator frame is retained explicitly; restoration uses
bank ownership and the preparation footprint, with no register-space enumeration.
The restoration and closed-caller checks peak at 1922.3 and 1926.6 MiB.
The cost still exposes the bank-stage witness inside release symbol volume;
its selected-parameter reduction, grouped execution with one shared setup/release,
and the final actual cost comparison remain open. The stated width-counter
interface is unchanged.

`stageLine_exec` and `collectLine_exec` now implement one grouped line's input
staging/archiving and result collection. The round-trip register effect changes
only the batch cursor and input/output archives, preserving all retained setup.
`finishGroup_exec` restores the original input prefix and publishes output in
line order by reversing archives once. `lineSymbolsSetup_exec` installs the one
shared s*w counter from computed source words and restores its temporary zero
slot and complete source bank. The three new checks peak at 1923.4, 1920.5 and
1927.0 MiB. Retained readiness through staging and the repeated line loop still
need proof; the group must then scope one initialization/release and close costs.

`LineData.frame` now transports all retained tape requirements across changes to
the raw input and high group ports; `LineData.stage` instantiates it for staging.
`groupStep_exec` composes actual staging, selected forward execution and collection,
changing only the batch cursor and two archives. Its additional cost is
16 times input symbols plus twice output symbols plus 18. `groupStepR_low` and
`LineData.groupStep` retain the complete prepared interface for the next line.
The guarded checks peak at 1941.1 and 1930.3 MiB. The repeated counted loop and
one group-wide initialization/release, grouped error/restoration and final numerical
cost comparison remain open.

`groupLoop_exec` now executes an arbitrary list of bounded lines by structural
induction, retaining all shared data, archiving inputs/outputs and saving count
symbols. Its state recurrence is a generic stream lemma. `preparedGroup_exec`
restores the supplied count and original raw batch and publishes outputs in order,
with only `groupOutput` changed in the final state. The bound sums all line costs
and adds 5 per line, twice the input/output symbol volume, and 8. Both archives
and the saved-count tape restore to empty. Guarded checks peak at 1967.2 and
1934.9 MiB. One raw initialization/release around the prepared group, its decoded
error contract and the final numerical cost comparison remain open.

`initialized_lineData` now derives the retained interface from initialization;
the single-line caller shares this proof. `initializedGroup_exec` executes raw
initialization once, computes the shared s*w counter and executes every grouped
line. `groupRelease_exec` clears that counter and releases all preparation and
binary banks. The generic `releasedStack_eq_of_frame` restores arbitrary original
spectators when only owned setup differs. `closedGroup_exec` composes all phases:
its final state is exactly the original state with only the ordered output batch
prepended to `groupOutput`. All raw/scalar inputs, count, archives and private/
left/native stacks restore. Every phase is charged. The checks peak at 1924.6,
1930.9, 1947.0, 1929.6 and 1927.4 MiB respectively (including the single-line
refactor). The decoded grouped-error proof, release-volume and length reduction,
and final numerical cost comparison remain open. The width-counter interface
remains stated explicitly.

`readGroupLine_published` recovers each actual output row before any suffix;
`publishedGroup_error` gives scaled error at most 4 at every batch index.
`GroupOutputError` packages that exact property for the caller.
`groupInputBatch_length`, `groupOutputBatch_length`, `groupLineCost_sum` and
`groupRunCost_eq` reduce all data lengths and line-cost sums to scalar dimensions.
`LineData.clearPreparedCost` computes the exact retained release symbol volume:
2 times (3(w+q+topN w) + (M(7m+1)+m+1)w + 4w + t(p+l+Γ+5)), plus 45.
High group ports do not affect it. `closedGroup_exec` now combines raw-input
execution, exact restoration except the published batch, decoded error at most
4 for every line, and the scalar-only bound `selectedGroupCost s t α p N`.
The bank-stage witness no longer appears in the cost. The checks peak at
1927.2, 1919.6, 1949.8 and 1931.3 MiB. Final comparison of this cost with the
intended fast-resampling bound remains open; the W-length counter interface is
still stated. S2 is not marked complete by the explicit formula alone.

The conversion budget now uses the existing host theorem `toUnary_exec_linear`:
6*x+11*W+6 for the unchanged Horner program. This propagates through counter
lists, advance emission, block-count setup and every caller cost. The shared
symbol counter costs at most 2*tblC W w + 6*s*w + 11*W + 7. Control generation
charges 8*D rather than (4*W+4)*D; full gather setup charges 22*D rather than
(4*W+18)*D. `selectedGroupCost_affine` separates the exact shared zero-line
cost from N times `selectedGroupUnitCost`. No execution or layout changes.
The fixed advance schedule is still regenerated per line, charging
6*M*tblC W w in that per-line budget, although the gather sweep restores it.
Retaining the schedule across the group is the next cost-comparison task;
the current budget is not yet claimed to meet the intended fast bound.

`chirpGatherMode` and `chirpRawGatherWith_exec` share the sweep/cyclic/cleanup
proofs between generated and retained advance controls. The dimensions bridge,
correlation, fixed/selected forward line and `LineData` now carry that mode;
the actual counted/prepared group can retain count and schedule across lines.
`chirpGatherFromDimensionsModeCost_split` identifies the avoided per-line charge
as M*(6*tblC W e+11*W+24)+10*D+17*tblC W e+11*W+16, D=chirpCenter s t m M*w.
`controlsSetup_exec` executes generation from source slot 7 and the gather bank,
restores both banks, and changes only the retained count and schedule tapes.
Its guarded check peaks at 1940.5 MiB. The complete existing closed caller
still selects generated mode; the next integration must turn generated controls
into shared `LineData`, select the retained loop and clear those controls once.
Only then does the complete caller inherit the per-line saving.

The complete closed caller now uses retained controls. `LineData.transport`
separates arithmetic/producer reads from raw-control readiness, and
`LineData.shareControls` establishes shared readiness after actual generation.
`initializedGroup_exec` runs `controlsSetup` once before the retained-mode loop.
`controlsRelease_exec` and `controlsReleaseR_collect` erase the count/schedule
once, preserving output and restoring their original empty tapes; the cost is
2*(M+(D+M))+5, D=chirpCenter s t m M*w. `symbolGroupResult` feeds the existing
symbol/arithmetic/bank restoration proof after that erasure. `closedGroup_exec`
now composes the complete retained-control caller, still giving exact restoration,
decoded error at most 4 for every published line and a scalar-only execution bound.
`selectedGroupCost_affine` uses the retained unit cost, with control generation
and release paid only in the shared term. The initialized-group and closed-group
checks peak at 1958.9 and 1934.4 MiB. Final fast-cost matching remains open.

`ChirpFastCost` now bounds every retained line, including transfer/archive work,
by fixed scalar/header startup plus M*rpRecBound(q+1,l,w), six times
(s+t+m+1)*rmulCost(w), and 2000*(s+t+m+1)*(w+1). The power-of-two ring is at
most 14m and total padded block volume is at most t+m. Gathering, operand
formation and output finishing have checked linear-volume bounds; the product
estimate reuses S1's existing theorem. `selectedGroupCost_le_fast` discharges
selected gates and lifts the unit bound through shared setup/release amortization.
`closedGroup_exec` now includes that bound as well as the exact scalar bound,
execution, restoration and decoded error. Checks peak at 1988.1 and 1934.9 MiB.
The intended O(M(p)) comparison is still open: match the two supplier primitives
and fixed startup to the resampling envelope. `Cost.MatchConv.mt_cv_ring_le`,
`Cost.Growth.gr_ringBound_le` and `Cost.MatchBase.mt_rmul_le` already supply
relevant packed-product and pointwise estimates.


The supplier bridge now exists in `Cost/ChirpLogGrowth` and `Cost/ChirpSupplier`:
selected recurring ring work is at most C*m*p^(129/128), and complete repeated
line work is at most C*(s+t+m+1)*p^(129/128), plus explicit fixed startup.
The closed group's fast budget has the corresponding uniform bound with shared
setup once and fixed startup per line. Selected fixed startup is at most
`32000*(W+1)^2 + (7056*mtCvKf 125+264000)*p^2`; all headers and cleanup are
included. The supplier guarded check peaks at 2851.6 MiB. Address-width and
startup absorption and shared setup amortization remain open; this is not yet
the final O(M(p)) forward-resampling comparison.


`Cost/ChirpAddressCost` now absorbs the selected address width and all per-line
startup: the complete line budget is at most C*(p²+t)*p^(129/128), uniformly.
For p²≤t it is at most C*t*p^(129/128). The actual scalar group budget is bounded
by its zero-line shared setup plus N times the same uniform line envelope.
This covers headers, loading, address operations and cleanup; the guarded check
peaks at 2838.5 MiB and the expanded supplier axiom audit/build passes. Shared
setup still needs a uniform dimension bound and amortization; outer integration
must also establish the long-line regime before using its specialization.


`Cost/ChirpSetupCost` bounds all shared setup/release by
`6000000*(t+m+1)*(W+1)^3`. Its total-cost theorem holds for every group size,
with repeated work C*N*(p²+t)*p^(129/128). Its amortized theorem bounds the
actual scalar group budget by C*N*t*p^(129/128) under p²≤t and (W+1)³≤N.
No supplier-cost or setup-cost inequality is assumed. These dimensional gates
must still be audited against the intended caller before S2 is marked complete;
the conditional comparison does not itself prove an outer sizing theorem.


`Cost/ChirpForwardBudget` selects a single uniform constant and defines an
all-size `chirpGroupAllowance` with no primitive-cost assumptions. The actual
`closedGroup_exec` execution witness now satisfies that allowance and the
conditional C*N*t*p^(129/128) bound, alongside exact restoration and decoded
error. Its guarded check peaks at 2821.3 MiB; the expanded caller and supplier
axiom audits/build pass. The caller still accepts arbitrary group length, so
the size/count conditions are explicit rather than silently inferred. The
referenced source note is absent locally and could not be fetched; intended
outer sizing remains an acceptance-audit item, not a proved caller invariant.


S2 completion: `Cost/ChirpCallerSizing` now discharges the conditional cost gates
at the existing executable `Mult.Sizes`. Eventually every source/target axis
pair has p²≤t, and complete complementary batches have N≥(W+1)³, for every
mixture of source and target dimensions. The proof uses the existing radius
growth theorem, modulus bounds and a generic positive-product lower bound.
`chirp_runtime_group_cost` therefore bounds the actual scalar group budget by
C*N*t*p^(129/128), and `closedGroup_exec` gives that same bound on the actual
execution witness when its now-proved gates are supplied. Its all-size allowance,
actual decoded error ≤4 and exact restoration except ordered output are also
proved. The explicit bootstrap width/count counter ABI remains unchanged.
The final guarded sizing check peaks at 2832.9 MiB, and the guarded machine and
supplier audit build completes 13925 jobs at 3.4 GiB combined peak. S2 is complete
as a standalone primitive; full tensor/support-local scheduling, future sizing
retunes and global machine integration remain S4/S6 and do not change kappa here.
