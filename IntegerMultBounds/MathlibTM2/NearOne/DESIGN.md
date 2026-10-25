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

## Shared S3–S5 interface (pinned 2026-10-24)

This is the implementation contract for the inverse work packages. S3/S4/S5
remain open. It supersedes the older whole-axis loader/resume instructions below;
`rsbAllG` and `pcSolve` are reference implementations, not required execution
schedules. S2 remains the completed forward primitive.

### Ownership and endpoints

| Owner | Produces | Consumer and required proof |
| --- | --- | --- |
| S4 with R4 | Ordered core/halo descriptors, private gathered line batches, replica counts and a publication schedule avoiding reserved coordinates | S3 receives local buffers with global coordinate metadata; S4 proves exposure/publication execution, support and exact restoration |
| S3 | Interior cell setup and two interior passes, residual/recovery coupling, complex assembly, scaling and final rounding | S4 receives core results with a uniform error bound, an execution theorem, restoration and a paid scalar cost |
| S5 | Boundary setup, prepared factor/solver pages and repeated boundary solves | S3 receives an error bound for the stated computed Schur system, RHS/magnitude bounds, executed setup/solve/release and storage/cost bounds |
| S4 | Locality comparison and tensor composition | Converts local core accuracy to the global inverse endpoint without a factor for the number of windows or tensor entries |

The numerical vocabulary is checked in
[`Mult/PhaseCellInterface.lean`](../Mult/PhaseCellInterface.lean).
`Window.core` and `Window.halo` retain the ambient coordinate type, with
`core_subset_halo`. `SolveSpec A active core rhsBound solve error` means that,
for every solution of the principal system on `active` and every admitted RHS,
the returned values approximate that solution on `core`. For the inverse,
`A = PhaseCellMatrix.realMatrix s t p u` in the original `ZMod s` coordinates.
The top-level real RHS bound is 1/2. Recovery and boundary calls carry their
proved, generally larger bounds explicitly.

`SolveSpec.with_locality` composes a halo solver with an explicit comparison
between a halo solution and a global solution of the same ambient matrix.
The resulting core error is arithmetic error plus locality error;
`SolveSpec.of_windows` then assembles global core contracts over a cover.

S3's full endpoint is `SolveSpec A univ univ (1/2) X e`.
`SolveSpec.full_error` supplies precisely the `hX` consumed by
`FastB0.concrete_resampB₀_specX`; that existing theorem owns complex pairing,
`2^-j` scaling, final p-grid rounding, the diagonal approximation and the
normalized `B₀ J / 2^j` error/unit-ball guarantees. Its numerical hypotheses,
including `hsmall`, must be proved by the caller. They are not discarded by this
interface. `PhaseCellReferenceSpec.pcSolve_spec` anchors the full endpoint to the
existing checked reference solve.

### Geometry, cuts and boundary order

A descriptor contains ambient s,t, semantic p,u, ordered global halo coordinates,
owned core coordinates and the original phase/period cuts intersecting the halo.
An artificial halo endpoint is also a cut. A halo is a principal subsystem of the
same global matrix: do not replace s by the halo length, restart the phase at
zero, or introduce periodic wrap at the halo edge. Payload order and global
coordinate maps must be inverse on their advertised ranges. Publication writes
owned cores only; gathered halos and the reserved/untouched suffix are borrowed.

For each descriptor, S3 generates the actual interior set I from cells and cuts;
S5's boundary set is B = halo \ I. Cell intervals are nonwrapping, lie within the
halo, stay in one original phase cell, and cover the selected interior exactly.
Clipped cells and empty interiors/boundaries are admitted and handled explicitly.
S3 must prove these facts for generated descriptors, not request arbitrary masks,
selectors or interval covers as free inputs to its closed caller.

The boundary page records an explicit elimination order with no duplicates and
exact underlying set B, plus the coordinate/rank maps. The canonical full-line
reference is `bFoldOrder s B`; its proved half-bandwidth is `8*w+1` for the
reference phase-cell boundary. Local cuts change the interior/boundary problem:
S5 must prove its local support/fill and derived bandwidth or block sparsity.
Neither the full-line band theorem nor `boundary_card ≤ 2*w*(t-s+1)` is a local
window theorem. Any local bound must also account for artificial cuts.

Keep d (tensor dimension), g = t-s (axis gap), w (matrix half-bandwidth),
b = |B| (boundary rows), q (arithmetic precision), W (address/counter width) and
N (replica count) distinct. In particular the factor `w²/d` requires a proved
gap/density estimate; it is not obtained by treating boundary rank as d.

### Numerical handoff and precision

S3 proves stage errors for the operations on their computed inputs. In particular
its four triangular Toeplitz products per interior pass must establish the
corresponding clauses of `PhaseCellMatrix.CellRun.Valid`. The S1 short-convolution
error must be rescaled back to the actual generator/input magnitudes before it
can be charged as the stage tolerance. S1 does not assert exact equality with a
uniform scalar rounding function, so exact equality with `pcSolve rd` is not a
backend acceptance requirement. The other interior, coupling and boundary error
clauses are combined through the existing generic `SchurBlockError` lemmas.

S5 approximates the Schur operator computed from these interior responses; it
accounts for coefficient generation, interior-response error, rounded products,
pivots/reciprocals and solve error. It cannot assume an exact Schur matrix or
factor table supplied from outside the machine. Setup proves coefficient/word
fits and RHS/pivot bounds; each repeated solve preserves that prepared page.
The second S3 interior pass uses its proved recovery magnitude bound, not the
initial RHS bound 1/2.

The semantic rounded matrix (including its selected coefficient precision),
arithmetic precision q, storage widths, reciprocal iteration count and output
shift j are separate parameters. S5 owns a proved precision/iteration selection
from the error allocation, active sizes and magnitude bounds; S3 generates the
associated counters/headers and proves fits. Global address bits are priced
separately through W. The existing full-line estimate
`2^(8p+46)*p^7*s^2*η` is a reference bound; substituting halo cardinality for s
requires a new localized proof. No such substitution is assumed here.

S4 owns the separate locality bound between the exact halo solve and the exact
global target on the core. `ErrorOn.trans` adds arithmetic and locality errors;
`ErrorOn.crop` restricts to the core. `norm_error_of_publish` proves that selecting
one owned output per coordinate preserves the uniform error bound independently
of the number of windows. `SolveSpec.of_windows` requires comparison to the same
global system; a halo-only solve contract cannot silently satisfy that premise.
The previously listed core/halo/Neumann constants are candidate sizing choices,
not locality certificates. S4 must prove the chosen sizes, coverage and error
allocation before S6 uses them.

### Machine ABI, reuse and cost ledger

The logical ports are immutable descriptor/scalar inputs, borrowed raw line batch
and count/width headers, retained interior setup, retained S5 boundary page,
private scratch, and an output stream with an arbitrary existing suffix. Each
kernel has a dimension-independent finite register placement; concrete offsets
are fixed when its machine is built. Only the advertised output prefix changes.
All input buffers, descriptors, setup pages, headers, left/native stacks and
spectators restore after a repeated line/group call. Setup and release have their
own executed contracts and explicit footprints. There is no supplied arithmetic
execution oracle, free coefficient page or unpriced zeroing of borrowed fields.

A reuse key includes ambient s,t,p,u, global halo/cut metadata, arithmetic and word
widths, rounding/reciprocal parameters and the boundary order/backend format.
Only replicas with the same key share a page. Equal halo lengths alone do not
justify coefficient/factor reuse. Transport between keys needs a proved semantic
identity and an executed, priced conversion.

The ledger is

`sum_keys (setupCost + releaseCost) +
 sum_groups (externalTransferCost + N*kernelLineCost + publicationCost)`.

`kernelLineCost` includes both real solves, all S1 batches and their headers,
interior weighting, two couplings, S5 repeated solves, local transfers, scaling,
rounding and crop. S5 work is charged inside that term once. S4/R4 owns external
exposure/publication and global layout restoration. Shared setup includes all
coefficient, mask, descriptor, reciprocal and boundary/factor generation and final
erasure for each distinct key. Actual setup multiplicity and batch counts must be
proved; S2's whole-axis amortization does not automatically pay halo-specific keys.

Before using `O(t*M(p)*(1+w²/d))`, expose the actual interior volume, coupling
nonzero count, boundary row count and boundary bandwidth/block-work count.
Repeated boundary work must be priced in those quantities. A band factorization's
setup cost and storage must be charged separately; reusing `Fast/BandLine` alone
does not establish S5's new-regime cost. Match q,W and all supplier primitives to
the final envelope only after precision and fits are proved. Record simultaneous
retained pages plus live input/output and scratch storage; separate per-routine
peaks do not establish the combined stock bound needed by M4/S6.

The module dependency order is shared interface/S1 → S3 interior kernel → S5
prepared boundary → S3 composed line → S4 schedule. S5 setup may call the
interior kernel to compute boundary-column responses and must charge those calls;
it must not depend on the composed S3 line. This keeps the construction acyclic
while allowing the same interior code to serve setup and both line passes.

S3 implementation checkpoint (2026-10-25): `Mult/ToeplitzShortConv` supplies
both convolution/index identities and decoded lower/upper stage errors on the
actual S1 result tape. The scaling factor 2^l remains explicit. The upper theorem
assumes reversed rows in S1's input bank; it does not pretend reversal is free.
`PhaseCellToeplitz.lower_batch_exec` in `PhaseCellLowerBatch` ties the lower error
to an actual fixed S1 run and its exact bank restoration/time budget. Normalized
raw operands and unary dimensions are still supplied. Checks peak at 1807.7 and
1796.8 MiB. Generated normalization, executed upper reversal/crop, weights and
generators, the four-product cell composition and `CellRun.Valid` remain next.
The guarded interface/Toeplitz axiom audit build completes 4065 jobs at 2.4 GiB
combined peak. S1's existing `coeff_diskGrid` already proves normalized returned
coefficients remain admissible operands for the next product; reuse that fact
when composing stages instead of duplicating coefficient range proofs.

Upper-stage execution checkpoint (2026-10-25): `PhaseCellReverseRows` replaces
an exact private row stream in place and restores scratch and counters, preserving
word bits and row order. `PhaseCellReverseSetup` generates and erases L*w; its
cost is C = M*(32Lw+19L+17)+6Lw+9L+20. `PhaseCellUpperInput` places this operation
in S1's ten empty private host slots, all blank again before convolution.
`PhaseCellToeplitz.upper_batch_exec` in `PhaseCellUpperBatch` executes both
reversals around S1 from ordinary raw rows; its exact frame restores the original
input and dimensions, changes only the output prefix, and bounds time by
`Fixed.cost + 2*C`. The returned tape has the proved upper-stage error. Its padded
ring rows still need executed selection/compaction before the next lower product.
The expanded axiom audit build passes (3999 jobs, combined peak 2.5 GiB); setup,
fixed-input and upper-batch checks peak at 1827.3/1806.7/1803.0 MiB. Full cell,
boundary and line composition and their generated setup/cost gates stay open.

Compaction checkpoint (2026-10-25): the same extraction loop/program now has
arbitrary offset/count proofs, with chirp retained as the a=3m specialization and
all prior costs unchanged. `ShortConvSliceDecode` decodes selected rows at their
compact stride and carries the disk bound to the next product. The upper-stage
coefficient error is shared by the padded and compacted stream proofs.
`PhaseCellToeplitz.upper_crop_exec` in `PhaseCellUpperCrop` produces upper-output-ordered rows, preserving
the padded source and all borrowed suffixes. `PhaseCellUpperCropSetup` generates
2^l*w, runs the crop and clears that counter; its complete bound is
`M*(20Lw+19L+6*2^l*w+23)+4w+6*2^l*w+9l+22`. Its check peaks at 1842.0 MiB.
Compaction now executes; staging between successive S1 calls must still retain
original inputs under a proved storage/frame contract. The structural S1 packer, coefficient packer, shared-product caller and unary
setup caller now preserve arbitrary raw operand suffixes with unchanged costs.
Their original exact-stream theorems specialize the same proofs at empty suffixes.
The fixed-bank `exec_with_tails` and S3 `lower_batch_with_tails_exec` now
expose this contract with unchanged costs and exact suffix restoration. Generated coefficients/normalization,
cell, boundary and line composition and final precision/cost gates remain open.
The expanded S3 and both S2 regression axiom audits pass in a guarded build
(13936 jobs, combined peak 10.6 GiB, 2.5 minutes). Eight changed/new source and
audit files pass guarded checks; the largest single-file peak is 1935.0 MiB,
with default proof limits and only the three approved axioms.

Suffix-preservation verification (2026-10-25): the expanded S3 audit and both
S2 regression audits pass in a guarded build (13936 jobs, combined peak
10.6 GiB, 2.7 minutes). Guarded single-file checks pass for the structural
packer (1889.5 MiB), product caller (1851.5 MiB) and unary caller
(1835.4 MiB). No program definitions, old theorem contracts or costs changed.

Fixed-bank staging checkpoint (2026-10-25): `inputBankWithTails` and
`startWithTails` retain arbitrary suffixes beneath both counted raw operands.
`Fixed.exec_with_tails` proves the same finite program and cost, and the old
`Fixed.exec` is its empty-suffix specialization. The lower-stage wrapper shares
this proof. `PhaseCellUpperOperand` identifies each compacted upper row and
proves its length and normalized disk bound for the next S1 call. Guarded
checks peak at 1857.3 MiB (fixed bank), 1797.8 MiB (lower wrapper) and
1792.5 MiB (upper operands). The expanded S3 and both S2 regression audits
pass in a guarded build (13937 jobs, combined peak 10.6 GiB, 2.2 minutes).
The actual staging, generator switching and temporary-stream release between
products still require executed composition; S3 remains incomplete.

Executed triangular-pair checkpoint (2026-10-25): `PhaseCellStageFrame`
identifies compaction's exact bank as the next lower call's input.
`PhaseCellStageInput.upperToLowerInput_exec` executes generated-count compaction
onto the right-operand tape, preserving its original rows below the new prefix.
`PhaseCellTriangularPair.triangularPair_exec` composes the upper product, staging
and lower product on 117 tapes, with the sum of their actual costs and decoded
lower error against the computed normalized upper rows. Its guarded check peaks
at 1806.3 MiB. The expanded axiom audit passes (4009 guarded build jobs,
combined peak 2.4 GiB). Temporary compact/padded upper rows remain explicit in
the postcondition: crop/publication of the lower result and paid prefix release
are still required before the second branch and four-product cell composition.
Generated weights/generators, precision, boundary/coupling/recovery, full line
composition and final S3 costs remain open; kappa is unchanged.

Paid intermediate release checkpoint (2026-10-25): `PhaseCellPrefixRelease`
proves prefix removal with an exact arbitrary suffix and original-symbol
counts. `releaseRows_exec` generates and releases both product counters from
retained batch/row/width dimensions; its bound is
`12*symbols + 9*M + 6*L*w + 9*L + 18`.
`PhaseCellInputRelease.releaseUpperInput_exec` removes only the compacted
upper-row prefix, restores the original right operand and leaves the output
untouched. `PhaseCellTriangularPairRestore.triangularPairRestored_exec` now
executes both triangular products, generated staging and this release, returning
the canonical bank with both original raw operands and decoded lower-product
error. The two padded product streams remain explicitly on the output tape.
Lower-result crop/publication and paid release of those output prefixes are
still required before repeated branches. The expanded axiom audit passes
(4012 guarded build jobs, combined peak 2.5 GiB); the row-release and fixed-input
release checks peak at 1827.1 and 1800.2 MiB. This does not complete S3: generated
cell arithmetic, both branches, boundary/coupling/recovery, precision and uniform
line costs remain open.

Lower-output components checkpoint (2026-10-25): `PhaseCellLowerCrop`
reuses the shared generated-count selector on lower-product streams. Its
`lowerRows_error` reads compact row position `L-1-i` and proves the lower error
with stride L; no free row reversal is assumed. The execution theorem preserves
source/destination suffixes and restores generated counts and work ports.
`PhaseCellRingRelease.releaseRingBatch_exec` generates both ring-symbol and
batch-total counts from exponent/width/batch headers, erases one padded batch,
releases both counts and preserves the exact borrowed suffix. Its bound is
`12*symbols + 9*M + 4*w + 6*2^l*w + 9*l + 26`. Guarded checks peak at
1807.6 MiB (lower crop) and 1821.5 MiB (ring release). The expanded S3
axiom audit passes in 4014 guarded build jobs (combined peak 4.0 GiB).
These components still
need composition with the triangular pair: crop into private workspace, remove
both padded result batches, then move the compact stream back to the persistent
output tail while clearing workspace. Both branches and the full cell/line
precision, setup and cost obligations remain open.

Compact triangular-pair endpoint (2026-10-25):
`PhaseCellResultPublish.publishPairResult_exec` releases both padded batches,
then transfers compact symbols in order through fresh workspace.
`PhaseCellPairFinish.finishTriangularPair_exec` composes lower extraction and
publication on the fixed bank. `compactTriangularPair_exec` now executes the
whole upper/staging/lower/release/extraction/publication chain from ordinary raw
operands on 117 tapes. Exactly one compact result prefixes the original output;
original operands, dimensions, native stacks and every work port are restored.
`compactPairCost` charges every constituent operation. Decoded lower error is
proved against the actual normalized upper numerators at reversed compact row
position `L-1-i`; there is no free rescaling or orientation change. The publication
and complete-pair checks peak at 1838.0 and 1829.6 MiB. The expanded S3
axiom audit passes (4016 guarded build jobs, combined peak 2.5 GiB).
Next: connect the two stages' explicit scales and errors to `CellRun.Valid`,
batch both generator branches, execute their merge/scalar arithmetic and generate
weights/generators. Boundary/coupling/recovery, full-line precision and uniform
S3 cost gates remain open. This endpoint does not mark S3 complete.

Triangular-stage scale checkpoint (2026-10-25): `PhaseCellPairScale`
connects compact upper operands and the actual published lower words to explicit
scaled stage errors. Bilinearity gives upper factor `a*b` and lower factor
`a*(a*b*2^l)`. Real projection loses no precision when raw generator words are
real; computed FFT intermediate rows may retain arbitrary imaginary rounding
noise. The real-stage error lemmas match the upper/lower arithmetic obligations
of `CellRun.Valid` on computed inputs. At generator scale 2 and input scale V≥0,
the proved tolerances are `4*V*2^l/2^q` and `8*V*(2^l)^2/2^q`. These are explicit
interpretations of stored numerators, not free tape rescaling or scalar arithmetic.
The guarded module check peaks at 1819.6 MiB. The expanded axiom audit
passes (4017 guarded build jobs, combined peak 2.5 GiB). Both generator branches, executed
merge/weight/reciprocal arithmetic and generated setup still need composition;
boundary/coupling/recovery, full-line precision and uniform costs remain open.

Both generator branches checkpoint (2026-10-25): `PhaseCellTwoBranches`
proves that concatenated generator/input banks produce the two compact branch
streams in order. `twoBranches_exec` runs all four triangular products through
the shared compact-pair program at batch size `M+M`, with one fixed-cost charge
per S1 call and exact raw-bank restoration. `PhaseCellDuplicateStream` and
`PhaseCellBranchInput.twoBranchesFromSingleInput_exec` execute the repeated
right-hand-side producer from one raw V stream, charging `6*M*L*w+6`; copy
workspace returns empty. The resulting repeated input remains installed in the
prepared bank, so its eventual release is still a caller obligation. Combined
generator construction and the doubled batch header remain explicit setup
inputs. Guarded checks peak at 1809.1 MiB (branch execution), 1799.2 MiB
(duplication) and 1809.8 MiB (single-input composition). Next: execute branch
merge and scalar arithmetic, generate coefficients/weights/headers, release
prepared input, and establish the full `CellRun.Valid` and line/cost endpoints.
The expanded S3 axiom audit passes (4020 guarded build jobs, combined peak
2.5 GiB). S3 remains active; boundary/coupling/recovery and uniform precision
are open.

Merge-word checkpoint (2026-10-25): the existing line-solver subtraction
automaton now lives in the small shared `Fast/SubWord` module. Its generic
`subWord_exec` proves exact full-stack framing and time `5*w+6` without a
multiplier-cleanliness hypothesis. `ResampBCore.rsb_subWord_runs` specializes
that proof, preserving its old contract and program; the duplicate automaton
execution proof was removed. `PhaseCellMergeWord.mergeWord_exec` proves that
one guard bit makes the actual reversed result word decode to the exact signed
difference. `value_sub` proves exact fixed-point subtraction. Guarded checks
peak at 1794.7 MiB (shared word) and 1885.2 MiB (merge word). This is the
arithmetic primitive for branch merge, not yet the stream loop or scalar
product. Those executions, generated cell setup and the full cell/line/cost
contracts remain open.

Merge-stream checkpoint (2026-10-25): `PhaseCellMergeStream.mergeStream_exec`
uses the existing Gaussian word-stream executor with the shared subtraction map.
No second per-word loop or subtraction implementation was introduced. Two
equal-length coefficient streams are consumed; the reversed exact-difference
stream prefixes the accumulator, and all other stacks (including width/tmp)
are restored. The bound is `n*(5*w+6)+2`, including empty streams, with w≥1.
The word guard-bit theorem supplies exact signed decoding; range hypotheses
remain separate from modular execution. Its guarded check peaks at 1895.4 MiB.
The expanded S3 audit passes (4288 jobs, combined peak 2.6 GiB), and the
refactored resampling core passes its guarded check at 1984.1 MiB.
The shared-word refactor passes regression builds for the old resampling line,
band factorization, S2 forward/supplier and S3 audits (13960 jobs, combined peak
4.4 GiB). Next: split the two published branch blocks into merge inputs with
generated counts, execute merge/publication and scalar multiplication, then
compose generated cell setup and the full numerical/line/cost endpoint.

Routed branch-merge checkpoint (2026-10-25): `PhaseCellTakePrefix`
consumes a counted prefix in original symbol order, preserving the suffix and
restoring workspace. `PhaseCellMergePublish.mergePair_exec` routes adjacent
branch blocks to the existing subtraction stream executor, then publishes the
difference in original word order above the exact output suffix. All temporary
stacks are cleared. `PhaseCellMergeSetup.mergeFromWords_exec` generates and
clears the total-symbol counter from word-count/width headers and charges the
whole chain by `n*(25*w+15)+22`. The word-count header remains explicit;
generating the per-branch count from cell descriptors is still setup work.
Guarded checks peak at 1805.5 MiB (prefix routing), 1922.7 MiB (routed merge)
and 1903.8 MiB (generated-count wrapper). The expanded S3 axiom audit
passes (4291 guarded build jobs, combined peak 2.6 GiB). Next: instantiate these stream contracts
on the two published branch lists, execute the reciprocal/scalar product, and
compose generated cell setup, `CellRun.Valid`, full-line correctness and costs.
S3 remains active; the entire inverse is not yet executed.

Executed four-product merge endpoint (2026-10-25): `PhaseCellHalfCount`
recovers M from the retained 2M header, preserving its actual symbols in
`6*M+4` steps. `PhaseCellBranchWords` generates ML and releases the half header.
`PhaseCellFixedMerge.fixedBranchMerge_exec` now generates every merge header
from 2M, L and w on the 117-tape bank, merges both adjacent result blocks, and
clears every header and work port; its bound is `ML*(25*w+21)+17*M+34`.
`PhaseCellMergedBranches.mergedBranches_exec` composes the one-input producer,
all four triangular products and the fixed-bank merge. Exactly one compact
branch-difference stream prefixes the original output, with the repeated-input
bank explicitly retained. `PhaseCellMergeRange.branchDifference_word` proves
that w≥q+3 recovers the exact signed difference from the actual output words;
there is no modular aliasing or extra rounding at merge. The two branch
numerators inherit the normalized disk bound from S1. Guarded checks peak at
1809.5/1813.5/1914.4/1894.2/1897.5 MiB for half-count, branch-count, fixed
merge, composed execution and range/decode modules. Next: execute reciprocal/
scalar arithmetic, generate coefficients, weights and headers, release the
prepared input and establish the complete `CellRun.Valid`, boundary/recovery,
line and uniform cost contracts. The expanded S3 axiom audit passes
(4296 guarded build jobs, combined peak 2.6 GiB). S3 is still active.

Shared scalar-kernel checkpoint (2026-10-25):
`PhaseCellScalarStream.realScalarStream_exec` reuses the real fixed-point table
multiplier with a one-word table for all merged coefficients. It restores the
operand/scalar streams and all other stacks, prefixes the actual product words
to the output, and charges `n*(rmulCost(w)+6*w+8)+6`. Its multiplier counters
and stored real scalar remain explicit inputs; setup and fixed-bank routing
have not yet been composed. `PhaseCellScalarRange` proves that actual compact
branch numerators have norm ≤1 and their merged difference norm ≤2. For a
stored scalar of norm ≤2, w≥q+4 proves product-word fit and signed decoding
with truncation error ≤`2/2^q` on the actual branch stream, without an output-fit
oracle. Guarded checks peak at 1889.6 MiB (kernel/bounds) and 1898.8 MiB
(branch range/error). Next: generate scalar readiness and the reciprocal word,
route and release the merged input around this call, execute output scaling/
weights and establish the full `CellRun.Valid`, boundary/recovery, line and
uniform cost contracts. The expanded S3 axiom audit passes (4298 guarded
build jobs, combined peak 2.6 GiB). S3 remains active.

Scalar-bank preparation checkpoint (2026-10-25):
`PhaseCellScalarPlacement` allocates the thirty scalar roles and 64 multiplier
tapes on the existing 117-tape bank. It proves injectivity, disjointness,
freshness after merged-branch execution and preservation of all retained
operands/dimensions/output ports. The exact three-counter readiness bank is
specified and proved sufficient. `PhaseCellScalarUnary.unarySetup_exec`
executes the binary q/w producer from unary ports 100/94, preserving both
source headers and all spectators; its cost is
`(q+w)*(4*w+10)+12*w+20`. No binary dimension words are supplied. The selected
w≥q+4, q≥1 guarantees q,w and the doubling program's temporary values fit
in binary width w. The unchanged thirty-role encoding was separated into
`ChirpOutputRoleCode` so scalar proofs do not import S2's entire output backend.
Next: compose binary-bank loading, the existing topN counter generator and
setup cleanup, then install the generated reciprocal word and route/release
scalar data around the actual multiply. Full cell/line correctness and uniform
costs remain open; S3 is active. Guarded checks for the final allocation and
unary producer peak at 1890.1 and 1899.8 MiB. The expanded S3 and both S2
regression audits pass (13967 jobs, combined peak 7.7 GiB, 1.2 minutes).

Generated scalar readiness checkpoint (2026-10-25):
`PhaseCellScalarBank.loadBank_exec` composes unary dimension conversion and
complete five-variable binary-bank loading. `PhaseCellScalarCounters` runs
the existing multiplier-dimension program and installs w, q and topN(w).
`PhaseCellScalarPrepare.prepare_exec` clears all 26 temporary setup ports,
with an explicit cleanup charge bounded by `52*w+53`; only the three actual
readiness counters remain changed. `prepareCanonical_exec` applies this to
the real 117-tape S3 bank and derives `Ready` plus clean multiplier tapes from
execution, without a prepared-state oracle. It preserves merged output, raw
operands, retained dimensions and native stacks. The unchanged table-role
encoding was separated into `ChirpBankRoleCode` to keep setup imports narrow.
Guarded checks peak at 1909.2 MiB (bank), 1897.3 MiB (counter generator) and
1934.5 MiB (complete setup). Next: route the merged words and stored scalar
into the generated-ready multiplier, publish and release its result/inputs,
generate the reciprocal/coefficient/weight data and establish the complete
cell/line numerical and uniform cost contracts. The expanded S3 and both S2
regression audits pass (13971 guarded build jobs, combined peak 7.7 GiB,
1.2 minutes). S3 remains active.

Executed scalar-application checkpoint (2026-10-25):
`PhaseCellTakeSetup` generates and releases a transfer count.
`PhaseCellScalarRoute.route_exec` generates ML from the retained doubled
header, routes the merged prefix into scalar operand port 84 and copies the
stored real factor from port 96 to 85. Every routing counter/scratch port is
cleared before multiplication; the factor source and original output suffix
are preserved. Readiness and multiplier cleanliness are proved to survive.
`PhaseCellScalarFinish` releases restored operand copies and publishes the
ordered product, clearing arithmetic data ports. `PhaseCellScalarRun` composes
the entire prepared pass. `PhaseCellScalarApply` adds generated readiness, and
`PhaseCellScalarCanonical.applyCanonical_exec` derives freshness/cleanliness
from the actual canonical bank, supplying the complete executed scalar pass
with decoded error ≤`2/2^q` and explicit setup/routing/product/release costs.
Readiness counters remain installed for reuse. Guarded checks peak at
1826.0/1921.6/1902.8/1916.3/1896.2/1892.4 MiB for generated transfer, routing,
finish, prepared run, setup/application and canonical entry.
The expanded S3 axiom audit passes (4323 guarded build jobs, combined peak
2.5 GiB). The stored factor is ordinary input data, not yet a generated reciprocal.
Next: retain/generate the reciprocal through the four-product stage (the raw
X suffix is a candidate storage location with proved S1 suffix support),
compose the entire cell arithmetic, generate weights/generators, release
prepared data/counters, and finish the cell/line error and uniform cost proofs.
S3 remains active.

Generator-suffix retention checkpoint (2026-10-25): the existing S3
programs now have proved generator-side suffix contracts through reversal,
upper multiplication, staging, lower multiplication, input release, compaction,
both branches, repeated-input production and final branch merge.
`mergedBranches_with_x_tail_exec` starts from one raw input stream and a suffix
beneath the combined generator bank, executes all four products and merge, and
restores that suffix exactly. A stored reciprocal word can therefore survive
under raw source port 110 while S1 uses its entire working bank. Runtime programs,
costs and numerical error bounds are unchanged; every original exact-stream
theorem is retained as the empty-suffix specialization of the same proof.
The counted access and scalar composition are now proved by the following checkpoint. Generating the
actual reciprocal, weights and generator data, prepared-data/counter release
and the complete cell/line numerical and cost contracts remain open. The expanded
axiom audit passes (4323 guarded build jobs, combined peak 2.6 GiB). All twelve
changed pipeline modules pass guarded single-file checks; the largest peak is
1914.7 MiB. S3 is active.


Retained-scalar composition checkpoint (2026-10-25):
`PhaseCellInteriorProducts.lean` proves `interiorProducts_exec` composes all four triangular products, exact branch subtraction,
counted reciprocal access, scalar counter setup, multiplication and staging-word
cleanup on the same 117 tapes. `copyAfterPrefix_exec` restores the full generator
prefix after copying its retained scalar, and `fetchCanonical_exec` derives all
access counts from the ordinary batch dimensions. The decoded result has error
at most `2/2^q` against the computed branch difference times the stored scalar.
`scaled_scalar_real_error` turns this into the real merge-stage bound after
rescaling, allowing imaginary FFT noise in intermediate rows. The reciprocal
word is still supplied numerical data; its generation is not proved. Repeated
inputs and multiplier counters remain explicit retained setup. Generated
coefficients/weights/reciprocal, complete `CellRun.Valid`, boundary/coupling/recovery
and full-line cost/error gates remain open. The expanded axiom audit passes
4327 guarded build jobs at 2.6 GiB combined peak; the composed theorem passes
its guarded single-file check at 1908.8 MiB. S3 remains active.


Real-stage handoff checkpoint (2026-10-25): `PhaseCellStageValues` identifies
cell coordinate `i` with stored reversed-row position `n*L+(L-1-i)` and proves
exact signed decoding of every compact branch numerator. Its
`upperNumerator_real_error` and `pairNumerator_real_error` give the real upper
and lower stage bounds on computed inputs: `4*B*2^l/2^q` and
`8*B*(2^l)^2/2^q`. Both generator branches use the same proofs, with real raw
generators and unrestricted imaginary FFT noise in intermediate rows.
`branchScalar_real_error` proves the actual output word satisfies the real merge
bound `8*B*(2^l)^2/2^q`. `cell_stage_precision` proves this latter budget is at
most `2^(-j)` when `B ≤ 2^b` and `b+2*l+j+3 ≤ q`; coefficient precision and address
width remain separate. No inverse-generator or reciprocal generation is assumed
proved: the reference generator still uses noncomputable `natInv`, and the
existing executable rational coefficient samples do not close that setup gate.
Full `CellRun.Valid`, weights, final rescaling, boundary/coupling/recovery and
line costs remain open. The new module checks at 1910.8 MiB, and the expanded
axiom audit passes 4328 guarded build jobs at 2.6 GiB combined peak. S3 is active.


Rational generator construction checkpoint (2026-10-25):
`NLogN.ToeplitzGeneratorIteration` defines a finite list recurrence with zero
initial vector, off-diagonal evaluation and an optional rounding map. Its
one-step and accumulated bounds are structural: error is at most
`rho^n*U+delta/(1-rho)`. Field embeddings commute with the unrounded recurrence,
so rational data give inverse-column approximations without evaluating `natInv`
or using a real rounding oracle. `NLogN.PhaseCellGeneratorData` instantiates this
constructor with the corrected executable rational coefficients of the actual
rounded cell matrix. It proves first-column and shifted-reverse accuracy,
computed corner at least `5/7` after one or more iterations, positive computed
reciprocal at most two, and reciprocal error at most twice the column error.
Choosing `j+1` iterations gives both column and reciprocal error at most `2^(-j)`.
This closes a numerical construction gap only: fixed-width encoding, tape
execution, setup costs and storage bounds are not yet proved. Weight setup,
full `CellRun.Valid`, final rescaling, boundary/coupling/recovery and full-line
contracts remain open. The data module checks at 1764.0 MiB; the expanded axiom
audit passes 4344 guarded build jobs at 2.5 GiB combined peak. S3 is active.


Encoded-generator checkpoint (2026-10-25): `PhaseCellGeneratorWords` constructs
real Gaussian numerators by computable rational floor arithmetic and proves the
grid error and exact zero imaginary component. Scale-two generator encoding
preserves the S1 numerator disk: the rational iterates have absolute value at
most `3/2`, so half-sized inputs and at least two grid bits absorb rounding.
`PhaseCellEncodedGenerators` constructs both generator banks and the reciprocal
word from the actual rational coefficient recurrence. It proves their lengths,
disk bounds, scalar norm at most two and accuracy against the actual rounded
matrix inverse. With `q ≥ j+2` and `j+2` iterations, each interpreted generator
and reciprocal is within `2^(-j)` of its target. Coefficient precision, arithmetic
precision, iteration count and storage width remain distinct. These constructors
close the numerical word/range obligations; tape generation, intermediate width
and bit-growth bounds, setup cost/storage, weights, full `CellRun.Valid`, final
rescaling and boundary/line contracts remain open. The expanded axiom audit
passes 4346 guarded build jobs at 2.5 GiB combined peak. S3 is active.


Constructed-data execution and cell-run checkpoint (2026-10-25):
`PhaseCellPreparedInterior.lean` proves `preparedInterior_exec` instantiates the 117-tape execution with the
constructed encoded generators and reciprocal, discharging their range and
reality conditions and returning their inverse-target accuracy. The setup bank
is still an input; this is not a setup-generation execution theorem.
`PhaseCellInteriorRun` interprets the computed upper/lower arrays and the actual
scalar output tape as `CellRun` fields, retaining reversed-row coordinates,
ring factors and input magnitude scale. `interiorRun_valid` derives the
triangular, merge and input-magnitude clauses structurally.
`preparedRun_valid` additionally derives generator/scalar accuracy from the
constructors and uses `q ≥ b+2*l+j+3` for `B ≤ 2^b`. It establishes
`CellRun.Valid` at tolerance `2^(-j)` conditional on exactly the three remaining
weight-stage errors: reciprocal weights, scaled input production and final
weight multiplication. Those hypotheses are pending work, not executed stages.
Setup tape generation/cost/storage, these weight stages, final word conversion,
boundary/coupling/recovery and the line endpoint remain open. The conditional
cell-run module checks at 1918.4 MiB; the expanded axiom audit passes 4367
guarded build jobs at 2.6 GiB combined peak. S3 remains active.


Complete numerical cell-run checkpoint (2026-10-25): `PhaseCellWeightData`
constructs reciprocal-weight, normalized-input and final-output Gaussian words
by rational floor arithmetic on the actual selected similarity samples and
computed inputs. It proves each rounding error and the reciprocal-weight range.
For RHS magnitude at most `2^cExp` and weight lower bound `2^(-e)`, normalization
by `2^(cExp+e+1)` places the rational encoder argument within `1/2`; at least two
grid bits therefore give the S1 input disk. `PhaseCellNumericalRun` uses
`inputExponent p cExp = cExp+(8*p+1)+1` and constructs all `CellRun` fields from
rational data and the actual interior scalar-output tape. `numericalRun_valid`
proves the complete `CellRun.Valid` contract with no assumed stage-error facts,
at tolerance `2^(-j)` when `q ≥ inputExponent p cExp+2*l+j+3`. It preserves
ambient coordinates and the selected coefficient precision `2^15*p`.
This is a complete numerical-data/validity theorem, not a composed tape solver:
setup and weight-stage execution, intermediate word/bit-growth fits, final
conversion/publication, setup and line costs, boundary/coupling/recovery remain
open. In particular the computed numerical `y` fields have not yet been produced
on the output tape. The numerical-run module checks at 1906.3 MiB; the expanded
axiom audit passes 4369 guarded build jobs at 2.6 GiB combined peak. S3 is active.


Executed weight-input checkpoint (2026-10-25): `PhaseCellWeightStream`
uses the existing `rmulOne`/`cmulStream` engine for aligned varying real weights.
It keeps arithmetic grid precision `q`, normalization `b`, multiplier counter
`q+b`, magnitude exponents and word width separate. Its output is the actual
`tdivN (q+b) (x*a)`, with error at most `2/2^q` against the normalized product,
proved signed-word fits and exact input/table/private-stack restoration.
`PhaseCellWeightedInput` constructs reciprocal table words from the rational
weights. Their lower bound `2^(-e)` and RHS norm bound `2^cExp` discharge operand
fits; normalization `b=cExp+e+1` makes every actual output satisfy the S1 disk.
The interpreted real input-stage error is at most `2^b*2/2^q`, hence at most
`2^(-j)` when `q ≥ b+j+1`. No output-fit oracle is required. The stream's cost is
`N*(rmulCost w+6*w+2)+8`. `ScalarFinish.finish_stream_exec` generalizes the existing
cleanup proof to an entire factor stream, with unchanged runtime code; the old
single-scalar theorem is its singleton specialization.
This addresses machine truncation toward zero directly. The earlier rational
floor-based numerical run is not asserted equal to the machine data. Fixed-bank
routing, generation of the `q+b` readiness counters, setup generation, final
weight multiplication/publication and boundary/line composition/costs remain
open. Guarded checks peak at 1897.5 MiB (generic stream), 1902.9 MiB (input stage)
and 1903.0 MiB (shared cleanup). S3 remains active.


Closed 117-tape input-weight checkpoint (2026-10-25):
`PhaseCellWeightRoute` generates one `M*L*w` symbol counter for both source
transfer and table copying, then releases it and the row count. Its cost is
`22*M*L*w+15*M*L+17*M+34`; the complete table suffix is preserved.
`PhaseCellWeightRun` composes routing, the existing varying-weight multiplier
and shared stream cleanup. `PhaseCellWeightPrepare` temporarily extends the
actual unary precision header by the normalization descriptor on port 116,
executes readiness generation at `q+b`, then restores the original precision
and descriptor symbols. Only the three counters remain; their paid release is
proved too. `PhaseCellWeightClose.lean` proves `ScalarPlacement.closedWeights_exec`
executes setup, routing, multiplication, publication and counter release,
changing only the persistent output prefix. `closedWeightedInput_exec` supplies
the constructed reciprocal words, derives operand fits and the S1 output disk,
and gives real-stage error at most `2^(-j)` for `q ≥ b+j+1`, with
`b=cExp+e+1`. No readiness, routing-count or output-fit oracle remains.
Ordinary descriptor/data headers and reciprocal words are still input data:
executing their setup constructors and integrating the normalized stream into
the interior bank remain open, as do final weighted publication, bit-growth and
storage bounds, boundary/coupling/recovery and the full line endpoint and costs.
The expanded axiom audit passes 4377 guarded build jobs at 2.6 GiB combined
peak. S3 remains active.


Closed final-weight stage checkpoint (2026-10-25): `PhaseCellOutputBounds`
proves that the actual scalar result has norm at most four. Restoring its
cell scale is the exact numerator shift `d=b+2*l+2`, with
`2^d=4*2^b*(2^l)^2`. Both shifted operands and final products fit at
`w ≥ q+d+4`. The final error charges multiplier truncation and weight encoding
at the restored magnitude: `(2+2^(d+2))/2^q`. Consequently the complete final
weight-stage tolerance `2^(-j)` needs `q ≥ d+j+3`, or `b+2*l+j+5`, two bits
beyond the triangular-stage budget.
`PhaseCellOutputScale` generates counts, isolates the owned output prefix,
executes the existing shift machine and restores its staging, leaving the
borrowed suffix unchanged. `PhaseCellOutputClose.lean` proves `ScalarPlacement.closedOutputWeights_exec`, which saves the shift header, reuses the closed
aligned-weight pass at extra shift zero, and restores the exact header symbols.
Only the weighted output prefix changes; no readiness or output-fit oracle is
supplied. Its explicit cost is prefix rescaling plus `closedWeightsCost q 0`
and `4*d+4` for header saving/restoration. `PhaseCellOutputData` proves decoded
word accuracy against the actual rational similarity weights.
Data/descriptor generation, integrating stage banks and their computed arrays
into the complete cell execution/validity theorem, final line ordering/conversion,
boundary/coupling/recovery and line/setup/storage costs remain open. Both weight
stages now execute as standalone 117-tape components. The expanded axiom audit
passes 4398 guarded build jobs at 2.6 GiB combined peak. S3 remains active.


Actual-arithmetic cell-validity checkpoint (2026-10-25): `PhaseCellRowTable`
proves that compact index `n*L+(L-1-i)` selects row `n` and cell coordinate `i`.
The final similarity table uses this actual reversed order, with ambient phase
coordinates unchanged. `PhaseCellExecutedData` constructs the actual normalized
input numerators, scalar interior stream and final shifted/weighted output
words from raw Gaussian RHS data. Input disk, input-stage error and scalar
magnitude bounds are derived from the constructors and selected weight bounds.
`executedRun_valid` in `PhaseCellExecutedRun.lean` proves the complete real `CellRun.Valid` contract for these actual stage words and decoded
output symbols, with no stage-error assumptions and no equality with the
rational-floor reference. The common bounds are
`q ≥ inputExponent p cExp+2*l+j+5` and
`w ≥ q+inputExponent p cExp+2*l+6`, at tolerance `2^(-j)`.
The shared `inputExponent` definition moved to `PhaseCellWeightData`; the old
numerical-reference API retains the same definition and behavior.
This composes the numerical contracts of the individually executed stages;
it does not yet provide their complete bank-to-bank tape execution. That
composition, data/descriptor generation, final ordering and complex/line
endpoint, boundary/coupling/recovery and full setup/storage/line costs remain
open. Guarded checks peak at 1910.7 MiB (actual run), 1902.1 MiB (stage data)
and 1891.8 MiB (row table). The expanded axiom audit and
reference regression pass 4401 guarded build jobs at 7.5 GiB combined peak.
S3 remains active.


Input/interior execution composition checkpoint (2026-10-25): `PhaseCellInputRows`
proves structurally that the aligned product on a flattened batch is exactly
the flattening of its rowwise products. `PhaseCellInputInstall` derives the
transfer count, installs the normalized stream on raw input tape 111, and pays
for releasing the owned table copy and normalization descriptor. Its endpoint
is exactly `singleBranchInputWithXTail`, including the unchanged borrowed X
suffix and persistent output tail. `PhaseCellInputStage` starts from raw RHS
words, constructs the actual normalized words through execution, and installs
them. `PhaseCellInputInterior` then executes the four triangular products,
merge and retained scalar multiplication; no normalized-input data is assumed
in its initial bank.
`PhaseCellExecutionSizing` proves a conservative controller-compatible choice:
`cExp=rhsExp+2*l+j+5`, `b=inputExponent p cExp`, `q=2*b`, `w=4*b+8`.
It preserves the given RHS bound and satisfies the actual-run validity and
final word-width bounds. `PhaseCellNormalizationHeader` uses the existing
half-count machine on the precision header to generate the normalization
count, preserving all actual header symbols. `inputInteriorFromPrecision_exec`
therefore needs an empty normalization slot initially, and includes its
`6*b+4` generation cost. Every other input/interior setup, routing and owned
staging release cost is included. The interior endpoint still explicitly
retains its repeated raw input and three scalar counters.
Coefficient/table data generation, output-control and table loading after the
interior stage, final stage composition and ordering, complex/line correctness,
boundary/coupling/recovery and uniform setup/storage/line costs remain open.
The even-precision choice has not yet been matched into a uniform line budget.
The expanded axiom audit passes 4407 guarded build jobs at 2.5 GiB combined
peak. S3 remains active.

### Next implementation gates

1. S3: implement one generated cell interval through S1 and prove `CellRun.Valid`
   with rescaled error and a paid cost; cover clipped/empty cases before a line loop.
2. S5: implement a generated boundary page and a repeated solve with explicit
   computed-Schur perturbation, reciprocal stability, precision, storage and costs.
3. S3: compose the two interior passes and S5 via the generic error lemmas and
   establish the shared `SolveSpec` endpoint from actual returned words.
4. S4: prove descriptor generation, locality, ownership/coverage and publication,
   then batch equal keys and prove the complete ledger/amortization.

The numerical interface is pinned; these execution, locality, stability and cost
obligations remain open. They do not mark S3, S4 or S5 complete or change kappa.

Verification: guarded checks pass for `PhaseCellInterface` (1730.6 MiB),
`PhaseCellReferenceSpec` (1737.3 MiB) and `PhaseCellInterfaceCheck` (1723.0 MiB).
The guarded audit build completes 3851 jobs at 2.4 GiB combined peak. The audit
accepts only propext, Classical.choice and Quot.sound, with default proof limits.

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

**Current status.** S2's forward primitive is complete; S3's inverse mathematics
is checked, while the S3/S4/S5 machines and fused schedule are open. The shared
contract above is the implementation entry point. The mathematics below remains
a reference and is not yet used by `mulInTime` as a phase-cell inverse backend.

**Resume point.** Use S1's checked `ShortConv.Fixed.closed_exec` for the interior
products, targeting `CellRun.Valid` and the backend-independent `SolveSpec`.
Develop the S5 prepared-boundary endpoint in parallel in the design, with separate
setup/solve/release costs. Compose these locally before introducing S4's generated
core/halo schedule. The existing `pcSolve`/`phase_resampB₀_spec` and `rsbAllG`
whole-axis path are references and optional adapters, not the required new schedule.

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
     setup key, matched into the shared S3–S5 ledger above. `Cost/MatchBandB.lean`
   remains a reference for supplier matching, not the required outer schedule.
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
| b3c | the costs of b3b, matched into the shared S3–S5 ledger | 1–2k | 4–6 weeks |
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

### Generated final output controls (2026-10-25)

`ScalarPlacement.outputFromHeaders_exec` closes the final weight stage from
ordinary retained headers: precision `q=2*b`, row exponent `l` and width `w`.
It generates shift `d=b+2*l+2` and remainder `w-d`, executes rescaling and
similarity multiplication, then erases both owned controls. Only the output
prefix changes; prepared similarity data and borrowed suffixes survive exactly.
The actual-word error contract is retained. The generated-control and cleanup
overhead is `6*b+8*l+6*w+6*d+28`; the existing output execution cost is added.
The whole-cell caller must still arrange the prepared similarity table after
interior execution and release its retained work. Generated coefficient pages,
boundary/coupling/recovery and the uniform line ledger remain required.

The input/interior handoff `closedInputInterior_exec` releases the three
readiness counters after the entire generated-normalization and actual-input
pipeline. The following output stage may generate fresh counters. The normalized
raw operand on 111 remains retained and must be explicitly released; the
shared generator/scalar bank and arbitrary borrowed suffix remain untouched.

The final similarity table may be retained immediately below the two generator
banks and scalar on tape 110. `fetchOutputTable_exec` generates its address and
length from ordinary retained dimensions, copies the table to 96 and restores
110 exactly, including its arbitrary suffix. All addressing workspace is
released, with cost `40*M*L*w+15*M*L+17*M+12*w+49`. This is a paid copy
contract, not a coefficient-generation theorem. The caller still owes actual
setup generation and cleanup of the owned copy after the final pass.

### Cell arithmetic composition (2026-10-25)

`cellArithmetic_exec` composes the complete actual-word interior chain from a
staged raw source and reciprocal-weight copy. It borrows a retained page of two
generator banks, the reciprocal scalar and final similarity table, preserves
that entire page and arbitrary suffix, and emits the final weighted word list.
The normalized raw operand on 111 and the copied final table on 96 are erased.
Every normalization, multiplier, addressing and shift descriptor is generated
and released. `cellArithmeticCost` adds every component cost, including both
readiness releases, final-table movement and `4*M*L*w+2` input-copy release.
The output remains in the compact reversed row order used by the numerical
backend. Connecting constructed setup data to this exact execution, publishing
row order, executing numerical setup and the boundary/line gates remain open.

`constructedCell_exec` now instantiates the complete arithmetic execution with
constructed generator/reciprocal words, actual ambient similarity weights and
raw source rows. Its terminal stream is exactly `executedOutputWords`; the same
contract supplies `CellRun.Valid` through `executedRun_valid` for each row.
Generator, scalar and weight bounds are derived rather than supplied. This
closes the arithmetic data/execution bridge while preserving the staged-bank
boundary: setup generation and input staging still need executed, paid callers.

`publishRows_exec` publishes coefficient-row reversal while preserving an
arbitrary output suffix. It generates and releases the total prefix count,
erases only the old prefix and uses two symbol moves to preserve word bits.
Its bound is `42*M*L*w+19*M*L+26*M+24`; all other stacks are restored. The
closed caller still owes generation of the batch/record headers and the
identification of actual output-word rows before this publication primitive.

The publication caller `publishFromDimensions_exec` now derives `M` and
`L*w` from ordinary retained `2*M`, `L`, `w` headers and releases them after
publication. Its bound is `42*M*L*w+19*M*L+34*M+6*L*w+9*L+37`. It restores
all other stacks and the arbitrary output suffix. Row decomposition of actual
terminal output data and composition into the cell caller are still required.

`publishedCell_exec` now appends generated-header publication to constructed
cell execution. A structural `outputRows_spec` produces equal-length rows from
the actual terminal list, including empty-row cases. The final stream is exactly
`publishedWords M L (executedOutputWords ...)`; retained setup/suffix and all
cleanup guarantees survive. The cost adds `publishFromDimensionsCost`. The
remaining numerical publication obligation is the coordinate-read identity
between forward-order words and the reversed-index `executedRun` endpoint.

`executedRun_y_published` closes the publication coordinate handoff: each
`CellRun.y i` is exactly the decoded final word at forward position `n*L+i`.
The underlying `publishedWords_read` reflects within each row and preserves
arbitrary suffixes, without extra arithmetic/rounding or error. Together with
`publishedCell_exec` and `executedRun_valid`, the real cell arithmetic and
coordinate-order publication now share one actual-word numerical endpoint.
Setup generation/source staging and the boundary/line gates remain required.

### Amplified precision correction (2026-10-25)

The earlier half-precision recovery choice `q=2*b` is insufficient for final
error allocation: the rounded-cell estimate contains `2^b*η`. Final sizing
now uses `q=4*b`, width `8*b+8` and stage exponent `2*b`; b is chosen from
the requested final accuracy and original source magnitude.
`execution_cell_error` proves the full rounded-cell error is at most `2^-j`.
`quarterCount_exec` generates b from the retained precision, preserves every
source symbol and releases the temporary half header for `22*b+10`. Existing
half-count execution contracts are valid but do not instantiate this final
sizing; normalization/output-shift wrappers still need migration. Preserve the
ambient s in later line/error bounds.

The quarter-count migration is complete through `publishedCell_sized_exec`.
Both normalization and output-shift controls recover b from q=4*b using 115
as restored intermediate workspace. The input/interior/output/publication
execution contracts and costs now require q=4*b; the earlier q=2*b wrappers
have been replaced. The sized caller derives stage precision 2*b and word
width 8*b+8 from requested final accuracy and original RHS magnitude.
Normalization costs 22*b+10; generated output controls cost
22*b+8*l+4*w+6*d+29 before final control release. The existing complete
rounded-cell error budget now fits the executed precision. Exact interior
comparison still requires ambient geometry and a principal-system hypothesis.

### Exact published real interior comparison (2026-10-25)

`publishedCell_accuracy` proves final `2^-j` error for each actual published
forward-order word against a solution of the original ambient principal
system. It derives the stage validity, source bound and `L*η≤1`, applies the
existing structural `rounded_cell` theorem and pays its amplified error using
the quarter-count sizing. The caller still proves interval fit, interior
membership, common phase cell and maximality in the stated principal set.
These geometry conditions are not generated descriptors or a halo-local
replacement theorem. Setup/source staging and boundary/line costs remain open.

### Paid per-call payload staging (2026-10-25)

The retained 110 page may contain two generator banks, scalar, output weights,
then per-call RHS and reciprocal input weights. `stagePayloadBank_exec` starts
with empty 93/96 work prefixes, copies RHS and reciprocal words with generated
addresses and yields the exact existing input ABI. It restores the full page
and arbitrary suffix. RHS is per-call borrowed payload and is not reusable
setup-key data; gathering/packing still needs its own executed transfer ledger.
`fetchPage_exec` is the single counted-copy engine, also used for final weights.
Its bound is `(16+12*k)*M*L*w+15*M*L+17*M+12*w+4*k+42`. Staging adds the
k=3/k=4 copies and `4*M*L*w+4` for moving RHS to its working port.

`stagedCell_sized_exec` now composes paid payload staging with sized arithmetic
and publication. Its endpoint is the initial empty-work bank with only the
published output prefix replaced. The entire reusable setup and per-call RHS/
reciprocal payload are restored, as are all headers, native stacks and the
arbitrary output suffix. Staging adds `stagePayloadCost` to the complete cell
cost. The `CellRun.Valid` numerical endpoint survives composition. Setup
creation and initial payload gathering/packing still require executed callers;
the per-call payload remains outside the reusable setup key.

### Computable ambient geometry (2026-10-25)

`PhaseCellDiscreteGeometry` computes exact phase indices by signed integer
division, with a proof matching the existing tie convention. Its Boolean
interior predicate, duplicate-free per-phase index lists and computed full
interior set match the original analytic definitions. All coordinates and
phase cuts remain ambient. These constructors do not generate artificial
halo cuts and do not establish tape execution, scan cost or interval endpoints.
They provide the computable predicates for that next descriptor stage.

### Generated full-cell interval geometry (2026-10-25)

`intervalStart`/`intervalLength` compute full ambient interior intervals from
exact integer phase metadata, with zero length for empty phases. Convexity
proves nonwrapping fit, exact coverage, common phase and maximality.
`generatedCell_accuracy` applies the published real solver accuracy theorem
using these computed endpoints and computed interior mask; only an interior
anchor is needed to select a nonempty phase. No arbitrary interval/geometry
oracle remains in that numerical specialization. This does not handle
artificial halo cuts or establish execution/cost of descriptor generation.

`PhaseCellGeneratedCover` computes the nonempty phase ownership schedule.
Its generated intervals cover exactly the full ambient interior, with no
duplicate phase keys and unique ownership of every coordinate. The number of
keys is at most s. The list deduplicates exact integer phase labels; no
arbitrary interval-cover input is assumed. This is metadata correctness, not
executed descriptor generation or artificial-halo-cut geometry. Total-volume
and length-group accounting remain separate cost obligations.

`PhaseCellGeneratedVolume` closes full-interior volume accounting: every
computed span length equals its phase-fiber cardinality, and the sum over the
actual duplicate-free key list equals the computed interior mask cardinality
and is at most s. The cardinality proof preserves physical-to-ambient
coordinates exactly. This supplies a volume ledger for cell costs, while
length-group scheduling and executed metadata/setup generation remain open.

`PhaseCellLengthGroups` now computes equal-length phase batches and proves
positive keys, nonempty batches, no duplicated keys/rows and exact volume
preservation: sum of batch count times length equals the interior cardinality
and is at most s. Natural-index `groupOrigin` matches the existing arithmetic
ABI, with generated geometry for every bounded row. This is a numerical
batching schedule, not an executed scheduler. Length equality alone does not
identify the complete setup reuse key or any prepared boundary page.

`lengthGroup_sized_exec` connects the computed equal-length schedule to the
complete staged arithmetic/publication program. Batch count and origins are
derived, not supplied; exact restoration and all component costs are retained.
`lengthGroup_accuracy` derives requested published error for each actual row
from generated ambient geometry. The constructed initial setup/payload bank
still needs executed setup/gathering, and the outer key iteration is not yet
an executed scheduler. Full reuse-key equality and boundary/line costs remain
separate obligations.

### Integer inverse-generator setup representation (2026-10-25)

The shared structural generator engine now admits rings, so integer setup uses
the same row evaluation/step definitions. `dyadicGeneratorIter_spec` identifies
integer numerators at denominator 2^(P*n) with the existing exact rational
recurrence. Actual coefficient numerators use the corrected exponential
routine. Both encoded column banks are exactly integer-quotient encodings of
that integer vector; no new numerical oracle or reference equality assumption
is introduced. This representation prepares executed setup and avoids rational
reductions, but reciprocal encoding, setup widths and paid tape execution are
still required.

The integer generator corner is proved positive, and
`integerReciprocalWord_eq` identifies its integer-division scalar with the
existing encoded reciprocal exactly. All three retained generator/scalar data
now admit integer-only representations. Stored column entries fit width
P*n+3; the reciprocal division numerator fits q+P*n+2. These do not yet bound
all step accumulators or supply executed setup/cost/space contracts.

Setup row products and arbitrary partial sums/RHS accumulators now have
structural signed-word bounds. With L≤2^l, the common allowance
`integerSetupWidth=P*(n+1)+q+l+5` covers those operations, stored integer
columns and the reciprocal numerator and is monotone in iteration count.
The first iterate is exactly a scaled unit vector, so row-step bounds apply
from n≥1. The contracts do not yet establish tape execution, coefficient
argument arithmetic, setup cost or total peak storage.

### Executed integer setup initialization (2026-10-25)

`generateSeed_exec` emits the actual scaled unit first iterate from unary
L/W/P headers, with exact restoration and an arbitrary output suffix. It
generates/releases L*W, emits zeros and replaces bit P in the first word; its
cost is bounded by 10*L*W+9*L+6*P+17. The program is independent of the
dimensions. Existing integer-data/format lemmas identify its output exactly
with the first integer generator iterate. This is initialization, not a
complete coefficient/row/iteration/reciprocal setup execution theorem.

### Executed integer generator-row arithmetic (2026-10-25)

The existing signed real multiplier stream now exposes its direct `Fits`
contract, including truncation precision zero. The same scalar preparation
program generates zero-precision readiness from ordinary retained headers
when W≥5; the positive-precision API is preserved. `integerProducts_exec`
executes those products with paid setup and exact operand/scratch restoration.
`subtractRow_exec` consumes an arbitrary product list through the shared
subtraction automaton, leaving one accumulator word and restored work tapes.
The composed 117-tape `integerRow_exec` costs at most
`prepareCost 0 W + L*(rmulCost W+13*W+12)+10`; generated counters remain explicit.
`generatorRow_exec` proves the result is the next actual integer generator
entry and derives its signed-word fit. The width applies to stored words;
coefficient-page and scaled-RHS staging, row/iteration control, reciprocal and
column encoding, setup release and combined peak/cost proofs remain required.
This arithmetic kernel does not supply a free coefficient page or close S3.

`integerRowPrepared_exec` separates the reusable arithmetic call from executed
readiness generation. Only the accumulator word changes; installed counters,
operands and scratch restore. Its bound is `L*(rmulCost W+13*W+12)+10`, allowing
setup to be paid once across row calls. `rowColumnWords_eq` proves each row's
column operand is the stored integer vector in its existing order. The outer
iteration must still execute coefficient/RHS staging and publish each row.

### Executed integer generator iteration (2026-10-25)

Row staging now generates/releases L*W and copies borrowed column/factor/RHS
prefixes with exact suffix restoration. Row publication releases only owned
copies and preserves the output word's symbol order. The composed row call
changes only the output prefix and costs at most
`L*(rmulCost W+43*W+21)+14*W+55`. The consuming variant also releases the
owned factor/RHS prefixes, keeping their arbitrary suffixes, with bound
`integerRowCost L W=L*(rmulCost W+55*W+30)+20*W+73`.

The existing unary scanner executes N such rows, restoring the original count
symbols at bound `N*(integerRowCost L W+5)+4`. A stable context proves readiness,
column storage and workspace survive each iteration. Descending generator rows
and prefix publication emit the next complete integer column in its original
order. All signed fits follow from the existing structural bounds. The initial
wrapper generates readiness once at extra `prepareCost 0 W`, and the counters
remain installed for reuse. The column is borrowed on 110, owned factor and RHS
pages are consumed on 111/112, and output is prefixed on 113; these setup-local
roles precede assembly of the retained runtime page.

The factor page is independent of iteration count. The RHS page is the scaled
unit seed in reverse word order. These identities do not execute page generation:
coefficient/RHS construction, repeated-iteration control and column replacement,
reciprocal/column encoding and complete setup release/peak-space/cost proofs
remain required before this becomes a closed setup theorem.

### Generated iteration RHS and exponent (2026-10-25)

`generateReverseSeed_exec` emits the existing single-word power seed, generates
(L-1)*W and prepends that many zero symbols. It restores every count and work
tape at bound `10*L*W+15*L+6*d+37`, preserving an arbitrary existing suffix.
`generateRhsPage_exec` handles empty interiors through an executed branch,
with uniform bound `10*L*W+15*L+6*d+39`.

`generateIterationRhs_exec` computes P*(n+1) from ordinary P/n headers, emits the
page and releases the exponent header. Its bound is
`10*L*W+15*L+12*P*n+21*P+49`. The composed `generateRhsIntegerStep_exec` executes
RHS/exponent generation, scalar readiness and the entire generator row loop at
`prepareCost 0 W + L*(integerRowCost L W+10*W+20)+21*W+53`.
The original RHS suffix on 112 restores after the generated page is consumed;
the temporary exponent on 115 restores. Ordinary P/n headers on 114/116 are
borrowed. The factor page is still a stated consumed input, and the input column
remains borrowed. Generating coefficients/factors, replacing the column and
controlling repeated iterations, generating setup widths, reciprocal/column
encoding and combined setup cost/space/release proofs remain separate obligations.

### Executed integer-column construction (2026-10-25)

The next-column transition is now an actual program: derive L*W once, erase
only the owned old prefix, install the computed prefix and release temporary
output, preserving both borrowed suffixes. Its bound is `18*L*W+9*L+18`.
Factor copying derives L² and L²*W, restores the retained page and releases
both generated counts at `16*L²*W+15*L²+9*L+22`.

One repeatable iteration reuses readiness and the factor page, generates its
RHS and exponent, executes every row, installs the next column and increments
the ordinary iteration header. Only the current column and iteration count
change. The bound is
`I(L,W)=16*L²*W+15*L²+L*(integerRowCost L W+28*W+38)+21*W+94`.
The existing unary scanner executes M calls at `M*(I(L,W)+5)+4`, restoring the
original supplied count symbols. A stable context proves the next call's
readiness, column fits, immutable factor page and empty workspace.

`generateIntegerColumn_exec` emits the unit seed for a nonempty cell, initializes
the iteration header, prepares readiness once and runs the complete loop. No input column,
RHS page or readiness is supplied. It emits integer column M+1 at
`prepareCost 0 W+M*(I(L,W)+5)+10*L*W+9*L+6*P+22`, with its arbitrary original
column suffix retained. Signed decoding followed by division by 2^(P*(M+1))
has the existing error ≤2^-M against the rounded Toeplitz inverse column. The
actual decoded corner is positive, supplying the later reciprocal divisor.

Setup-local roles: 109 retains the square factor page; 111 holds a consumed
private copy; 110 holds the current column; 113 is temporary row output.
The supplied iteration count on 101 is borrowed and restored through archive
100 after zero-precision readiness has been generated. The multiplier reads
its precision from its installed counter, so archive 100 may be live during
this loop. Row headers 102/103, word width 94 and coefficient precision 114
are borrowed. Header 116 is generated at 1 and incremented to M+1. Every RHS,
exponent, square/symbol count and row work tape restores.

This entry point still assumes the stated retained factor page and ordinary
sizing headers. Its L²*W page remains an explicit storage obligation; neither
this scalar cost nor per-module checking peaks establish the final S3 uniform
cost/stock envelope. Coefficient/factor generation, final sizing/header
selection, quotient/reciprocal encoding and setup release/combined peak/cost
matching remain required, alongside outer scheduling and full-line composition.


The executed column encoder now generates and releases its slice counters from
retained P/n/q/W headers, preserves the raw integer column and borrowed suffixes,
and emits the existing dyadic runtime column words. Signed decoding and the
existing inverse-column error bound hold for the emitted words. The encoder
cost is L*(20*W+6*(2*q+8)+23)+31*W+57. This is a separate verified entry point;
composition with raw column generation, reciprocal and reversed-branch encoding,
factor-page generation and the combined S3 cost/storage envelope remain open.
