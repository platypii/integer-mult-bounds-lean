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

This is the implementation contract for the inverse work packages. S3 is
implemented at this supplier boundary; S4/S5 remain open. It supersedes the older whole-axis loader/resume instructions below;
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

Current S3 acceptance (2026-10-28): `Mult/PhaseCellS3.lean` combines actual
production execution, restoration, selected fast time and compiled stock with
normalized exact-inverse error at most `3/2^p` and unit-ball preservation for
full-line records. General halos retain their principal-system error contract.
`FastB0.executed_dispatch_resampB₀_spec` supplies the complete normalized `B₀`
`ApproxMap` with uniform scaled error 10 and unit-ball preservation, using an
output chosen from the same restored descriptor dispatcher. Complex input
quantization is charged explicitly; `target ≥ p+8` discharges the smallness gate.
This complex-vector bridge avoids identifying the shared batch execution with
two independent real calls. The full real `SolveSpec` above remains proved.

All twelve new/changed implementation modules pass guarded standalone checks
(maximum 3,328 MiB), as does the expanded S3 axiom audit (3,376 MiB).
The expanded audit and both S2 forward/supplier audits pass together (15,587
jobs; 8.3 GiB combined peak), with default proof limits and only the three
approved axioms. S4's exposure/publication, halo/global locality and tensor
composition, remaining S5/S6 work and kappa are unchanged. Implementation
checkpoints below are historical; the current S3 acceptance is recorded here.

### Retained-mode placement correction (2026-10-29)

The retained-mode interfaces below are not yet usable for positive workspace
width. A guarded Lean diagnostic proved that the current
`PackedHaloSetup (freshGeometry := false)` implies `V = 0`: its factory
`LengthKeyReady.blank` on logical 115 requires physical 149 to be empty, while
retained geometry makes it a `V`-bit word. The other factory arithmetic/work
ports 147--151 also overlap the retained bank. The mode-propagation theorems
remain conditional, but do not establish an executable positive-width call from
real retained state. Earlier checkpoint wording about retained-mode execution
must be read with this correction.

`retainedFactoryRouting` moves the five conflicting factory ports 147--151 to
scratch 158--162. Its checked geometry frame transports the existing factory
frame through the permutation, including the formerly overlapping actual
geometry slots. `protectRetainedFactory` is the generic placement and
`retainedGeometryFactory` instantiates the existing numerical factory. This
placement still needs to be threaded through the factory/setup input views and
mode execution contracts. S4 remains open.

### S4 implementation checkpoint (2026-10-28)

The new `NLogN/SchurLocality` proves decay through supported neighborhoods;
`PhaseCellHaloLayers`, `PhaseCellLocalityPrecision`, and `PhaseCellLocality`
instantiate it for the actual rounded matrix. Depth
`16*p*(target+p+4)` gives absolute locality error at most `2^-target` for
RHS bounded by one, without an ambient-size factor.
`PhaseCellCoreWindows` generates disjoint quotient-owned cores and padded
interval halos, using the full principal system when padding crosses the
period seam. `PhaseCellCoreDescriptors` supplies bounded interval endpoints
with exact principal-set agreement. `PhaseCellCoreWindowCost` bounds fallback
indices by three when radius ≤ core width, and total halo volume by `9*s`
when also core width ≤ s. `Mult/PhaseCellGeneratedWindows` assembles these
into a global real `SolveSpec`, conditional only on the local arithmetic
solver contracts and the stated matrix regime. This is numerical assembly,
not an executed S4 machine.

Integration must address the existing `FamilyDispatchFrame.source` contract:
its payload is an ambient `chirpLine s` per input even for interval descriptors.
The new geometric volume bound does not price repeated full-source loading.
Descriptor execution now uses a shared `descriptorEnumeration_do` theorem for
core intervals, halo endpoints and filtered group origins. The core-origin host
computes its loop count from numeric headers and emits the ordered origin
packets with a step bound and preserved external stacks. `PhaseCellCoreGatherExec`
instantiates the existing restoring ordered gather; its controls remain a caller
obligation. `PhaseCellCorePublication` executes individual core copies, including
their source-prefix traversal cost. These are components, not a fused schedule.
Paid packed input/output, complete-key reuse, tensor composition, simultaneous
stock, selected sizing, and the fused R4 schedule remain open. S4 is not complete
and kappa is unchanged.

Packed-storage progress: `PhaseCellPackedInterval` proves length, ambient
indexing, slicing, encoded-word equality and unchanged error bounds for a
physical halo slice. `coreGather_packed` identifies the ordered gather's output
with those slices. `publishPackedCore_exec` crops a packed halo in
`6*radius*wordWidth + 10*coreLength*wordWidth + 16` steps, restoring its source
and all other stacks. `PhaseCellPackedComponentInputs` reuses the existing
component splitter by embedding its count register into a private register;
it prepares both components in `20*L*w+9*L+20` steps while preserving the
ambient-period header. This does not yet refactor the S3 solver: its boundary
gather/scatter addresses, retained original-input operations, full output
assembly and downstream time/stock bounds still use ambient-length storage.

`PhaseCellSparseScatter` now proves sparse publication once over arbitrary
lists. `PhaseCellPackedBoundaryScatterData` translates boundary offsets by the
halo origin while retaining `bOrder` and ambient field values; the existing
full-line `boundary_scatter_field` is a specialization of this proof.
`packedBoundaryScatter_exec` runs the unchanged scatter machine into a packed
halo in at most `35*L*w+6` steps, with arbitrary borrowed source/output suffixes
and exact restoration of other stacks. Its control tape and zero halo buffer
are explicit preconditions. Generating those resources and integrating this
primitive into the retained S3 recovery lifecycle remain to be done.

The packed recovery movement components now include binary bank initialization
(`40*V+41` steps), ambient-origin scanning started at the halo origin, bank
release, and the existing advance-to-gap converter. `packedPublicationProgram_exec`
composes these from actual metadata and coordinate packets.
`controlledPackedBoundaryPublish_exec` combines conversion, generation of a
halo-sized zero buffer, scattering, and local control cleanup in `89*L*w+41`
steps. The halo length is held in private register 222, preserving the ambient
header. Joining origin generation to this publisher and replacing the retained
S3 recovery lifecycle remain open; these component theorems do not establish
the S4 tensor machine, stock bound, setup count or fused R4 schedule.

### Prepared packed input lifecycle checkpoint

`packedHaloPreparedInput` separates the repeated input program from factory
initialization and final factor/table release. It executes packed RHS production,
the prepared residual solve, recovery, and `packedPreparedInputRelease`.
`PackedPreparedBank` packages solve readiness and numerical workspace; the
actual halo residual, solution publication and recovery proofs use this interface.
The numerical factor values and column accuracy remain separate explicit facts.

The post-recovery continuation has a complete execution theorem. It releases
the per-input coefficient page, derives the halo row count from binary metadata,
retires the residual and original-input prefixes on port 110, and clears the
word-width header on 130. Its exact state preserves every other port except
owned headers 138--140. It returns the retained numerical bank and exposes the
next borrowed suffix in the native input-bank format. The continuation cost is
`packedRecoveryReleaseCost + packedInputAdvanceCost + 2*w+3`.
Recovery already disposes of the boundary mask; no second mask erasure is needed.

`packedHaloPreparedBoundary_exec` now composes actual RHS production with the
prepared boundary solve, including accuracy of its exact computed solution.
Its lifted endpoint constructs the interior principal-system solution and
provides fresh recovery workspace. `packedHaloPreparedRecovery_exec` composes
that prefix with recovery. `packedHaloPreparedInput_exec` then executes the
complete prepared program through per-input release, proves the actual final
halo error, returns the numerical bank, exposes the borrowed source suffix and
clears owned headers 130 and 138--140. Its cost is the shared prepared-input
ledger, including advancement/reset, with setup and final factor disposal
outside the call. Numerical matrix, coefficient-fit and input conditions remain
explicit hypotheses.

`PackedHaloBetweenInputs` now packages the returned bank, fixed headers,
restored native and temporary scratch, binary-length bound and blank private
workspace. Its next-input lemmas derive the producer's physical preconditions.
`packedHaloNextInput_exec` allocates a bounded zero output prefix above completed
outputs and executes a complete input while preserving this invariant and all
factor-page meanings. `packedHaloTwoInputs_exec` composes two actual calls over
one retained setup: second-call readiness is derived from the first call, both
halo error bounds are retained, the source advances twice, and the final output
contains both computed halos above its original borrowed suffix. No factory or
final factor disposal occurs inside those calls. The time bound includes both
output allocations and both complete prepared-input charges.

`PhaseCellPackedHaloBatchProgram` supplies one fixed counted program with its
counter isolated on port 248, outside the 248-port numerical bank. Its structural
list theorem consumes arbitrary input lists and retains a relational certificate
for every call, including its intermediate physical states. This permits earlier
output accuracy certificates to survive subsequent output prepending. The exact
control charge is `N*(perInput+3)+2`, including the empty batch.

`PhaseCellPackedHaloNumericalBatch.packedHaloNumericalBatch_exec` now instantiates
that theorem with `packedHaloNextInput_exec`, not a numerical execution callback.
An arbitrary list of RHS/exact-solution pairs supplies the numerical input bounds
and solve equations. The queue invariant contains the unconsumed encoded RHSs,
the between-input bank and the actual shared factor-page meanings. Each step
consumes one RHS and derives the next bank and factor meanings from execution.
The endpoint consumes the whole source prefix, retains a physical output/error
certificate for every input, restores the reusable bank, preserves the factor
pages and empties the loop counter. Its output archive grows by exactly
`N*(b-a)*w` symbols. This archive length is not a bound on intermediate live
storage. Initialization, final disposal and publication are outside this program.

`PhaseCellPackedBoundaryFactoryBetween.packedBoundaryFactoryGeometry_between_exec`
now derives the initial between-input invariant from the actual fresh-geometry
factory execution. Its column/stage certificate, table error and factor-page
meanings are outputs of the supplier theorem. The reusable workspace follows
from its returned solve readiness and native/high scratch restoration; retained
headers follow from the factory frame and canonical metadata generation. Only
initial scratch emptiness is assumed, with the six added recovery ports supplied
by a blank extension. The arbitrary source queue and publication buffer are
preserved. This bridge uses the fresh-geometry factory; it does not repair the separate
retained-geometry factory entry.

`PhaseCellPackedHaloInitializedBatch.packedHaloInitializedBatch_exec` now joins
that supplier to the arbitrary numerical batch in one executed program. A generic
embedding lemma preserves the external replica counter while setup runs. The
composed endpoint derives the common format from `boundaryHaloTarget_sizing`,
obtains all numerical columns/factors and initial readiness from the actual
factory, then runs the counted batch. Its bound charges setup once plus the
counted per-input costs. It consumes the source queue, retains all per-input
accuracy certificates and proves the exact output archive length above the
caller's original suffix. The initial counter is still supplied, and final
factor/table disposal and publication are not part of this program.

The executed one-input contracts now expose a structural frame for physical
ports 168--241 except solution port 238. The numerical batch composes this frame
in its queue invariant. The initialized batch therefore retains the actual raw
table and the factory's per-register factor stock, in addition to the three
numerical factor-page meanings. `packedBoundaryFactorStock_of_solution_frame`
transports that stock without rechecking concrete factor data.

`PhaseCellPackedHaloFinalRelease.packedHaloFinalRelease_between_exec` derives
release dimensions and blank scratch from the returned between-input invariant,
erases the raw table above its borrowed suffix, and clears the owned factor
registers using the retained stock bound. `PhaseCellPackedHaloClosedBatch` then
composes the actual factory, arbitrary counted numerical batch and final disposal.
Its execution theorem charges each shared setup/disposal once, restores the raw
table suffix, empties every owned factor register and the replica counter,
consumes the RHS queue and preserves the exact output archive length and all
per-input accuracy certificates. The endpoint now exposes an ordered list of actual numerical outputs,
with `List.Forall₂` relating each input to its halo error certificate. The physical
archive is exactly the reverse list of encoded halo blocks above the original
suffix; word order inside each block is preserved. The structural
`PackedHaloInputTrace.outputs` theorem proves this once for arbitrary result
relations. Its packed specialization removes archived suffixes from each error
statement using equality of the decoded words, with no representability premise.
Disposal preserves the actual output archive.

`PhaseCellPackedCoreAccuracy.packedCore_error` transports these decoded halo
certificates to any contained owned core with arbitrary publication suffixes.
`publishPackedCore_accurate_exec` joins that fact to the actual restoring packed
slice program: its exact destination prefix has the same error bound and the
cost traverses only halo padding and core words.

`PhaseCellPackedCoreArchiveStep` now composes that restoring crop with
`retireCountedLine`: it removes exactly the consumed halo, preserves borrowed
controls and restores every temporary. `PhaseCellPackedCoreArchiveLoop` iterates
this actual program with a structural consumed/remaining-list invariant. Its
endpoint consumes the entire halo prefix, exposes the original source suffix,
empties its loop counter and preserves every stack except source, destination
and counter. `PhaseCellPackedCoreArchiveAccuracy` instantiates it on the reversed
solver archive: prepending the extracted cores restores forward input order
without another reversal pass. `List.Forall₂` transports each halo's decoded
error to its corresponding published core. The charged time is
`N*(6*radius*w+10*coreLength*w+16+retireCountedLineCost haloLength w+3)+2`.
`PhaseCellPackedCoreArchiveControls` now generates the padding/core symbol
counts, halo row count and disposable replica counter from borrowed unary
radius/core/word-width/replica dimensions. It reuses unary products, constant
multiplication and copying; the charge is `(radius+coreLength)*(4*w+13)+4*N+20`.
`PhaseCellPackedCoreArchiveFromDimensions` composes this generator, the actual
accurate archive loop and erasure of its three retained slice controls. Its
endpoint restores all stacks except the consumed halo source and forward core
destination, preserves borrowed dimensions and carries `List.Forall₂` core
accuracy. Cleanup costs `2*(radius*w+coreLength*w+coreLength+2*radius)+7`.
This program checks near 2.12 GiB with default proof limits. The contract accepts
the exact reversed archive and error relation returned by the closed numerical
batch.

`PhaseCellPackedHaloPublishExec` provides the structural handoff: it embeds the
249-port closed solver into a 263-port bank, preserves the external publication
dimensions, derives the publisher's input archive and blank counter from the
executed solver, and runs generated publication plus control cleanup. Geometric
endpoint transport is proved here with arbitrary `q,w`; rewriting endpoints in
the expanded numerical format exhausted the default heartbeat budget. The
abstract transport and its numerical consumer each build in about 2.6 seconds
with unchanged limits.

`PhaseCellPackedHaloPublishedBatch.packedHaloPublishedBatch_exec` instantiates
this handoff with the actual closed factor/solve/dispose theorem. One program
now executes shared setup, arbitrary real replicas, final factor/table disposal,
control generation, forward core publication and control erasure. The original
halo archive suffix is restored on 132, the source queue advances on 110, the
raw-table suffix is restored on 220, owned factors and counter are empty, and
all external publication ports except destination 253 are restored. The exact
forward core stream and per-input `List.Forall₂` accuracy describe the actual
final destination. External ports 249--252 borrow radius, core length, replica
count and word width; no intermediate solver-state readiness is assumed.
`PhaseCellPackedHaloCountedPublishedBatch` now starts with the solver counter
blank and copies the retained replica count on 251 into 248 before setup.
The actual counter preparation costs `4*N+4`; the replica dimension remains
available for the generated publisher and the solver counter returns blank.

`PhaseCellPackedHaloGeneratedPublishedBatch` additionally reconstructs the
publication word-width header on 252 using the existing `generateWordWidth`
program. Its input precision on 119 is derived from the initial factory master's
contract and the two physical views, rather than supplied independently. The
identity `w=2*q+8` follows from the existing execution sizing definitions. The
program charges `8*q+9` for generation and `2*w+2` for final width erasure.
It starts with width 252 blank and restores it after ordered publication; all
other external publication controls/dimensions are restored as before. Both new
endpoints check below 3.25 GiB with unchanged proof limits.

`PhaseCellPackedHaloGeometryPublishedBatch` reuses the existing
`prepareCoreDimensions` program to derive unary radius/core-length masters from
an owned binary radius word on 252 and the retained binary halo length on 165.
The latter word is transported from the original factory-entry state through
both views. Regular-core geometry proves that its length is exactly
`coreLength+2*radius`, so both conversion bounds follow from the existing binary
coordinate bound; no independent unary dimensions are assumed. The radius word
is erased before port 252 is reused for generated publication word width. After
the complete solve/publish program, the two generated dimensions are also erased.
The additional charges are `prepareCoreDimensionsCost V haloLength radius`,
`2*V+2` for the owned binary word and `2*(radius+coreLength)+5` for the unary
dimensions. The endpoint checks near 3.27 GiB with unchanged limits. Replica
count 251 remains borrowed from the outer schedule. Port 252 is an owned input
and returns blank; all other external ports except destination 253 are restored.

Bulk-routing audit: `rawReplicaGather` scans the complete ambient replica batch
for one fixed origin. Its bill includes `12*((N+1)*s*w)` in the restoring gather,
in addition to copying/cleanup of the ambient batch. Calling it separately for
every complete halo key would repeat that scan once per key. Do not connect that
schedule to the selected S4 bound. The intended route is to gather equal-length
halos once per movement class and regroup their compact blocks across replicas
before executing the fixed-key numerical batches.

`PhaseCellReplicaKeyLayout` proves this regrouping structurally over arbitrary
replica/key/block dimensions and arbitrary payload symbols. The existing
`swapList 1 N 1 K W` permutation changes replica-major blocks into key-major
blocks, preserving both replica order and every symbol within a halo. Its block
identity identifies the output as one contiguous complete replica batch per key,
without merging distinct equal-length numerical keys.
`PhaseCellReplicaKeyInterchange` instantiates the already proved
`placedSwapProg_exec` tape machine on this layout, retaining its exact step
bound and spectator-register guarantees. It requires dyadic replica/key counts
with balanced exponents, a bit-encoding relation, canonical binary headers and
the existing private-bank conditions. `replicaKeyBitInterchange_exec` now derives its finite-array/encoding witness
internally for genuine bit planes, using a generic array-view lemma; no extra
encoding equality is needed from that caller. Padding nondyadic groups,
generating the interchange headers and establishing the selected routing bound
remain open.

Packed symbols have two bits, not an arbitrary alphabet-sized payload.
`PhaseCellPairBitPlanes.copyPairBitPlanes_exec` reuses restoring mapped copies
to emit their real and imaginary bit planes in order, preserving the source,
borrowed destination suffixes and scratch, in `12*N+12` steps.
`PhaseCellJoinBitPlanes.joinBitPlanes_exec` reuses mapped moves and the existing
counted `pairComponents` program to consume two equal-length routed bit planes
and reassemble pair symbols in order in at most `8*N+6` steps. Its reversal
passes cancel the pairing program's reverse accumulation. The symbol counter
is consumed and both temporary planes return blank.
`PhaseCellPairBitPlaneData` proves exact round-trip recovery for every actual
`cstream`, without a representability premise, and identifies both bit-plane
layouts with the corresponding replica/key bit arrays.

`PhaseCellReplicaKeyPlanes` composes two actual bit-plane interchanges sharing
one header/private bank. The second run's readiness follows from the first
run's frame and bit-format result. Its normalization volume is unchanged because
permuting the first plane preserves its length. No second-run execution or
readiness callback is supplied.

`PhaseCellPackedReplicaKeyRouter` now composes the complete codec and routing
lifecycle: restoring bit-plane encoding, both actual interchanges, erasure of
the preserved original pair payload and counted reassembly in key-major order.
Only the packed payload and disposable symbol counter change; the bit-plane
and codec scratch registers return to their initial blank values. Besides the
two interchange charges, the bound includes `12*V+12` for encoding, `2*V+2`
for disposal, `8*V+6` for reassembly, and normalization of the additional two
`V`-symbol planes. The router checks near 2.96 GiB, and its separate
`PhaseCellPackedReplicaKeyRouterCheck` audits the entire composition. The paired
layout and zip laws are structural over arbitrary symbolic dimensions. The
binary interchange headers, private-bank placement and balanced dyadic dimensions
are still initial conditions.

`PhaseCellCountedPackedReplicaKeyRouter` removes the supplied symbol-counter
assumption. It scans the actual owned pair payload once with `ucopy`, routes it
through the complete codec/interchange lifecycle and restores the initially
blank counter. The counter is outside the placed interchange bank, so the bank's
normalization volume is unchanged; preparation adds exactly `4*V+4` steps.
Only the payload changes in the resulting register file. The endpoint checks
near 2.94 GiB with default proof limits.

`PhaseCellReplicaKeyRoutingBill` names the actual counted-router bill used by
its execution theorem. Its structural normalization is
`2*(T+12*swapT t₀+5)*swapCost + 12*stock + 50*V + 4*T + 12*swapT t₀ + 54`,
where `V = 2^h*(2^d*W)` and `stock` is the initial placed-bank volume.
`PhaseCellReplicaKeyRoutingCost` applies the existing uniform interchange bound
to generated canonical header bits. Thus, for balanced exponents, the full
router costs a constant times `V*max(1,h,d)^tau`, with the explicit register
and normalization overhead above. Header generation/erasure is separate. This
bridge retains the balance hypotheses; it does not justify padding an arbitrary
rectangle up to a square. Unbalanced/nondyadic scheduling and simultaneous
peak-stock bounds still require proof. The expanded router axiom audit passes;
the guarded build peaks near 3.2 GiB.


`PhaseCellCanonicalUnaryHeader` reuses the existing halving-based `unaryBinary`
converter, adds the tape machine's separator and proves the emitted
`binBits (Nat.size n) n` have value `n` and are canonical, including zero. Its
structural binary-recursion lemmas identify the converter output with `Nat.bits`.
The program preserves the borrowed unary dimension and restores scratch in at
most `21*n+11` steps. This is one actual header-field generator, not a premise
asserting that some chosen bits are canonical. It checks near 1.93 GiB and has a
separate `PhaseCellReplicaKeyHeadersCheck` axiom audit. `PhaseCellCanonicalHeaderList` now composes field generation structurally over
an arbitrary destination-distinct list, with a summed execution bill and exact
frame. `PhaseCellReplicaKeyHeaders` instantiates it for all five interchange
fields, permitting the two constant-one fields to share a source. It preserves
borrowed unary dimensions and restores scratch, with cost at most
`21*(W+h+d+2)+56`. `PhaseCellGeneratedPackedReplicaKeyRouter` now composes all five generated
headers, the actual counted packed router and structural header erasure. It
starts with blank headers and derives values/canonicity from borrowed unary
dimensions; only the packed payload changes at the endpoint. Its bill charges
header generation, the router's actual intermediate bank volume (including
the generated headers), and erasure of all five actual header words. `PhaseCellBankVolume.bank_volume_of_frame`
now proves the bank increase exactly once for arbitrary distinct slots. The
executed endpoint uses `generatedPackedReplicaKeyRoutingCost`, measured from
the initial bank stock, rather than an intermediate register file. Its uniform
bound includes `14*replicaKeyHeaderVolume` (twelve normalization passes plus two
erasure passes), `21*(W+h+d+2)` for conversion, and the original compact-volume
interchange bound, with fixed overhead explicit. The expanded axiom audit
checks both this bound and the generic volume identity. It checks
near 2.94 GiB with default limits. This closes the generated-header lifecycle
for balanced dyadic routing. Padding nondyadic movement groups, proving the selected
routing/peak-stock bounds, and connecting the router to the generated gather and
numerical key batches remain open. The data module checks near 0.82 GiB and the execution module near
2.52 GiB. A separate `PhaseCellReplicaKeyInterchangeCheck` audits this supplier
without joining its import closure to the numerical coupling audit.

Replica tiling cost bridge: `PhaseCellSelectedSetupKeys` now exposes its
existing all-key polynomial bound `C*t^8*p^6` as a reusable theorem, and the
one-time whole-box bound consumes it. `PhaseCellTiledSetupKeys` separately
charges repeated setup per replica tile: eventually any capacity `B ≥ t^9`
pays all scaled selected-key setup costs for one tile, and
`ceil(N/B)*setup ≤ N+T`. The generic lemma only needs `setup ≤ B`; it pays
the final partial tile by one extra setup. This is an alternative ledger to
the once-per-key schedule, not permission to reuse its old multiplicity claim.
Padding the final tile adds at most one tile of traffic, and the selected
whole-box bound absorbs that additive overhead when the actual tile volume
is polynomial in one axis and precision.

A candidate executed schedule can choose tile capacity as a fixed power of
the padded regular-key count, split its replica address into equal-width
chunks, and move the key address past those chunks using balanced interchanges.
This avoids padding the whole tensor replica dimension to a square.
`PhaseCellReplicaChunkLayout` now proves this list schedule structurally:
`replicaKey_swap_factor` moves the key past the last replica chunk and then
the prefix, and `runReplicaChunkSwaps_words` iterates that factorization for
`K^c` replicas and `K` keys. The schedule has exactly `c` equal-width swaps,
positive prefix/suffix dimensions when `K,W` are positive, and summed stage
volume exactly `c*(K^c*K*W)`. It preserves the complete-key/replica/block
order of the existing router. No concrete permutation certificate is used;
the module checks near 0.92 GiB. This is a layout theorem, not execution of
the varying headers and machine stages.
`interchangeHeaders_exec` now generalizes the same structural five-field
generator to arbitrary prefix/middle/suffix dimensions; the previous
`replicaKeyHeaders_exec` is its `P=G=1` specialization.
`PhaseCellGeneratedChunkInterchange.generatedChunkInterchange_exec` executes
one actual equal-width stage with arbitrary positive prefix multiplicity and
suffix width. It generates canonical headers, invokes `placedSwapProg` and
erases the headers, changing only the bit payload. Its initial-state bill
includes exact header volume in bank normalization and erasure. The stage accepts the actual Boolean payload list and derives its finite-array
witness internally. `PhaseCellInterchangeBitData` proves exact bit-encoding
commutation despite the different machine/default Boolean symbols; the full
rectangle never reads a default. It also proves payload-length preservation.
`PhaseCellChunkInterchangeLoop.chunkInterchangeLoop_exec` now executes an
arbitrary structural list of these actual stages. Later calls receive their
bit format, length, blank header/private bank, scratch and spectator frames
from the preceding call; there are no stage execution/readiness callbacks.
The initial placed-bank stock is invariant, so the loop bill sums actual stage
costs measured against that same stock, plus one terminating step.
`chunkStageBits_words` identifies its result with complete-key order, and
`chunkStages_shape_ready` derives every stage's positivity/common-volume
premises once from the structural chunk schedule. Borrowed dimension masters
for all stages are still initial inputs: generating/allocating/erasing those
masters and connecting the loop to the packed codec remain open.
`PhaseCellUnaryPowerChain` now executes the reusable dimension-bank primitive:
from borrowed unary lengths `K,n`, a structural destination list receives
`n*K, n*K^2, ...`. Each product reuses `unaryProduct`; both borrowed masters
and scratch restore. The exact register-file result has a pointwise power
lemma and an off-bank frame. Generation costs
`4*generatedVolume + (9*K+4)*chainLength + 1`; for `K ≥ 1`, volume is at most
`chainLength*n*K^chainLength`. Structural `clearWords` cleanup restores the
initial bank and costs `2*generatedVolume+2*chainLength+1`. Prefix powers use
seed one; suffix widths use the borrowed word width. This supplies generation
and release primitives, not yet the wiring/allocation of the complete stage
master bank or its composition around the chunk loop. The primitive checks
at 1975.1 MiB; its narrow 3,970-job build and generation/release axiom audit pass.
`PhaseCellChunkDimensionBank` now composes two actual chains from the borrowed
one/width seeds, with exact combined frame and reverse-order release.
`chunkDimensionBank_lengths` includes the borrowed seeds as power zero.
`PhaseCellChunkStageWiring` reads the prefix column in reverse and the suffix
column forward, sharing one exponent master for both exchanged fields. Its
stage list has exactly the structural chunk schedule.
`wiredChunkStages_bank_values` derives all five fields of every stage from the
actual generated register file and the original one/width/exponent lengths;
there is no premise supplying any generated power. This establishes wiring
and paired bank generation/release.
`PhaseCellGeneratedChunkTile.generatedChunkTile_exec` now composes both
actual power-chain generators, the wired interchange loop, and reverse-order
bank erasure. It starts with blank generated dimension banks and only the
original base/one/width/exponent masters; all generated powers and later
stage readiness are derived. The endpoint replaces only the bit payload by
complete-key order. Generated dimension words are outside the placed bank,
so their allocation does not increase repeated machine-normalization volume.
The explicit bill includes both chains, every generated-header machine stage
and both bank releases, measured from the original placed-bank stock.
`unaryPowerChainR_update_off` and its paired-bank specialization transport
cleanup across the routed payload update, avoiding a second cleanup proof.
`PhaseCellChunkTileCost.generatedChunkTileCost_uniform` now bounds that
same executed bill uniformly. With `V=(2^d)^c*2^d*W`, it is at most
`C*(T+12*swapT t₀+5)*c*V*max(1,d)^tau` plus
`1000*(c+1)*(V+stock+T+swapT t₀+1)`. Here `stock` is the original
placed-bank volume and the two generated chains have length at most `c`.
The proof bounds actual canonical-header lengths by their dimension values,
bounds every stage's prefix/suffix/exponent by `V`, charges both complete
dimension-bank lifecycles linearly, and sums the existing equal-width
interchange bound by structural induction. No additional key-count factor
occurs. It uses the existing default proof limits and checks at 2952.2 MiB.
`PhaseCellGeneratedChunkPlanes` composes two actual generated tile routes,
reusing the restored dimension/header/private registers between planes. The
second route's readiness and unchanged placed-bank volume are derived from
the first route's exact frame and bit-format output. Its bill is twice the
same initial-stock tile bill.
`PhaseCellPackedRouterCodec` factors restoring encoding, old-payload disposal
and counted reassembly into one generic composition lemma, consumed by both
the original balanced packed router and the new tiled router. Concrete
production endpoints discharge its routing premise with actual programs;
neither exposes an execution callback. This removes the duplicated codec
proof. `PhaseCellPackedGeneratedChunkTile` now executes the full packed pair
tile lifecycle with `(2^d)^c` replicas and `2^d` keys. Its bill includes
`12*V+12` for encoding, twice the complete generated tile bill at initial
placed stock plus `2*V`, `2*V+2` for old-payload disposal and `8*V+6` for
reassembly. Only the packed payload and disposable symbol counter change;
all dimension banks, headers and codec scratch restore.
`PhaseCellCountedPayload` now factors counter allocation/disposal around an
actual counter-consuming body. Both the original balanced packed router and
`PhaseCellCountedPackedGeneratedChunkTile` instantiate it with their actual
router proofs; neither exposes a body-execution premise. The tiled endpoint
starts with an empty counter, counts its actual packed payload in `4*V+4`
steps, runs the complete packed tile and restores the counter. Only the
packed payload changes. The counter lies outside the placed bank and the
borrowed/generated dimension masters, so the original bank-stock bill is
unchanged. `countedPackedGeneratedChunkTileCost_uniform` keeps the routing
exponent and accounts for the extra restoring scan linearly.
Equal halo lengths do not alone establish one encoded word width: the packed
local numerical batch derives precision and width from the complete key's
boundary cardinality. Connecting uniform-width movement tiles to those
batches still needs an executed, priced format/precision handoff.
`PhaseCellOwnedPrefixPadding` now reuses the short-convolution padding
counter generator to prepend dummy symbols to an owned compact payload.
It generates the total exponent `(c+1)*d`, derives missing symbols from
the actual source length, emits the constant prefix and clears all generated
controls. The old payload is scanned restoratively and retains its order.
`PhaseCellPaddedReplicaTile.generatedReplicaTilePadding_exec` applies this
actual program to a short pair-encoded tile with `2^d` keys, padding its
replica count to `(2^d)^c` in at most `29*V+20` steps. Only the source
changes. The output supplies genuine padded bit-plane arrays internally,
and dropping the whole dummy-replica prefix mathematically recovers the
original payload. `PhaseCellTilePaddingData` proves these shape/order facts
structurally, with a generic finite-array view shared by the bit interchange
interface. No prepared padding counter or encoding certificate is supplied.
`PhaseCellPaddedCountedChunkTile` now composes actual padding with the
counted packed router. It reuses header scratch `a` as the temporary total
exponent, `count` as the missing-symbol counter, and the codec work tapes
during padding. The owned pair source is outside the placed interchange
bank, so padding leaves the original bank-stock bill unchanged. All padded
arrays and later readiness are derived from the executed producer. Only
the source changes at the endpoint, and a retained suffix identity records
the original real replicas in the padded replica-major view.
`paddedCountedChunkTileCost_uniform` adds only `29*V+20` to the complete
counted routing bill. This handles partial replica tiles when the key count
is `2^d`; it does not yet pad nondyadic key rows or execute removal of dummy
replicas after inverse routing. Nondyadic key padding, executed dummy removal,
selected key/capacity bounds, gather/numerical-batch integration and global
movement/stock ledgers remain open. The 8,220-job integration build and
padding, packed-routing and interchange axiom audits pass. Single-file
peaks are 2947.5 MiB for the padded router, 2973.0 MiB for its cost module,
1945.7 MiB for the generated padding program and 1931.2 MiB for its paired
producer contract. The pure padding data checks at 807.0 MiB and the shared
bit-array interface at 2513.4 MiB. All use unchanged default proof limits.
Still required: prove regular-key cardinality and tile-capacity bounds, execute
final-tile padding, match the packed factory bill to the
selected setup supplier, and handle small exceptional movement classes
separately. No arbitrary-rectangle execution or final resource bound follows
from these cost lemmas alone. Guarded single-file checks peak at 3261.0 MiB
for the tiled ledger and 3274.6 MiB for the refactored selected-key ledger;
the 15,121-job build and expanded core-setup axiom audit pass.

The outer generated schedule still must supply this binary radius word and the
replica count for a complete setup key. The existing generated core-group count
counts windows, not replicas, and cannot be substituted for that count. Full-line
seam publication, normalized complex and tensor/R4 composition, and the selected
time/live-stock ledgers remain open. The loop checks near 2.07 GiB
with default proof limits; broad contextual simplification was replaced by
direct register inequalities to stay within those limits.
The closed-batch endpoint checks near 3.24 GiB with default proof limits. This is a local
fixed-key lifecycle theorem; it does not provide a peak-live-stock bound or the
full generated S4 schedule.

Still required: generated geometry and replica-dimension handoff, outer
publication/coverage, setup-cost matching, peak storage, seams and tensor/R4
execution, with the selected global time and live-storage bounds. The original single-input solver still initializes and releases
factors per call. The retained-factory placement correction above also remains
open; the prepared body itself excludes that factory path.

### S4 implementation plan: close the packed execution boundary first

Scheduling clarification from the complete-key audit (2026-10-29):
`selectedCoreSetupKey_eq_iff` identifies complete production keys with endpoint
pairs when numerical parameters are fixed. `coreSetupGroup_eq_singleton` proves
that each non-full key contains exactly one generated core. Consequently the
factor-reuse loop must run input replicas (and both real components) at a fixed
halo before releasing its setup; advancing to the next regular halo changes
the key. Equal halo lengths justify shared movement, not shared factors.
The existing `selectedCoreSetupKeys_scaled_volume_le` pays setup over all
distinct keys, but does not yet bound the new packed executable's setup by that
supplier charge. Establish that cost bridge and a fixed-key repeated-call
contract before expanding the origin-advance loop. The existing
`sharedComplexClosedBatchCost_affine` and shared-page batch lifecycle are the
reuse templates; their ambient-sized loading still needs packed adaptation.
The current `packedHaloSolveUsing` constructs and releases factors per call,
including in retained-geometry mode, so it is not this reusable batch body.

The packed recovery endpoint now returns `BoundarySolveReady` for its actual
final factor bank. The structural `packedBoundaryFactorState_of_solution_frame`
allows the solution buffer 238 to change while preserving all factor roles
except the replaceable RHS. The existing solver consumes this returned
readiness for the final table-release dimensions. This establishes factor
readiness after recovery; native/header reset and the next packed input
producer's full contract are still needed for a repeated-input loop.
Recovery also returns `PackedBoundarySolveWorkspace` on that same output:
left tapes, native multiplier scratch, precision, and the high temporary bank
are ready again. A shared frame lemma derives this from recovery's actual
restoration facts. This does not reset the separate packed-input headers or
consume the retained residual/source buffers.
The actual `packedBoundaryRecovery` program now follows recovery with
`releasePackedRecoveryHeaders`, clearing private ports 242, 243, 244 and 247.
Its bound `2*(2*V+cellBound+w)+9`, where
`cellBound = (s/(t-s)+1)-2*band`, uses the actual generated loop
length bound and is included in `packedBoundaryRecoveryCost`. The solver
uses this composed program. The endpoint proves those ports empty and retains
the numerical workspace and factor readiness. The interior frame proves port
245 stays empty, and interior readiness proves port 246 is already empty.
Together with left-tape restoration, the composed recovery endpoint now proves
all six private ports 242--247 empty on both sides. No additional erasure cost
is needed for 245 or 246. Reset of the separate first-pass runtime remains open.
The first-pass `packedHaloInteriorCoefficients` now clears its selected-key
headers 125 and 128 after coefficient generation. The bound
`2*(V+cellBound)+5` comes from the actual interior execution and is included
in the existing first-pass cost. Structural view equalities preserve the coupling and native
banks, so the downstream numerical proof is reused. Word width 130 remains
available for coupling and output disposal; a complete next-input contract
still needs its later reset and the retained buffer lifecycle.
The empty-key facts now pass through the actual residual, boundary-data and
placement proofs into the boundary setup/solve scratch contract. They are
conclusions about the executed output, not additional next-call assumptions.
The generic key loop preserves any bound covering the initial unary header and
all its keys. Each executed key step proves its final unary length equals that
key; list induction then supplies the bound for the actual final tape.
Generated keys satisfy `cellBound`, and initialization supplies an empty unary
header. This removes the loose ambient `s` charge from both new cleanup bounds.
The existing `phaseGap_cellLength_le` bounds `cellBound` by `4*p+1` under the
numerical ABI's gap assumption. Other per-input costs and the complete batch
ledger remain to be connected; this refinement does not establish that ledger.

The proof should follow the manuscript construction recorded in
`plan/D-sharper-bound.md`, M7b: local principal solves, owned-core cropping,
shared factor pages, and bulk tensor exposure. The local source records core
length about `p^8` and halo radius about `p^3`; these are sizing targets, not yet
proved hypotheses for the selected machine. Keep geometry symbolic until the
cost and precision inequalities determine the concrete sizes.

The existing locality and generated-window results supply the mathematical
spine. The next work should connect one complete executed group before adding
more descriptor variants. In particular, a theorem assuming an efficient packed
solver or an R4 execution oracle is an intermediate lemma, not S4 acceptance.

| Order | Deliverable | Reuse and decisive acceptance check |
| --- | --- | --- |
| 1 | Packed halo input/output for S3 | Factor the current dispatcher's loading and storage interface from its arithmetic proof. Retain ambient coordinates for coefficients and cuts, but store only halo words. Prove agreement with the existing principal solve by restriction and index transport. An interval call must neither load nor return `s` words merely because its ambient period is `s`. |
| 2 | One executed generated group | Connect generated origin packets to `originAdvanceControls_exec`, then `orderedGather_exec`, the packed S3 call, and an ordered core publisher. Include count/header generation, width scaling, suffixes, empty groups, cleanup and step bounds. The theorem must return the same outputs that its accuracy theorem describes. |
| 3 | Complete schedule with actual setup reuse | Instantiate the generic group theorem for the at-most-two regular halo lengths and at-most-three full-system seam fallbacks. Length groups organize movement only. Partition arithmetic calls by the existing complete setup key; prove coverage, order and the number of setups rather than assuming all equal-length halos share factors. |
| 4 | Tensor accuracy and support | Feed the normalized complex one-axis result and its unit-ball guarantee into `TensorApproxD`/`TensorApproxV` and `ResamplingPermutedNumeric`. Use their additive composition, with no window-count or tensor-volume multiplier. Prove reserved-coordinate and suffix preservation for the actual executed schedule. |
| 5 | R4 fusion and final ledger | Execute the layout transitions, retaining the exposed representation across compatible axes. Restore the required layout at the phase boundary. Sum setup/solve/release and movement costs; bound simultaneous live storage; instantiate selected sizes and precision. Combine S2 and S3 at their existing supplier interfaces. |

Use only a few abstractions, each justified by a repeated proof obligation:

* **Packed interval view:** an origin, length, ambient coordinate embedding and
  a word-slice relation. Prove indexing, crop and restriction laws once. Never
  replace the ambient matrix by a new short-period matrix: that changes aliases
  and coefficients.
* **Ordered schedule:** descriptors with disjoint owned cores, covering all
  published coordinates, and ordered source intervals. Separate overlapping
  read halos from disjoint write ownership. Use list induction and existing
  window/gather lemmas, not one theorem per window.
* **Restored group execution:** one composition theorem parameterized by the
  solver's executed contract. Its invariant records the remaining descriptors,
  published prefix, borrowed suffix, retained setup and scratch state. Instantiate
  it with the real packed S3 theorem before declaring the group complete.
* **Complete setup-key equivalence:** reuse the production key and its equality
  laws. Movement classes and setup classes are distinct partitions; price any
  required reordering explicitly.
* **Cost and live-storage ledger:** add sequential time, take maxima of scratch
  peaks, and include retained factor pages and gathered buffers in every live
  state. Keep exact symbolic bounds until the final sizing theorem.

For fast implementation, first inspect every `chirpLine s` dependency in the S3
loader, arithmetic consumer and output publisher. Change the narrowest common
boundary that admits packed storage; preserve the existing full-line endpoint
as an instance. Do not duplicate the 303-register arithmetic proof. Generalize
the origin-to-controls preparation over an ordered origin list instead of
copying the halo-specific controller proof into another geometry-specific file.
If packed loading requires deeper arithmetic changes, resolve those before
expanding controller machinery.

Validate each abstraction with its first real consumer immediately. Use one
generic frame theorem for arbitrary untouched stacks and instantiate register
maps last. Keep arithmetic semantics and lightweight controller checks in
separate import closures. Check changed files with `check-lean-safe.py`, aiming
below 4 GiB, then build the affected endpoints with `build-lean-guarded.py`.
Use default proof limits and the existing axiom audit. Concrete finite checks
should concern small register maps only; prove schedule facts structurally.

S4 acceptance requires a concrete machine theorem combining execution,
normalized accuracy, tensor support, restoration, selected time and stock for
the same returned output. No unpaid ambient scans, externally supplied control
tapes, assumed setup counts or assumed R4 fusion may remain. S5/S6 obligations
stay explicit; completing a component does not change kappa.

### S4 local ribbon lifecycle checkpoint (2026-10-28)

`prepareMaskedGatheredRibbon_exec` generates the local word count from the
retained binary row count and unary bandwidth, constructs the masked spatial
source from a gathered raw ribbon, and releases its counter. It changes only
the source prefix on register 141. `releaseCouplingRibbon_exec` regenerates the
word and symbol counts, releases exactly that prefix and restores all scratch;
the borrowed suffix is arbitrary. Its bound is
`12*((N+2*band)*w) + 17*N + 26*band + 11*V + 24`.
The release specializes the existing generic prefix-release machinery rather
than adding another erasure loop.

These endpoints bracket `generatedRestoredPackedCouplingInterval_exec`, which
restores the ribbon, coefficient page and cursors after the interval arithmetic.
`gatheredCouplingInterval_exec` now composes all three into one actual caller.
Its exact postcondition changes only the consumed RHS prefix and the returned
reversed coupling results. The raw gathered ribbon, masked-source suffix,
coefficient page, row index and all temporary counters/scratch are restored.
Readiness supplies the low-bank and native scratch invariants; the caller does
not receive additional blank-bank certificates. Its step bound adds the three
proved execution costs. Binary geometry metadata, the gathered raw ribbon and
the retained interval coefficient page are still caller inputs.

Complete packed inverse integration and the full S4 schedule remain open. The
expanded `PhaseCellCouplingIntervalCheck` audits the composed caller and its
three endpoints as well as interval coefficient setup.

The local coupling feed now has an executed endpoint:
`feedPackedCouplingResult_exec` generates `N` from the retained binary header,
copies the reversed result into natural word order on register 110, releases
the reversed intermediate on 113 and restores all temporary counters. It reuses
`reverseWords_coeffs_exec` and `releaseFromDimensions_exec`, preserving bits
within each word and arbitrary source/destination suffixes. Its cost is at most
`28*N*w + 36*N + 11*V + 26`; the ambient-period header is preserved.
`gatheredFeedCouplingInterval_exec` composes it with the complete gathered
coupling lifecycle. The final state changes only RHS consumption on 93 and the
natural-order result prefix on 110, matching the next solver's source port.
The complete retained inverse must still adopt this local endpoint and replace
its other ambient-length loading/publication operations. The interval audit
includes both feed endpoints.

`CouplingIntervalMetadata` now gives the local feed caller one physical
binary geometry contract. A canonical value function describes ambient
sizes, bandwidth, cuts, origin, interval end, padded end and row count on the
existing ports. Its guard and ribbon projection lemmas instantiate the two
bank loaders, and the common geometric bounds prove every loaded value fits.
`gatheredFeedCouplingInterval_exec` consumes this contract directly: callers
no longer supply two arbitrary value maps, duplicated scalar equalities,
per-bank bounds, width proofs or a separate binary row-count equation.
This is an interface consolidation, not metadata generation; the physical
encoded words are still required and their production remains to be composed.

`completeCouplingIntervalMetadata_exec` now generates the derived binary
fields from the seven retained base fields (ambient sizes, bandwidth, cuts,
origin and row count). It computes doubled bandwidth, interval end, padded end
and encoded zero using the existing restoring binary primitives, in exactly
`36*V + 36` steps, with scratch restored. Its result proves
`CouplingIntervalMetadata` for the same physical state.
`completedGatheredFeedCouplingInterval_exec` composes that setup directly with
the gathered packed coupling/feed lifecycle. Derived metadata remains retained
in its postcondition; its setup cost is included. Base-field production, eventual
metadata release, coefficient-page setup/reuse and complete inverse integration
remain open. Neither this endpoint nor the earlier feed completes S4.

`binaryHeaderBank_exec` proves retained unary-to-binary conversion once over
an arbitrary assignment list, with distinct destinations and disjoint source and
destination banks. It restores every source and scratch register and sums the
actual conversion bills. `prepareSharedCouplingMetadata_exec` instantiates it
for the five shared geometry fields `s,t,band,a,b` from native retained headers.
Its exact frame changes only ports `145,146,147,149,151`, and its cost is at most
`(s+t+band+a+b)*(4*V+10) + 20*V + 41`. The generic conversion check peaks near
1.4 GiB; the actual shared geometry instantiation peaks near 2.1 GiB.
This setup belongs outside the local interval traversal. Dynamic origin and row
count must still be loaded from binary descriptor packets: regenerating unary
origins for every halo would introduce an unproved repeated ambient charge.
The grouped caller must compose this setup, descriptor loading, derived metadata
completion and eventual release, while proving the intended setup reuse.

`loadCouplingIntervalDescriptor_exec` now consumes two width-`V` binary
words (origin, row count) from port 159 into 155 and 165, preserving the packet
suffix and shared geometry. Its exact cost is `12*V+12`.
`releaseCouplingIntervalDescriptor_exec` clears all six dynamic metadata words
in `12*V+13` steps. `descriptorCouplingInterval_exec` composes loading, derived
metadata completion, gathered coupling/feed and release into a single interval
step. Its final frame changes only the descriptor suffix on 159, RHS suffix on
93 and natural-order result prefix on 110; all dynamic metadata ports are blank
again, while shared geometry and the coefficient page survive. The caller no
longer supplies binary origin/count words directly on working ports. Generated
packet-stream connection, shared setup scope, page setup/reuse, full packed
inverse, tensor execution and the selected resource bounds remain open.

`coreHaloPacketCode_do` reuses the existing halo selector and structural
descriptor enumeration to emit origin/length pairs for the analytic halos,
including the same full-system seam fallback. Its generated form computes the
core count from `s` and core width. `tablePacketHost_list_exec` generalizes the
existing one-field packet host to an arbitrary list; the original theorem is
now the singleton specialization with its unchanged cost and statement.
`generatedCoreHaloPacketHost_exec` places this host on the 168-register bank and
publishes actual binary packets to port 159, exactly the descriptor loader's
input port. Low table workspace is cleared and all external stacks/suffixes
are preserved. For `K = (s+width-1)/width`, its bill is at most
`(17*K+9)*tblC V V + (4*K+62)*V + 65`. The code and physical-host checks peak
near 1.9 and 2.0 GiB respectively. The initial table bank still requires executed
loading; grouping/filtering packets to match reusable arithmetic keys and the
full traversal remain open.

`preparedCoreHaloPackets_exec` closes the packet controller's initialized-bank
precondition. It reuses `chirpBankLoad_exec` with the shared binary ambient size
on 145, selected core width on 150 and halo radius on 152, plus the unary binary
width on 163. Unused table variables read an empty zero source on 154 and are
padded by the loader. Loading costs exactly `110*V+137`; packet generation and
complete table release follow in the same executed program. The exact final
state changes only the packet prefix on 159. All geometry inputs, borrowed
suffixes, native solver stacks and temporary table slots are restored. Its
single-file check peaks near 2.0 GiB. Producing the selected core/radius scalars,
matching movement groups to complete setup keys and executing the full grouped
solver still remain open.

`PhaseCellCoreSetupGroups` now partitions generated cores by their ambient
halo endpoint pairs. It proves coverage, unique group membership, no repeated
indices within a group and an exact additive ledger identity over the fibres.
Non-full endpoint keys contain at most one core; repeated full-system requests
share the full-system key. Every non-full arithmetic group lies in the matching
movement-length class, without identifying distinct arithmetic keys.
`Cost/PhaseCellCoreSetupKeys` maps the endpoints into the existing complete
`SelectedFamilyKey` with fixed `u` and target. Its key equality is exactly
endpoint equality, and the distinct generated setup family inherits the existing
scaled whole-box setup allowance. These are mathematical grouping and accounting
facts: executing each key once, routing its replicas and paying physical
reordering remain scheduler obligations.

`gatherPackedCellInputs_exec` supplies a bounded interior RHS gather on the
168-register bank. It generates the local row counter from binary port 165,
copies only the `N`-word packed halo, performs one ordered sweep through all
selected cell windows, and releases the copy, counter and owned controls.
Only the RHS prefix on 110 and consumed controls on 91 change; the original
packed source/suffix and ambient period header are preserved. For `K` windows
of length `L`, its bill is bounded by
`K*(14*L*w+27) + 32*N*w + 17*N + 11*V + 6*L*w + 9*L + 60`.
`packedInterval_eq_cellSourceRows` identifies these local slices with the
existing arithmetic input rows at the same ambient origins. The existing
advance controller already accepts a starting origin;
`packedGatherControls_eq` proves that starting it at the halo origin produces
the local controls directly from absolute-origin packets. Thus no packet
rewriting or separate local coordinate generator is required. Actual controller
initialization/composition and replacement of the complete interior caller's
ambient input/output bank contracts remain open. The bounded gather and its
bridges check at about 2.1 GiB with default proof limits.

`restoredLocalAdvanceControls_exec` now loads, runs and releases the existing
absolute-origin advance controller with the halo origin as its retained start.
Its bound is `K*(3*tblC V V+29*V+30)+8*N*w+78*V+91`, charging the local span
rather than the ambient starting offset. `placedLocalAdvanceControls_exec`
places binary width/origin/zero inputs on 153/155/154 and the width master on
163, preserving the gather's unary width on 94. It restores absolute-origin
packets, batch count, metadata and all table scratch.
`controlledPackedCellInputs_exec` composes this actual controller with the
bounded gather. Its exact postcondition changes only the gathered RHS prefix
on 110: the owned controls are generated and consumed within the call, not
supplied. Checks peak near 2.1 GiB. Encoded word-width/origin/zero metadata and
absolute-origin packets are still inputs; their surrounding setup must be
joined to the complete local interior solver before S4 acceptance.

`preparedPackedCellInputs_exec` generates the binary width field on 153 from
the retained unary width and releases it after the controlled gather, adding
`w*(4*V+10)+6*V+10` steps. `rawPackedCellInputs_exec` also generates and releases
the unary width from the ordinary fraction header on 112, adding `8*q+2*w+11`
steps. The final frame changes only the gathered RHS prefix on 110; both width
representations and all temporary controls are gone before arithmetic.
`packedCellRows_eq_sourceRows` and `packedCellOrigin_packets` identify the
resulting cell rows and retained absolute origins with the unchanged closed
batch arithmetic interface. The bridges are structural list reindexing proofs;
no new scalar arithmetic implementation or short-period matrix is introduced.
All three modules check near 2.1 GiB. The actual closed-batch execution still
needs to be composed with this input frame, followed by packed publication,
complete local inverse composition and grouped resource accounting.

`packedCellInputBank_exec` now proves the exact native-bank handoff from the
executed local gather to `batchInputBank`. Blank native registers follow from
the supplied bank itself, and the retained absolute-origin packets match its
existing origin format. `packedCellBatch_sized_exec` composes that preparation
with the unchanged `closedBatch_sized_exec` through the injective register
embedding. Its execution returns the actual `releasedCellBank`, compact cell
outputs and the existing per-cell `CellRun.Valid` certificates for those same
outputs; the input preparation and complete arithmetic setup/run/release costs
are summed. All stacks outside the native 117-register bank are preserved.
Both new endpoints check near 2.1 GiB. This establishes an executed packed cell
batch, not the complete local inverse: cell geometry/global accuracy,
local publication, retained setup reuse across replicas and full inverse/tensor
composition still need to be joined.

`cachedPackedCellBatch_spec` now connects local packed gathering to the
existing `cachedBatchFromOrigins_spec` numerical supplier. The actual cached
call preserves the origin-dependent weight page on 117, its count and cache
scratch, and all external metadata. The same physical returned output has the
existing per-coordinate/core error `2^-target`, bounded encoded-stream length
and exact native cleanup. Preparation and cached arithmetic bills are both
charged. This uses the original ambient matrix and explicit cell geometry
hypotheses; the geometry still needs instantiation for the generated cells.
The retained page is a weight cache, not a claim that every inverse factor is
cached. Its generation/release, remaining factor setup reuse across replicas,
packed publication and complete grouped inverse composition remain open.
The cached numerical endpoint checks near 2.1 GiB with default proof limits.

`packedCellScatter_exec` publishes arbitrary disjoint local cell windows
with exact source/output suffix restoration in at most `35*N*w+6` steps.
`packedCellScatter_word` identifies each published word with the corresponding
compact arithmetic word. `packedCellPublish_exec` generates its window counter
from the existing protected dimensions and releases that counter and the owned
publication controls. Its bound is `54*N*w+15`; it changes only the consumed
solution prefix, local output and released controls. Both proofs reuse the
existing scatter machine and structural window lemmas. They check near 2.0 GiB.
Publication controls and the local destination buffer are still caller inputs;
their generation and composition with the executed cached cell batch remain
open, as do the complete local inverse and S4/R4 execution/ledger gates.

`packedCellPublicationControls_exec` now derives arbitrary disjoint local
publication gaps from the existing gather-advance stream, preserving that stream,
its borrowed suffix and the batch count. It reuses `publicationControls_exec`
and the structural advance/window identities, with bound
`12*N*w+21*K+21`. `packedCellPublicationFromDimensions_exec` generates the
window counter from native cell length 102 and word width 94, puts controls on
protected register 140 and releases all temporary counters. Its accumulator is
95, disjoint from the live width, and its full bound is
`12*N*w+21*K+6*L*w+9*L+27`. Both check near 2.1 GiB; the combined execution
axiom audit passes. The generated controls must still be inserted before input
gather consumes its advances, retained through arithmetic and joined to the
publisher. Local destination allocation, complete halo inverse composition and
the grouped/tensor/R4 resource gates remain open.

`publishingPackedCellBatchPublish_sized_exec` now closes the executed interior
cell gather–solve–publish chain. The origin packet controller runs once; its
advance stream supplies both protected publication controls and the local RHS
sweep. Unary/binary word widths and all temporary gather controls are generated
and released. `publishingPackedCellInputBank_exec` identifies the resulting
native bank with the unchanged arithmetic input contract. The closed arithmetic
batch runs under its existing proof and preserves the publication controls
outside its bank. Finally the packed publisher consumes the actual compact
solution words and writes exactly their local scatter into register 132,
restoring the solution suffix and clearing publication controls. The same
execution retains per-cell `CellRun.Valid` certificates for those words.

The ledger is the existing `packedCellGroupInputCost` plus
`12*N*w+21*K+6*L*w+9*L+27` for publication-control preparation, the existing
`sizedClosedBatchCost`, and `54*N*w+15` for publication. Each new module checks
between 2.0 and 2.1 GiB, and the combined execution/axiom audit passes. The local
destination buffer and protected dimensions 128/130 are still caller inputs;
the selected cell geometry must still be instantiated. This is an interior cell
batch, not the complete halo inverse: boundary solve, residual/recovery
composition, retained factor reuse across replicas, grouped traversal, tensor
support/error, fused R4 layouts and final time/live-stock gates remain open.

`PackedCellOutputSpec` now states accuracy directly on the local destination
buffer, keeping local storage offsets separate from original ambient cell
geometry. `packedCellScatter_word_append` proves that a borrowed destination
suffix cannot affect an owned cell word. `packedPublishedCell_accuracy` reuses
`publishedCell_accuracy` to transport the existing requested error to that word,
without a cell-count multiplier. The actual
`publishingPackedCellBatchPublish_sized_exec` endpoint now returns this contract
for its physical register 132, alongside execution and the exact scatter state.

`preparePackedCellDestination_exec` generates retained dimensions 128/130 from
the native cell length and precision, decodes only the local length, copies the
local input prefix once into 132 and releases its counter. Its cost is
`16*N*w+17*N+11*V+8*q+4*L+37` for `w=2*q+8`.
`generatedPackedCellBatchPublish_sized_exec` composes that prelude with the
complete interior cell gather–solve–publish chain. The destination payload and
protected dimensions are no longer supplied; an arbitrary initial 132 tail is
preserved. The native arithmetic bank, binary local geometry and origin packets
remain inputs, and the returned local buffer has `PackedCellOutputSpec`.
These modules check near 2.0–2.1 GiB and the combined axiom audit passes. The
owned RHS prefix retained by the arithmetic bank has not been erased by this
publisher. Instantiating cell geometry and composing boundary solve,
residual/coupling/recovery, group reuse, tensor/R4 execution and the final ledgers
remain necessary for S4 acceptance.

The executed cell endpoints now expose their state for subsequent phases.
`publishingPackedCellBatch_sized_exec` preserves every external left stack,
including the publication-control port. After publication,
`publishingPackedCellBatchPublish_sized_exec` returns the exact native
`releasedCellBank` with the solution suffix restored and the gathered RHS plus
borrowed local source retained. Every external stack except destination 132 is
restored, including the initially blank publication controls. The generated
caller transports that native contract, preserves all external stacks except
its retained dimensions 128/130 and destination 132, and identifies both retained
dimension words exactly. No arithmetic proof is reopened for these frame laws.

`packedCellGaps_scale` and `packedCellScatter_cstream` specialize the existing
structural encoding/scatter laws. The generated endpoint now identifies its
physical destination as the encoding of a scatter on Gaussian words, followed
by its original suffix. Its numerical contract and this word-list contract
concern the same returned buffer. Updated modules check near 2.1 GiB and the
combined axiom audit passes. The next concrete payload boundary is coupling:
`gatherCouplingRibbons_exec` still takes an ambient `cyclicPaddedLine`; the local
halo route needs a padded local result ribbon with the existing halo mask,
then composition with the retained-page interval and boundary/recovery stages.
Full halo inverse, setup reuse/group traversal, tensor/R4 and final ledger gates
remain open.

`localFeedCouplingInterval_exec` now executes coupling directly from a packed
local result on register 132. The local-length decoder runs once; structural
`zeroPadLocalPrefix_exec` copies the local payload between generated zero bands
and restores its source. The existing mask producer runs on that payload,
retained spatial arithmetic consumes the masked ribbon, and both unmasked and
masked ribbons are released. The existing result feeder reverses the returned
rows into natural order and releases its intermediate. The final state changes
only consumed RHS 93 and the natural-order result prefix on 110; the source
result, raw-ribbon suffix, coefficient page and shared metadata are restored.
All stages, including padding, count generation and release, are charged.

The mathematical bridge is `maskedLine_localCouplingRibbon`. It keeps the
original ambient matrix and requires `origin=a`, `b=a+N` and `N+band≤s`.
`localRibbon_active_index` proves symbolically that an active cyclic stencil
coordinate lies in the unwrapped local payload under that separation condition.
The periodic/seam branch still needs its existing cyclic-padding route and an
executed branch selection; this local lemma does not cover it.
`buildMaskedGatheredRibbon_data_exec` factors the shared execution proof over
payload lists and their masked result, and the existing raw-ribbon theorem is
its specialization. The local caller uses the same actual mask/arithmetic
machines rather than assuming a mask or coupling execution oracle.

The padding constructor costs `16*N*w+21*N+14*band*w+13*band+11*V+46`;
its temporary unmasked ribbon release costs at most
`12*((N+2*band)*w)+11*(N+2*band)+14`. Mask generation, retained interval
arithmetic, masked-ribbon release and feeding retain their explicit existing
bills. New single-file checks peak between 1.9 and 2.2 GiB. The local result's
Gaussian-word scatter still needs to be identified with the packed ambient
field used by this coupling contract. Coefficient-page/shared-header generation,
boundary solve and recovery composition, actual setup reuse/group traversal,
tensor/R4 execution and selected time/live-stock gates remain open.

`packedField` supplies the semantic ambient view of a local Gaussian-word
list, with zero outside its advertised interval. `packedInterval_packedField`
recovers exactly that list when the interval fits; `packedField_property`
transfers word bounds structurally, including the exterior zero.
`packedField_read` identifies represented field values with the local tape
reader without constructing an ambient tape.

`generatedPackedCellBatchPublish_sized_exec` now constructs this field for the
actual Gaussian-word scatter, proves that it still has local length `N`, and
returns register 132 as `cstream (packedInterval origin N D)` plus the original
suffix. `publishedOutputWords_norm`, the original RHS bound and
`scatterRows_mem` give the global bound
`‖value q (D k)‖ ≤ 2^interiorOutputExponent`; the existing width theorem then
proves every `D k` fits its physical word. The native bank/frame and executed
accuracy guarantees remain part of this same endpoint.

`packedCellOutputSpec_field_at` transports the actual buffer's numerical
contract to `value q (D (lo n+i))` using one shared local/ambient coordinate-read
lemma. `couplingInputWords_property` factors the masked-input property proof;
its representability specialization lets `localFeedCouplingInterval_exec`
consume the field-level `Fits` fact directly, instead of separate per-row
operand-fit hypotheses. These close the local-result payload and
representability boundary. Single-file checks peak near 2.0–2.1 GiB and the
combined execution/axiom audit passes. Coupling scalar/header installation, actual stage
composition, complete cell geometry/group traversal, seam dispatch,
boundary/recovery, retained setup reuse, tensor/R4 and final resource gates
remain open.

`preparedSharedLocalFeedCouplingInterval_exec` now joins actual scalar-counter
setup to local coupling and counter release. A static injective register view
reads the retained master headers (117/119/121–124/141–142 and width 130), while
the released native bank supplies private arithmetic space. The existing
coupling execution theorem is transported through this view with no added
machine steps. `sharedCouplingHeaders_ready` derives its ordinary readiness
from the actual `releasedCellBank`, master-header lengths and their empty left
stacks. This avoids reinstalling ambient `s` and `t` unary copies for each
coupling call; retained masters still need their one-time construction at the
appropriate shared setup boundary.

`sharedCouplingCounters_exec` executes the existing counter producer through
that same view. Its cost is `prepareCost q w+6*q+4*band+10`; final counter release
costs `2*(w+q+topN w)+7`. The complete prepared coupling theorem restores every
stack except consumed RHS 93 and the natural-order result prefix on 110, so it
requires no supplied multiplication counters. The register map is a small flat
involution; composing nested equivalence values caused elaboration blowup and
was replaced by this simpler function and injectivity proof, with default proof
limits unchanged.

The local interval row-loop proof also no longer requires an initial unary
index of length `origin`. Its only use was an unused intermediate fact; actual
row semantics already come from binary guards and the retained coefficient
page. The generic loop and restoration wrappers now accept any initial index
tail, increment it structurally and restore it exactly. Consequently the local
and shared local callers can start with the empty 107 stack returned by the
cell stage. Legacy outer wrappers retain their stronger interface where needed.
The prepared shared endpoint checks near 2.1 GiB and the combined execution/
axiom audit passes.

The next concrete composition must generate/preserve the local RHS prefix for
residual coupling, construct the retained page/row-width frame, and join the
cell result, this prepared coupling call, boundary solve and recovery. Shared
master generation and factor reuse must be placed in the actual group schedule.
Seam selection, complete geometry, tensor/R4 and final time/live-stock gates
remain open; this endpoint does not complete the halo inverse.

`residualReadyPackedCellBatch_sized_exec` now composes a paid local RHS
preservation pass, the executed cell gather–solve–publish chain, and regeneration
of the retained page's `2*band+1` row-width header. The returned 93 stack contains
the original local RHS prefix plus its original suffix; 132 contains the bounded
packed ambient result field; 140 contains the row-width header. The same state
has the exact released native-bank contract and `CouplingReady` through the
shared master view. Master facts are transported through the actual frame
instead of reinstalling ordinary headers. Cell output accuracy and integer-word
bounds describe this same execution.

`preservePackedRhs_exec` copies only `N*w` source symbols and restores every
scratch stack, at cost `16*N*w+17*N+11*V+8*q+2*w+36`. The row-width regeneration
costs `4*band+5` and preserves the shared band master. Both calls reuse the
existing unary/header and counted-prefix machines. The combined endpoint checks
near 2.1 GiB and the combined execution/axiom audit passes. Retained master construction, coefficient-page content/count and
binary geometry remain shared-setup obligations. Only the advertised equal-
length cell windows receive this batch's accuracy guarantee; complete halo
interior coverage still requires the actual length-key traversal. The composed residual endpoint below feeds the preserved RHS, result field,
row-width frame and readiness into prepared shared local coupling. Boundary/recovery,
seam dispatch, group reuse, tensor/R4 and final resource gates remain open.

`packedCellResidual_sized_exec` now executes the packed cell stage followed
by prepared shared local residual coupling (`boundary=false`). The published
bounded field, saved original RHS, regenerated row-width frame and readiness
are supplied by the same preceding execution. Shared metadata and retained page
facts are transported through its frame; coefficient-word representability and
realness follow from the existing selected coefficient bounds and executed word
width, rather than per-row supplied fit hypotheses.

The returned 110 tape is the natural-order encoded guarded residual interval,
then the retained gathered-cell RHS and original local source/suffix. The saved
RHS copy on 93 has been consumed back to its original suffix. The theorem also
returns the exact released native bank, preserves the result field on 132 and
all shared page/master/metadata stacks, and retains the physical cell accuracy
contract. `residualReadyPackedCellBatchCost` and
`preparedSharedLocalFeedCouplingIntervalCost` name the two ledgers; the combined
bound is their sum. The endpoint checks near 2.1 GiB and the combined axiom audit
passes with default proof limits.

This composition assumes the retained coefficient page and canonical binary
geometry from shared setup, and keeps `N+band≤s` explicit. Complete interior
coverage across actual length groups must still be instantiated before claiming
a halo-wide numerical residual bound. The next payload boundary is ordered
boundary RHS extraction/folding from this local residual prefix, followed by the
executed boundary solve and recovery. Shared setup/factor reuse, seam dispatch,
complete group traversal, tensor/R4 and final resource gates remain open.

`PhaseCellPackedBoundarySelection` now proves that a supported boundary can be
selected directly from a packed interval without changing `bOrder` or
`bFoldOrder`. A generic filter/crop lemma removes only unselected prefixes and
suffixes; no geometry cases or finite certificates are needed.
`packedBoundaryRhsOrderedGather_exec` instantiates the existing masked gather
with local length `N`, costs at most `N*(16*w+10)+16`, and restores the source,
mask and scratch while prepending the ordered boundary values. The existing
boundary fold therefore applies unchanged. The module checks near 2.1 GiB.
This endpoint still assumes the supplied membership mask: generating that mask
from shared binary geometry and composing extraction with the actual residual,
boundary solve and recovery remain open.

`generatedPackedBoundaryRhs_exec` now composes local geometry-mask generation
with packed boundary extraction. `couplingSourceIntervalMaskCode` reuses the
existing membership row under the interval table loop, at `29*N+2` table steps.
The host publishes one pair symbol per local coordinate and releases the table
bank. `packedBoundaryRhsMask_flags` identifies its real-bit flags with the packed
boundary selector. The composed 117-stack program reads the packed source on
110, retains its generated mask on 109 for reuse, and prepends ordered boundary
RHS words on 93, preserving source, width, input/output and left stacks while
releasing table registers 0–31. Its cost includes the table interpreter and the
local gather; it assumes a loaded table bank, binary word bounds, and boundary
containment in the packed interval. Connecting that loaded bank and placement
to shared residual metadata, then executing fold/solve/recovery, remains open.
The composed endpoint checks near 2.1 GiB with default proof limits.

`metadataPackedBoundaryRhs_exec` now generates the boundary mask and extracts
ordered boundary RHS words directly from `CouplingIntervalMetadata`, with no
supplied table-bank interpretation or mask. The shared structural
`binaryIntervalStreamHost_exec` loads retained binary words, runs any interval
table program and restores every stack except its emitted stream. Boundary mask
generation specializes it, then embeds into 168 stacks with mask output 167.
Its placement reads the boundary width from canonical port 147 (`band`), rather
than recovery's port 148 (`2*band`). The composed extractor reads packed residual
110 using retained width 130, emits ordered values on 93, retains its mask on
167, and restores all other stacks exactly. Its explicit cost includes binary
loading, table execution/release and the local gather. It checks near 2.1 GiB.
The source interval, boundary containment, blank table workspace and blank mask
port remain hypotheses to discharge from the preceding residual execution;
fold/solve/recovery, complete coverage and the final S4 gates remain open.

`packedCellBoundaryRhs_sized_exec` now composes the actual packed cell stage,
residual coupling, metadata-driven mask generation and boundary extraction.
No new containment or workspace assumptions are imposed: boundary containment
follows from `haloBoundary` being a subset of the halo interval; blank table
stacks follow from the returned released native bank; mask port 167 and binary
geometry follow from the high-register frame; width 130 follows from generated
cell dimensions. The theorem identifies selected guarded rows with ordinary
`couplingRowField` residual rows on the boundary using the existing guard
soundness theorem. The resulting ordered boundary RHS is on 93 above its
original suffix, the reusable mask is on 167, the packed residual remains on
110 and the cell field/accuracy contract remain on 132. All other shared
registers retain their earlier frame. `metadataPackedBoundaryRhsCost` names the
additional fully paid local extraction ledger. The endpoint checks near
2.2 GiB with default proof limits. Boundary fold/solve/recovery, complete halo
coverage and group traversal, shared coefficient/factor setup, seam dispatch,
tensor/R4 and final resource gates remain open.

`Host.countSelectors_exec` supplies a reusable structural counter over an
arbitrary selector tape and Bool predicate. Its scan restores the tape, prepends
one unary tick per selected symbol and preserves all other stacks, at cost at
most `7*length+4`. `packedBoundaryFlags_count` uses the filter/crop support lemma
to identify the packed flag count with the actual boundary cardinality;
`packedBoundaryMask_count` transports this through the generated pair-symbol
format. `packedBoundaryCount_exec` therefore produces the fold count on 116
from retained mask 167, using only scratch 0 and restoring both mask and scratch,
at cost `7*N+4`. This removes the need to supply a boundary count as external
data. The counter builds near 2.0 GiB and its boundary specialization checks near
2.1 GiB. Its count still needs composing with the existing fold counter
generator and prefix isolation: the current extracted RHS on 93 retains its
borrowed suffix, whereas the existing physical fold expects an isolated line.
The final inverse and S4 acceptance gates remain open.

`preparePackedBoundaryFold_exec` now composes mask-derived counting, natural-
order prefix isolation and the existing fold counter generator. The generic
`moveCountedLine_exec` reuses counted transfer and reversal, moves only the
owned prefix in natural order, leaves an arbitrary borrowed source suffix and
restores every clock/reversal scratch stack. Its cost is `n*(12*w+9)+12`.
`packedBoundaryFoldCounters_exec` uses a flat injective placement of the unchanged
117-stack counter generator, reading retained width 130. Together they leave
the borrowed suffix on 93, isolate the ordered RHS on 143, produce boundary
count 116 and controls 0 (floor half-count), 2 (parity) and 3 (first-half bytes),
and preserve all other stacks, including both left banks and the reusable mask.
`preparePackedBoundaryFoldCost` sums mask scan, prefix move and counter setup.
The composed endpoint checks near 2.1 GiB. It still needs joining to the preceding
cell-to-boundary execution and to the actual fold; the existing numerical fold's
global empty-left-bank premise must be localized or framed to preserve retained
master stacks. No new boundary solve, recovery or S4 acceptance claim is made.

`closedPackedBoundaryRhsFold_exec` now executes the complete packed numerical
RHS fold. It derives the boundary count from mask 167, isolates the ordered
prefix from 93, generates the existing fold controls, runs the unchanged fold,
publishes solver-order words on 143 and releases every temporary control.
Only count 116, source 93 (now its original borrowed suffix) and result 143
change; the mask, width, metadata, cell field and every left stack are preserved.
Its paid cost is `preparePackedBoundaryFoldCost N n w+70*(n+1)*(w+1)+71`.
The endpoint checks near 2.2 GiB with default limits.

The supporting `Host.StackFrame` proves a structural frame rule for call-free
programs: stacks outside a declared footprint may be replaced arbitrarily while
preserving the exact local state and step count. The fold's footprint contains
no left stack. `framedBoundaryRhsFold_exec` therefore reuses the existing fold
proof with arbitrary left-bank contents; no retained-master emptiness premise
is needed. `packedBoundaryRhsFold_exec` embeds this unchanged execution using a
flat width placement (94 ↔ 130), preserving all spectators. Joining the closed
fold to the cell-to-boundary endpoint and the boundary solver remains open,
along with recovery and the full S4 coverage/setup/seam/tensor/resource gates.

`packedCellFoldedBoundaryRhs_sized_exec` now joins the closed numerical fold to
the actual cell-to-boundary machine. It introduces no new workspace or
cardinality hypotheses. Empty low stacks and initial count 116 follow from the
returned native released bank, destination 143 follows from the shared high
frame and initial freshness, and boundary containment follows from halo
membership. The same execution now leaves ordinary residual rows in canonical
`bFoldOrder` on 143, their generated cardinality on 116, the original borrowed
suffix on 93, the reusable mask on 167, the residual interval on 110 and the cell
field/accuracy contract on 132. `countedReleasedCellBank` records the exact
native projection with the newly owned boundary count. Every other retained
master/page has its prior frame; the ledger adds `closedPackedBoundaryRhsFoldCost`.
The endpoint checks near 2.2 GiB with default limits.

The next numerical handoff is the existing normalized/unscaled prepared boundary
solve, not an unnormalized triangular pass: its RHS magnitude and working
precision contracts must be established for the actual selected residual.
Complete interior coverage/stability, compatible shared factor setup and
physical RHS handoff remain open before claiming that solve composition.
Recovery, group traversal/reuse, seam dispatch, tensor/R4 and final S4 resource
gates also remain open.

`haloCellInterval_spec` now derives the interval solver's full geometric
contract from membership in the generated positive clipped phase cells:
positive length, ambient fit, selected interior membership, unchanged phase and
maximality. It reuses `haloInterior_phase_iff` and does not split into endpoint
or seam cases. `packedHaloCell_error` instantiates the actual packed output
contract with this generated geometry. `haloInterior_error_of_cells` then uses
`haloCells_cover` to assemble pointwise cell errors into the same uniform halo
interior error; there is no multiplier for the number of cells.
`haloInterior_stable_norm_of_cells` reuses the existing diagonal-dominance
stability lemma to obtain the precision-independent real-output bound.

`haloResidual_normalization_bound_of_cells` connects these facts to the existing
boundary normalization budget. For the real projection of the ordinary computed
residual, the stable interior bound and existing coefficient/count bounds imply
both the normalization kernel's `2^(q/2)` component bounds and the normalized
solver input's half-unit component bounds. The theorem keeps complete per-cell
accuracy and compatibility with the boundary working precision explicit. Those
conditions still need instantiating across the actual executed length groups;
this is not a claim that the current single equal-length batch covers the halo.
Physical real projection/RHS transfer, shared factor preparation and the executed
normalized/unscaled boundary solve also remain open. The normalization bridge
checks near 3.1 GiB with default proof limits; full S4 acceptance is still open.

`haloPackedOffsets` now expresses each generated clipped length group as
local offsets from the halo origin. Fit, ordered disjointness and ambient-origin
identity reuse the existing halo gather/scatter schedule. `packedHaloGroups_cover`
transports the generated key/group coverage to the exact finite batch indices
and local cell coordinates accepted by packed execution. Distinct length groups
have disjoint windows; `haloGroup_scatter_preserves` uses the generic scatter
outside-window theorem to preserve every coordinate of a different group.
There are no new endpoint cases or finite certificates.

`haloInterior_error_of_packed_outputs` now derives complete halo interior error
from the per-group `PackedCellOutputSpec` contracts on one final packed buffer,
using common working precision and exact generated offsets. The corresponding
stable-norm theorem feeds the existing residual normalization language without
an error factor for the number of keys or cells. These results still require
the runtime traversal to establish and preserve all per-group contracts on that
same final buffer; the present single-group execution does not itself establish
that family. The new scatter preservation lemma supplies the cross-group
publication invariant needed for this traversal. The geometry bridge
`haloCellInterval_spec` was reduced to a specialization of the pre-existing
`halo_solver_geometry`, removing its duplicated proof. The packed group and
accuracy modules check near 2.1 GiB. Runtime group traversal, shared setup/reuse,
precision handoff, boundary solve/recovery and the final S4 gates remain open.

`reusablePackedCellBatchPublish_sized_exec` now publishes into an existing
caller-owned packed destination and restores the original local source for a
subsequent length group. It retains the actual batch count on owned stack 129
before the unchanged gather/solve/publish chain consumes its native controls.
The generic `retireProductLine_exec` then derives the total record count from
retained batch size and cell length, removes only the owned gathered-cell RHS
prefix on 110, and restores all product/count/trash scratch. Stack 129 is also
retired. The final native projection is `releasedCellBank [] borrowed outTail`;
the high-register frame restores everything except the published destination
132, and the new cell's accuracy/validity contracts are preserved. No new
destination buffer is allocated. `reusablePackedCellBatchPublishCost` includes
count retention, the full original stage setup/publication cost, source-prefix
retirement and count cleanup. The endpoint checks near 2.2 GiB.

The runtime group traversal still needs to reinstall each next group's native
input headers and retune its retained cell-length dimension, while transporting
previous groups' accuracy through disjoint publication. This stage deliberately
pays the existing full arithmetic setup; shared factor/setup reuse is not yet
claimed. Complete traversal, normalization/solve/recovery and the final S4 gates
remain open.

`retunedPackedCellBatchPublish_sized_exec` removes the requirement that retained
publication dimension 128 already equal the next group's length. The generic
`replaceUnary_exec` clears an owned unary destination, copies a retained source
and restores its temporary stack. Applied to native cell-length header 102, it
sets 128 to the new `L`, at exact cost `2*oldLength+4*L+6`, and then runs the
verified reusable publisher. Width 130 and destination 132 are reused; the local
source is restored for the next group, and the new length and cell accuracy
contract are returned. Apart from dimension 128 and output 132, the previous
high-register frame is retained. The endpoint checks near 2.2 GiB.

The next group's native input bank is still a precondition. The existing
retained-header copier and generated halo class/origin controls supply the
patterns for reconstructing it, but their placement, packet-width compatibility,
shared setup costs and complete runtime key traversal have not yet been joined
to this stage. This checkpoint does not claim shared arithmetic setup reuse or
completion of the S4 numerical and resource gates.

`metadataHaloClass_inputBank_exec` now executes generation of the missing
origin packets and batch count from retained canonical binary geometry and the
selected positive length word on 157. `releasedHaloClass_exec` factors the
existing halo controller's run/release law; `binaryHaloClass_exec` supplies its
loaded table using the shared binary bank loader. The 168-stack placement reads
s/t/band/a/b from 145/146/147/149/151, zero from 154 and width from 163, preserving
all those sources and the selected length. Its injectivity uses a small left-
inverse proof rather than a Cartesian register split, which exceeded default
heartbeats. No limits were raised.

The generated packets equal the ambient origins represented by `haloPackedOffsets`
at the same `weightWorkspaceWidth` as the batch. The controller prepends them to
native 109's FFT-exponent suffix and emits the actual group cardinality on 116.
From an ordinary `naturalGroupInputBank`, the theorem derives blank workspace
and proves the resulting exact `batchInputBank`, preserving the borrowed RHS,
result suffix, input/output and all other stacks. `Host.embStk_updateR` factors
the structural projection/update law used in this ABI proof. The metadata and
native-bank endpoints check near 2.2 GiB.

This control generation avoids unary copies of ambient geometry. The production
controller now uses the local phase scan described below. Installing ordinary
scalar headers from shared setup, loading/traversing the actual key stream,
preserving all prior group accuracy, and joining the publishing stage remain open. No selected-time bound or
shared arithmetic setup reuse is claimed; the full S4 gates remain open.

The local halo scan now has a checked host interface. `haloPhaseRangeCode`
computes the binary endpoints in eight table instructions; `localHaloGroupCode`
scans `haloPhaseCount` rows and emits exactly the existing length group in the
same order. `haloPhaseCount_scaled_le` bounds the scan by the halo span, and
`haloPhaseCount_le_length` gives the simpler span-plus-two bound when
`t-s ≤ s`. The generic `countedOriginHost_exec` publishes and counts any table
program with this emission contract; both the ambient and local scans instantiate
it. The local host costs `(36*haloPhaseCount+2)*tblC` plus the unchanged packet
publication cost. `localHaloClassCode` composes six initialization instructions,
eight endpoint instructions and the local loop, with table cost
`36*haloPhaseCount+16`. The production released, binary, metadata and native-bank
controllers now use this program; their packet order and exact final stack
contracts are unchanged. Their proofs require the valid halo interval `a ≤ b`,
already present at the native-bank endpoint. Release and binary-load costs remain
explicit. The legacy ambient controller remains available for existing callers.

The shared publication buffer now has a checked processed-key invariant.
`scatterRows_slice_off` lifts the structural off-window law to arbitrary slices.
`haloGroup_scatter_word_preserves` scales the cross-class geometry by the actual
word width and includes the borrowed output suffix. Consequently
`packedHaloGroupOutputSpec_scatter` preserves another class's full accuracy
contract, and `packedHaloGroupOutputs_scatter` extends the contracts for a list
of processed lengths by the newly published length. No numerical error is added:
the old words are identical. This matches the scatter expression returned by
`reusablePackedCellBatchPublish_sized_exec`. The invariant checks near 2.1 GiB.
Instantiating it along an executed key traversal, with common precision and
installed headers, remains open.

The packed runtime now reuses the existing retained-header installer rather than
assuming its ordinary parameter bank has already been supplied.
`packedGroupHeaders_exec` embeds `installGroupHeaders` unchanged and reuses
`copiedGroup_project` to obtain `naturalGroupInputBank` for an arbitrary borrowed
local source. It preserves every register at or above 117. `packedHaloGroupInput`
then executes the binary-metadata local controller, yielding exactly the actual
`batchInputBank` with generated halo offsets and count, while retaining those
high registers. Its explicit cost is the existing header-install cost plus
`binaryHaloClassCost`; it checks near 2.1 GiB. This supplies the next-group input
handoff from retained scalar masters and binary selected length. Consuming the
key stream, maintaining selected length in both banks, and joining successive
publishing executions remain open; the older counted-key traversal provides the
structural loop pattern, but uses an ambient output and cannot be substituted
for the packed traversal.

`packedLengthKey` now consumes a key packet from 126 using retained width 125,
replaces the old unary selected length on 128, and retains the same binary word
on 157 for the metadata controller. Its exact result changes only these three
registers; conversion scratch 134--136 is restored. The cost explicitly includes
clearing the two old length headers. The generic `takeBinaryUnaryKey_exec`
factors the existing prefix-consumption and binary-to-unary proof; the original
`takeUnaryKey_exec` reuses it and clears the retained word. No second conversion
or reconstruction of the binary key is needed. The key step checks structurally
and supplies both representations required by `packedHaloGroupInput_exec`.
Joining this step to the retained-header input and publishing stages in the
counted traversal remains open.

`keyedPackedHaloInput_exec` now composes packet consumption, both selected-length
headers, retained scalar installation, local origin generation and count generation.
It assumes no installed ordinary native input bank and retains the queue suffix
and all high registers except the selected-length headers and queue itself.
`keyedPackedHaloPublish_sized_exec` joins this actual input stage to the reusable
publisher. For a nonempty class it executes from the generated key through the
cell solve, shared-buffer scatter and borrowed-source cleanup, returning the
physical output accuracy/validity contracts and exact released native bank.
The whole cost includes old-header disposal, decoding, header copies, local
scan, the full uncached numerical batch and publication cleanup. It checks near
2.2 GiB. The candidate keys can include classes with no halo cells, so a runtime
empty-count branch is still required before this nonempty execution theorem can
be iterated over the generated list. The counted traversal, shared setup reuse,
and full S4 resource gates remain open.

The keyed publication now covers empty candidate classes too.
`emptyPackedHaloGroup_exec` releases precisely the copied native scalar headers
using the existing structural `clearWords` executor. The empty exit restores the
same released native bank and leaves every high register unchanged, including
the packed publication buffer. `conditionalPackedHaloPublish_sized_exec` tests
the generated count on 116 once and chooses this exit or the existing reusable
numerical publisher. Both branches return the identical scatter, accuracy,
validity and borrowed-source contracts; the empty contracts are vacuous and its
scatter is the identity. The branch adds two steps and charges the exact empty
header cleanup rather than a numerical setup. `keyedPackedHaloPublish_sized_exec`
now uses this conditional continuation and has no nonempty-class hypothesis.
The composed keyed stage checks near 2.2 GiB; counted iteration and shared
numerical setup reuse remain open.

The actual counted packed-key traversal is now checked.
`PackedHaloReady` packages the released native bank, retained scalar/geometry
masters, source, word width, bounded selected-length headers, publication prefix
and fresh scratch. `of_publication` restores this invariant from the existing
native-bank and high-frame contracts; `update_count` isolates the loop-owned
count on 127. `packedHaloReady_publish` executes the total keyed publisher,
restores readiness, and extends the complete processed-key accuracy contracts
using the structural cross-class scatter theorem. `packedHaloKeyLoop_exec`
then uses ordinary list induction to verify the fixed count-controlled loop:
each iteration pops 127, consumes one packet from 126, publishes and cleans the
class, and tests the remaining count. The final queue is exactly the borrowed
suffix, the count is empty, and all processed classes retain their contracts on
one common-precision packed buffer. No key-count factor enters the error bound,
and even repeated keys are permitted by this invariant. The explicit time bound
is the sum of `packedHaloKeyCost+3` plus one terminal test. Modules check/build
below 2.7 GiB. Connecting generated-key initialization and initial readiness,
projecting the final full-halo numerical contract, shared numerical setup reuse,
seam dispatch and the full S4 resource gates remain open.

`runGeneratedPackedHaloKeys_exec` now specializes the executed counted loop to
`haloLengthKeys`. It derives positive lengths, the ambient size bound, common
FFT padding and binary fit from the existing candidate geometry, initializes the
loop flag from its actual count, and returns all generated groups' accuracy
contracts on the final buffer. `haloInterior_error_of_packed_reads` combines
these contracts with the existing exact coverage and solver geometry to prove
the uniform full-interior error bound directly for `packedIntervalRead` of that
physical output. It needs no separately supplied ambient Gaussian output field
or ambient-sized tape. `packedCellOrigin_local_index` factors the generic
coordinate-to-local-word address calculation; this structural abstraction
avoids a default-heartbeat timeout elaborating a concrete halo offset expression.
The generated execution module checks near 2.2 GiB. The generated packet queue
and initial reusable state are still hypotheses: the retained-header key
initializer must be embedded and connected. Shared numerical setup reuse,
residual/boundary solve/recovery composition, seam dispatch and the final S4
resource gates remain open.

The packed interior now has an initialized executed endpoint.
`initializePackedHaloKeys_exec` embeds the existing `initializeHaloLengthKeys`
program without duplicating candidate selection or deduplication. Its exact
four-register result establishes `PackedHaloReady`, generates the key/count
prefix and retains the binary and numerical word widths. The pure
`initializedKeyRuntimeR` update law is now polymorphic in the register-bank size,
so both embeddings use the same state description. `solvePackedHaloInterior_exec`
composes initialization with `runGeneratedPackedHaloKeys_exec` and proves uniform
whole-interior accuracy directly on the final physical local buffer. It starts
from retained scalar parameters, unary endpoints, canonical binary geometry,
a released native bank, a caller-owned local publication prefix and fresh owned
scratch. No generated queue or loop-readiness hypothesis remains. The borrowed
queue suffix is restored and the loop count is empty; the returned readiness
retains the runtime widths and last selected-length headers for subsequent work.
Both new modules check near 2.2 GiB. Rewriting the workspace-width equality
before the word-width equality keeps the composition structural and avoids
expanding concrete generated-key expressions under default heartbeat limits.
The numerical batches still pay full uncached setup. Connecting the interior to
local residual construction, normalized boundary solve and recovery, establishing
shared numerical setup multiplicity, seam dispatch and final S4 time/live-stock
bounds remain open.

The executed interior now also preserves its encoded magnitude representation.
`packedCellScatter_range` is the generic aligned-scatter preservation law for
`EncodedRange`; the per-key, counted-loop, generated-key and initialized-solver
contracts propagate the existing `interiorOutputExponent` bound from the initial
publication prefix. `encodedRange_packedField` turns any bounded encoded local
prefix of the correct length into a supported ambient Gaussian field, its exact
local stream representation, global magnitude bound and `Fits` contract.
`solvePackedHaloInterior_field_exec` applies this to the actual final executed
buffer and returns uniform whole-interior field accuracy. It checks near 2.2 GiB.
The normalization proof is factored through `haloResidual_normalization_bound`,
which takes whole-interior `ErrorOn` directly; the older per-cell statement is
now a thin specialization. Thus the completed grouped execution supplies the
semantic field/error contract needed by normalization without assuming accuracy
for unexecuted cells. Precision compatibility with the boundary solver remains
an explicit hypothesis of normalization. For machine composition, the key
initializer needs 138 empty, while coupling retains its coefficient page there:
page generation/retention must therefore follow key initialization. That executed
handoff, the residual/boundary/recovery composition, setup reuse and final S4
resource gates remain open.

The completed packed interior state now supplies coefficient setup in the
shared-header view. `PackedHaloReady.coupling` reuses
`sharedCouplingHeaders_ready` and reads retained dimensions in place, with no
new scalar-header copies. `couplingIntervalMetadata_shared` transports the
canonical geometry through that same static view. The executed
`sharedCouplingCoefficientInterval` copies the retained lower endpoint once into
the temporary origin-index port, runs the existing binary-length guarded
coefficient-page generator through the shared permutation, and clears that
index. Its exact final state retains the page on 138, its actual count on 139,
and row width on 140; other stacks, including the published interior on 132,
are unchanged. `PackedHaloReady.coefficient_exec` instantiates this operation
from the solver's returned invariant and caller-owned endpoints/left frames,
requiring only fresh page-count/interval-count ports and the existing fit bounds.
The page setup is now an executable continuation rather than a supplied page
hypothesis; it checks near 2.2 GiB. Composing it with the initialized interior
execution and the RHS-preservation/coupling continuation remains open, as do
boundary normalization/solve/recovery, setup multiplicity and final S4 resources.

`packedHaloInteriorCoefficients_exec` now composes the actual full-halo interior
execution with coefficient-page generation, including the local RHS copy needed
by residual coupling. `preservePackedRhsFrom` generalizes the existing structural
RHS-preservation program to read a retained precision header directly; the native
112 version is a specialization. The composed program reads 119, preserves the
local RHS prefix on 93, initializes and executes all interior groups, then
generates the page after initializer scratch has been released. The result has
the fitted physical interior field and uniform error, the actual coefficient
page/count/row-width, canonical binary geometry, and shared-header
`CouplingReady`. The original I/O streams and borrowed queue suffix are retained.
The temporary RHS-copy counters and width are released with their explicit cost.
The generic `sharedCouplingPage_core` proves that retaining the page leaves the
shared arithmetic view unchanged. The per-key, loop, generated and initialized
interior interfaces now explicitly retain the proven 93/input/output restoration
facts; previously those facts were available inside execution proofs but omitted
from the loop contracts. The composed module checks near 2.2 GiB. Executing the
residual continuation from this state, then gathering/normalizing boundary data,
boundary solve/recovery, shared setup multiplicity and final S4 resource gates
remain open.

The complete grouped halo now has an executed local residual endpoint.
`packedHaloResidual_exec` composes RHS preservation, generated key initialization,
all interior classes, coefficient-page generation and
`preparedSharedLocalFeedCouplingInterval false`. It derives the coefficient-word
fit and reality contracts from the selected coefficient bounds, uses the actual
generated page/counts, restores the borrowed RHS suffix on 93 and prepends the
owned residual interval to the original local source on 110. The result retains
the physical fitted interior field, its whole-interior error, canonical geometry,
the numerical word width, the empty boundary-work port and the exact released
native bank. The page-only state has a generic native-bank projection law in
addition to the shared arithmetic-view law. The explicit cost sums the three
executed stages, with the interior preparation factored as
`packedHaloInteriorCoefficientsCost`. This still uses the nonseam assumption
`b-a+band ≤ s`. The residual module checks near 2.2 GiB.
`haloResidual_guarded_normalization_bound` now transports the stable
normalization contract to the exact guarded residual on every halo boundary
coordinate, where the existing guarded-row equality proves it is the ordinary
residual. It checks near 3.1 GiB and retains the explicit dominance and boundary
precision-compatibility hypotheses. The executed boundary gather/fold and
normalization/solve/recovery compositions, shared setup multiplicity, seam route
and final S4 time/live-stock bounds remain open.

The complete grouped execution now reaches solver-order boundary RHS data.
`packedBoundaryData_exec` is the shared structural composition of canonical
metadata selection, local residual gathering and the existing closed fold. It
restores the borrowed RHS suffix and changes only the retained selection mask,
actual boundary count and folded output. `packedHaloBoundaryData_exec` composes
that operation with the full generated interior/residual execution and proves
its boundary support from the existing halo-vertex geometry. Guarded residual
words are rewritten to ordinary coupling words exactly on `bFoldOrder` using
`bFoldOrder_toFinset` and the existing guarded-row equality. The final 143 is the
actual ordinary residual in solver order, 116 is the actual boundary cardinality,
and 167 is the reusable mask. The exact native bank is shared through
`PhaseCellCountedReleasedCellBank`, extracted from the older single-batch wrapper
to avoid importing that unrelated pipeline. The retained coefficient page,
page count and row width are now explicit in both residual and folded-boundary
contracts, so recovery can reuse the generated setup. The full-halo module
checks near 2.2 GiB. The numerical boundary normalization/solve/unscale and
recovery still need composition at compatible precision; shared setup accounting,
seam dispatch and final S4 time/live-stock gates remain open.

The actual folded RHS now also has an executed real projection.
`packedHaloRealBoundaryData_exec` composes the complete halo pipeline with
`mapOwnedLine`, a generic two-reversal map of an owned line. It changes only
143 during projection, uses released scratch 0, and pays exactly four times the
symbol count plus four. The resulting real words satisfy both the input
magnitude bound and the normalized half-unit bound, by the whole-interior error
contract rather than a new per-cell certificate. Dominance and compatibility
with boundary working precision remain explicit. This module checks near
3.1 GiB.

`packedBoundaryFactorReg` places the existing factor workspace in 242 registers,
leaves geometry 154--167 and coefficient row width 140 outside its image, and
maps the kernel RHS directly to the emitted line 143. Its injectivity follows
from a structural left inverse. `packedBoundaryNormalize_exec` transports the
existing generated normalization kernel through this placement: only 143
changes, the original cost is retained, and no RHS transfer is required. The
kernel readiness and clean-workspace assumptions are still supplied explicitly;
they have not yet been derived from an executed factor supplier. Composition
with the full halo producer, solve/unscale, recovery, setup reuse, seam dispatch
and final S4 time/live-stock bounds remain open.

The placed complete numerical kernel now checks as well.
`packedPreparedResidualSolve_exec` reuses the existing normalize/solve/unscale
proof under the same flat injection, consumes the actual RHS on 143 and appends
the unscaled solution on 238. A generic two-write embedding lemma transports its
exact output frame without expanding the intermediate state. The projected
post-state and `packedPreparedResidualSolve_ready` retain factor pages and solve
headers for another RHS. `haloResidual_norm_bound` isolates the whole-interior
stability argument without any boundary precision assumption;
`packedHaloResidualSolve_exec` uses it to derive the kernel's coarse component
bound for the actual real coupling rows in `bFoldOrder`, rather than accepting
an arbitrary bounded RHS. Factor format, StageInv, factor streams and readiness
are still premises. The full producer-to-consumer handoff and executed factor
supplier remain open, alongside recovery, common precision instantiation,
shared setup accounting, seam dispatch and final S4 time/live-stock bounds.

The factor supplier now executes in the packed layout as well.
`packedBoundaryFactory_spec` transports the existing complete constructed
Schur/factor factory through `packedBoundaryFactorReg`, returning computed
columns, their accuracy and format, StageInv, actual factor streams and solve
readiness. Its off-image frame retains the high geometry bank 154--167 and coefficient
row-width port. This factory runs before the halo RHS producer: its input
freshness includes the future RHS slot, so it cannot simply be inserted after
RHS construction.

`packedHaloRuntimeReg` places the entire 168-register producer in the low bank
of the same 242-register machine. `placedPackedHaloRealBoundaryData_exec`
retains the complete producer contract and proves that all registers at least
168 are unchanged. `packedBoundaryFactorState_of_high_frame` identifies the
resulting numerical state as exactly the old factor state with RHS replaced;
`packedBoundarySolveReady_halo` therefore preserves solve readiness across any
such halo execution, without rechecking its individual stages. Remaining
handoff work includes generating the producer's released native input from the
factory post-state, preserving/deriving its left-workspace conditions, and
instantiating common precision. These are not yet a composed factory/halo/solve
execution. Recovery, shared setup multiplicity, seam dispatch and final S4
resource bounds also remain open.

The prepared factory now retains its native arithmetic contract in the public
result, together with the actual coordinate-page and header lengths. The
proof reuses `boundaryRecoveryReady_of_frame`; the two existing batch callers
continue to use the original numerical result. The packed factory transports
the strengthened contract unchanged.

`releasePackedBoundaryRuntime_exec` erases only coordinate page 109 and headers
115/116, with exact cost `2*(N*V+V+N)+7`. Its generic native-bank theorem derives
the producer's exact `releasedCellBank` from the preserved arithmetic readiness
and clean low left stacks. Its factor-state theorem proves the cleanup leaves
every factor role unchanged. `packedBoundaryFactoryRelease_spec` composes the
executed factory and this cleanup, returning the exact released native bank,
computed columns, factor streams, solve readiness and existing off-image frame.
This closes the native-register cleanup step but is not yet the complete halo
handoff: factory table output on 132 still prefixes the caller's publication
buffer. A promising direct placement is the unused high register 220 (the
ordinary placement moved old 206 to 143); routing only the factory's table output
there would protect the publication buffer without copying it. Retained master
and endpoint frames and the producer's left-workspace contract must also be
carried through the full composition. Common precision, recovery, setup reuse,
seam handling and final S4 resource bounds remain open.

The factory table routing is now executed and checked.
`packedBoundaryTableRouting` is the static permutation of 132 and the unused
register 220; it adds no copy operations. The generic placement excludes 220,
so routing the whole existing factory/cleanup program preserves the original
publication buffer on 132 exactly. `routedPackedBoundaryFactoryRelease_spec`
retains the complete computed numerical and released-native contracts, with
solve readiness and clean left stacks stated in the actual solver view.
The routing fixes every numerical factor role and every native register;
`packedBoundaryTableRouting_left` handles the table port's left stack using its
preserved initial value. The existing factory frame for legacy headers and
endpoints is now exported through factory, cleanup and routing, instead of
being discarded at each wrapper.

The next geometry handoff must generate canonical metadata after the factory:
its freshness requirements on 147 and 151 conflict with preinstalled encoded
geometry on those same ports. The high geometry bank 154--167 can remain
reserved throughout. The existing binary-header bank and retained
`sharedCouplingReg` view can generate the low metadata from master s/t/band and
endpoint headers, followed by `completeCouplingIntervalMetadata`; neither needs
an ambient data scan. The complete factory/geometry/halo/solve composition,
common precision, post-halo left-workspace proof, recovery, setup reuse, seams
and final S4 bounds remain open.

The post-factory metadata initializer now also executes.
`prepareRetainedCouplingMetadata_exec` instantiates the existing structural
`binaryHeaderBank` checker on sources 121/122/124 and endpoints 141/142, producing
the same five binary geometry fields directly from retained unary headers.
Sources, scratch and the native bank are unchanged. The interval wrapper
`prepareRetainedCouplingIntervalMetadata_exec` composes that conversion with the
existing binary completion program, using descriptor origin/count on 155/165.
It returns canonical `CouplingIntervalMetadata` with cost at most
`(s+t+band+a+b)*(4*V+10)+56*V+77`. Its explicit output changes only the nine
metadata destinations, and `retainedCouplingIntervalMetadataR_off` is the shared
frame for all other ports, including the publication buffer and native source.
The remaining work is to compose this initializer in the 242-register factory
and halo execution, then close precision and post-halo left-stack readiness
before the solve/recovery and global resource gates.

The factory and geometry stages now have a single executed composition.
`placedRetainedCouplingIntervalMetadata_exec` lifts geometry generation into the
242-register machine and exports a complete frame outside its nine destination
ports. It preserves all left stacks; generic native-bank and factor-state
lemmas use the same frame. `routedPackedBoundaryFactory_header_frame` condenses
the factory's legacy, reserved-bank and publication frames into one retained
header rule for 117--167, excluding only the newly installed RHS port 143.

`packedBoundaryFactoryGeometry_spec` executes the routed factor factory,
coordinate-page cleanup and canonical metadata generation in sequence. It
obtains s/t/band from the factory's actual retained master invariant, transports
endpoint and descriptor seeds through the shared frame, and obtains scratch
blankness from the exact released native bank. The result contains computed
columns and their accuracy/format, StageInv, actual factors, solve readiness,
canonical metadata, the released native input and the original publication
buffer. The only geometry inputs still supplied are the binary width,
origin/count seeds, initial destination freshness and the existing fit bound;
there is no readiness assumption on an intermediate factory state. Remaining
work is its full halo/solve composition at a proved common precision, the
post-halo left-workspace contract, recovery, shared setup accounting, seams and
final S4 resource bounds.

The shared working format now has an explicit arithmetic witness.
`executionSizing_of_allowance` proves generically that conserving
`target+rhsExp` preserves precision, stage precision and word width. Let
`T = initialSchurTarget p u (boundaryTableBits p target rhsExp rowCount) 2`.
`boundaryHaloTarget = T+2-rhsExp` conserves that allowance between raw halo input
and the normalized boundary setup. Its sizing theorem proves all three format
equalities; its accuracy theorem proves it is at least
`initialSchurTarget p u target rhsExp`. Thus the format compatibility required by
the existing halo/residual consumer can be instantiated from a chosen target,
rather than remaining an arbitrary equality premise. This witness still needs
to be used in the full factory/geometry/halo/solve composition; it does not by
itself close post-halo left-stack readiness, recovery or the global S4 bounds.

The complete factory-to-boundary numerical execution now checks.
`packedHaloBoundarySetup_exec` composes factory generation, coordinate cleanup,
geometry and the full grouped halo residual pipeline. It selects
`boundaryHaloTarget`, derives format compatibility and transports masters,
endpoints and freshness through one retained-header frame. It returns the
actual fitted interior field, its error contract, solver-order real residual,
computed columns/factors, coefficient page and exact borrowed RHS queue.
The factory/geometry contract now also preserves caller register 93 explicitly.

Left-stack restoration is now a proved invariant rather than a missing premise.
`packedCell_left_eq` combines the arbitrary native prefix with its high-bank
frame. Publication, empty/nonempty class dispatch and keyed input/publication
now export full left equality; the arbitrary-key induction carries it through
the complete generated interior run. Coefficient generation, residual feed,
boundary gather/fold and real projection all change only right stacks, so the
same invariant reaches the placed producer. `embOvr_left_of_eq` transports that
invariant through the shared bank embedding. No cleanup instructions or costs
were added. `PackedBoundarySolveWorkspace` packages the resulting clean left
bank, multiplier scratch, precision and retired normalization/unscale controls.
Its swap port is required fresh in the initial caller bank.

`packedHaloBoundarySolve_exec` then composes the existing retained-factor
normalization/solve/unscale kernel with that generated setup and actual RHS.
The result clears 143, appends the unscaled computed boundary solution on 238,
preserves the caller's original 238 suffix and 93, and retains the interior
publication, original source suffix, coefficient page and canonical geometry.
It also retains solve readiness for factor reuse. Its boundary output is the
existing `bandSolveVec` of the generated factors and normalized actual residual;
this is an execution theorem, not yet the final accuracy/recovery theorem.
Remaining S4 gates include semantic boundary-error composition, recovery/core
publication, setup multiplicity and cache reuse, seam dispatch, ownership and
release of the routed raw table on 220, and final time/live-stock/tensor bounds.
The factory's input/output stream frame must also be carried into the final
public composition; the underlying constructed factory already proves it.

The full-boundary checkpoint passed the combined execution/axiom audit and
23 sequential guarded checks covering the changed left-frame and composition
modules. The largest measured module was `PhaseCellPackedHaloBoundarySetup` at
3286.2 MiB; `PhaseCellPackedHaloBoundarySolve` used 3230.7 MiB. All remain below
the 4 GiB per-module CI target. These checks establish the execution and
workspace contracts above, not the remaining semantic/recovery/resource gates.

The executed boundary output now has its semantic error bound.
`haloResidual_error_bound` proves that the actual real projected residual
approximates the exact Schur RHS using only whole-interior accuracy. The exact
interior solver may be chosen from dominance; `solves_unique` identifies it
with the principal solution used by the executed interior proof. Its explicit
error is `haloResidualError`, bounded by `3/2^cellTarget` at the execution format.

The boundary error proof now separates residual and matrix budgets.
`boundary_unscaled_solve_target_of_rhs_budget` reuses the existing unscaled
numerical estimate and applies `boundary_perturbation_target` with zero RHS
error to pay matrix quantization. The remaining residual contribution is
exactly `32*p*delta`. `boundaryHaloTarget_residual_budget` absorbs that term
in `1/2^(target+1)` from the selected target's existing initial-Schur accuracy.
This works for arbitrary RHS exponent: it does not require the interior error
to meet the stronger matrix-bit target. The original `3/2^target` total error
and stable solution magnitude are retained.

`haloBoundary_solution_accuracy` joins these estimates to the generated factor
format, StageInv and actual matrix error. It returns the unscaled solution's
length, word fits, error on every folded boundary coordinate and stable
magnitude. The exact interior inverse is constructed mathematically from
dominance. The factory's already-proved matrix error is now carried through
`packedHaloBoundarySetup_exec`, and `packedHaloBoundarySolve_exec` applies the
accuracy theorem to its actual computed list. `boundaryFoldedRead_error` then
states the same accuracy for decoding the emitted tape on 238, including its
arbitrary retained suffix; this is a physical output observation, not only an
integer-list property.

The recovery field bridge is local as well. `packedBoundary_scatter_solution`
identifies inverse folding, real projection and sparse scatter with the packed
zero-extended boundary field. Its packed reader and error lemmas transport the
same solution accuracy over the halo interval without an ambient scan. The
runtime inverse-fold/scatter placement and the second packed interior pass
still need composition. Recovery/core publication, caller stream frames, setup
reuse, seam dispatch, raw-table ownership and final S4 tensor/time/stock gates
remain open.

The boundary-accuracy checkpoint passed the combined execution/axiom audit and
six sequential guarded checks for the residual estimate, split error budget,
solution accuracy, packed/folded readers and two executed endpoints. Peak RSS
was 3287.8 MiB for setup and 3234.0 MiB for the complete solve; every checked
module remained below the 4 GiB CI target. Whitespace validation passed.

The recovery handoff now has an executed owned-prefix isolation step.
`packedBoundarySolutionInput_exec` moves exactly the counted boundary solution
from port 238 to inverse-fold input 231, restores the caller suffix on 238,
and preserves every other stack, including retained factors and coefficients.
It reuses `moveCountedLine_exec`; its time is `N*(12*w+9)+12`, independent of
the borrowed suffix length. The five workspace ports must still be discharged
from the boundary-solve endpoint when composing recovery. The new module passed
a guarded check at 1932.1 MiB. Inverse-fold placement and the second interior
pass remain open.

The packed recovery inverse fold is now executed as well.
`packedBoundaryUnfoldReg` extends the existing factor placement by four fresh
ports for inverse-fold counters and output; its injectivity follows by composing
register permutations with the established factor injection. The arithmetic
kernel is reused unchanged. `packedBoundaryRealUnfold_exec` consumes the exact
solution on 231 and emits real boundary values in natural order on 245, while
its exact final-state equation preserves all other data. The composed
`packedBoundarySolutionUnfold_exec` first isolates the owned prefix on 238 and
then inverse folds, preserving the arbitrary caller suffix on 238. It adds only
the existing counted-move cost to the established inverse-fold/projection cost.
The composed module passed a guarded check at 3201.0 MiB. The combined
execution/axiom audit also passed (4.8 GiB aggregate guarded-build peak). Discharging its
workspace premises from the full solve endpoint, generating and executing the
local scatter, and composing the second interior pass remain open.

The boundary solver now exports the workspace needed by recovery instead of
hiding it behind its final-state construction. `PackedBoundarySolveWorkspace.publish`
proves that the publication update preserves the complete numerical workspace;
`packedHaloBoundarySolve_exec` returns this fact. Both the setup and solve
endpoints now also return the generated boundary-count tape on 116. The
`packedBoundaryRecovery_clean` and `packedBoundaryRecovery_width` lemmas obtain
the old-bank recovery scratch and word width directly from the retained
workspace and solve readiness. The numerical solver count lives on 206 and is
separate from the generated count on 116; recovery uses the latter.

The composed inverse-fold handoff now borrows fresh ports 246 and 247 for its
counting controls, avoiding extra caller-header emptiness assumptions on 240
and 241. Its left-bank premise is restricted to the placed 224-register view,
rather than requiring the entire surrounding bank to be blank. Fresh-bank
extension and placement still need to be joined to the full solver endpoint;
local scatter and the second interior recovery pass remain open.

This handoff-contract checkpoint passed the combined execution/axiom audit and
four sequential guarded file checks. Peak RSS was 3087.9 MiB for workspace,
3200.8 MiB for inverse folding, 3286.4 MiB for setup and 3236.1 MiB for the
complete solver. The aggregate guarded-build peak was 3.5 GiB; whitespace
validation passed.

The fresh-bank inverse-fold bridge is now proved from the solver's actual
postconditions. `packedBoundaryRecoveryUnfold_exec` derives the placed left-bank
and multiplier conditions, all old-bank scratch emptiness and word width from
`PackedBoundarySolveWorkspace` and `BoundarySolveReady`; it takes the generated
116 count and actual 238 stream returned by the solver. Its only additional
workspace hypotheses concern the six freshly allocated ports. A structural
three-case swap lemma transports blank left stacks through each placement
permutation without enumerating register combinations.

`Host.extendStacks` provides a generic blank extension with an exact old-bank
projection and fresh-port lemma. `packedBoundaryRecoveryUnfold_extended_exec`
uses it to eliminate the fresh-bank hypotheses as well. The endpoint consumes
the actual owned boundary prefix, restores the arbitrary suffix on 238, and
produces the natural-order real boundary stream on 245 with the established
counted-move plus inverse-fold cost. The bridge passed a guarded check at
3193.0 MiB; the extension module checked at 1386.5 MiB. Local destination
retirement, generated scatter controls and scatter, then the second interior
recovery pass remain open. The existing binary local-length metadata on 165
can generate one unary local-row count for retirement and sparse publication;
no ambient-length scan is needed for that handoff. The combined execution/axiom
audit passed with 3.4 GiB aggregate peak; whitespace validation passed.

Local recovery-buffer retirement and sparse replacement are now executed.
`packedRecoveryDestination_exec` converts the retained binary local length on
165 once, retires exactly `N*w` owned symbols from 132, preserves the borrowed
tail, and leaves `N` ticks on 246. Its exact frame retains the inverse-folded
boundary words on 245 and all coefficient/factor data. Its cost is
`6*N+11*V+6+retireCountedLineCost N w`, independent of the caller tail.

`packedRecoveryPublishReg` reuses the inverse-fold placement, moving only the
local row-count role to 246 through one permutation. The existing controlled
sparse publisher executes unchanged in this placement. The composed
`packedRecoveryBoundaryBuffer_exec` replaces the retired first-pass interior
buffer by `cstream (packedInterval a N G)++tail`, consumes the natural-order
boundary input on 245, and retains the generated local row count. It adds
`89*N*w+41` to retirement cost and frames every other stack. The destination
module checked at 1937.1 MiB and the publication/composition module at
3194.8 MiB. The combined execution/axiom audit passed with a 3.4 GiB
aggregate build peak; whitespace validation passed.

This endpoint still assumes an origin-advance stream on 143, which its frame
restores; generating and releasing that stream is not yet composed. An
alternative is to reuse the already-generated boundary selector mask on 167
and develop a generic record-spread counterpart to `gatherRecords`, avoiding
origin packets altogether. Existing `Host.spread` is restricted to Boolean
source symbols, whereas boundary words contain paired complex symbols, so it
cannot be used directly. Both approaches must preserve local storage and avoid
an ambient scan. Full inverse-fold/buffer composition and the second interior
recovery pass remain open.

Recovery publication now uses the retained boundary mask directly; this
supersedes the preceding advance-control buffer implementation, whose new
placement and conditional publication wrapper have been removed. The generic
`Host.spreadRecordStep_exec` has one contract for both branches: transfer one
selected arbitrary-symbol record, or emit one fixed zero record. The new
`Host.spreadRecords_exec` composes those steps through `eachSym`, restores the
record mask and every temporary, consumes only the selected source prefix,
and emits all local records in natural order. Its proof is structural over the
record stream; no coordinate packets or finite certificates are introduced.
Its bound is `N*(6*w+10)+6`.

`maskedPackedBoundaryPublish_exec` instantiates this language for paired complex
words and the existing boundary selector. It reuses
`packedBoundaryRhs_select_ordered` and `packedBoundaryRhsMask_flags`, the same
selection semantics as RHS extraction. Zero extension supplies every false-mask
record. `packedRecoveryBoundaryBuffer_exec` now retires the old interior prefix
and runs this mask-based publisher; it has no advance-stream hypothesis. The
setup and full solver endpoints now export their actual retained 167 mask.
The generic record proof checked at 1968.3 MiB, the mask publisher at 2069.7 MiB,
and the complete buffer at 2069.0 MiB. Six final sequential guarded checks
also passed, including strengthened setup (3290.1 MiB) and solver (3239.8 MiB).
The combined execution/axiom audit and whitespace checks passed. Full inverse-fold/buffer composition,
recovery RHS construction and the second interior pass remain open.

The inverse fold and mask-based buffer replacement now form one executed
program. `packedBoundaryRecoveryField_exec` starts from the boundary solver's
retained workspace, actual folded solution and local metadata. It restores the
solution's borrowed suffix on 238 and replaces the owned first-interior prefix
on 132 by the packed zero-extended `boundarySolutionField`, preserving the
output suffix. Its exact final state changes only 238, 132 and the generated
local row count on 246. All other words, factors, coefficients and metadata
are framed. No scatter-control or intermediate readiness stream is assumed.
Its cost sums the established counted move, inverse fold, retirement and
record-spread bounds.

`packedRecoveryRhsInput_exec` reuses that same local row count to retire the
old residual prefix on 110, expose the retained original local RHS, and copy
only its owned prefix to 93 for recovery coupling. It releases the obsolete
boundary count on 116, selector mask on 167 and private row count on 246.
All scratch restores, all borrowed tails survive, and the exact frame retains
the newly published boundary field and factor/coefficient page. The boundary
setup and solve endpoints now also export their already-proved low native
scratch emptiness (all 117 old-bank ports except 93, 110 and 116), so subsequent
coupling readiness can be derived from execution rather than assumed.

The combined execution/axiom audit passed (7.1 GiB aggregate guarded-build
peak). Four sequential guarded checks passed: field composition 3199.0 MiB,
RHS input 1939.0 MiB, setup 3294.6 MiB and complete solve 3242.0 MiB. Whitespace
validation passed. Full field/RHS-input composition, retained header/scratch readiness for
recovery coupling, recovery RHS accuracy and the second packed interior pass
remain open, along with the broader S4 integration/resource gates.

The full local recovery-input handoff is now one executed program.
`packedBoundaryRecoveryInputs_exec` composes inverse folding, mask-based local
boundary publication, old residual retirement and original-RHS preservation.
It derives the shared count, width, mask length and scratch facts from the
first stage's exact final state. Its final state retains the packed boundary
field on 132, exposes the original RHS on 110, copies the owned RHS prefix to
93, restores the borrowed solution suffix on 238, and clears 116 and 167.
The private row count on 246 restores to its original blank state. Every other
register, including factors, coefficients and retained metadata, is framed.

`CouplingMasterHeaders` names the nine retained unary headers shared by both
coupling passes. Its frame lemma transports them without copying headers, and
its `ready` lemma derives `CouplingReady` from those headers and the released
native scratch bank. The boundary setup and complete solve now return this
header record and emptiness of 127, 135, 158 and 166. Port 135's emptiness was
already proved by the interior/coefficient endpoint; it is now carried through
residual, boundary selection, real projection and placement rather than
attempting to infer it from the high frame, whose page exceptions include 135.
No runtime cleanup or extra numerical setup was introduced for these facts.

The combined execution/axiom audit passed (5.8 GiB aggregate peak). Eight
sequential guarded checks passed for the two new interfaces and the six
strengthened execution endpoints, with maximum RSS 3314.1 MiB for setup and
3244.6 MiB for the complete solve. Whitespace validation passed.

Executing recovery coupling with the retained page, proving its recovery-RHS
accuracy at the common format, and the second interior pass remain open.
The fresh-bank embedding of the full solver and the broader S4 assembly,
seam/setup-reuse and resource gates also remain open.

The actual second coupling pass now executes in the packed recovery bank.
`packedRecoveryCoupling_exec` places the existing
`preparedSharedLocalFeedCouplingInterval true` kernel in the low 168 registers
of the 248-register machine. It derives `CouplingReady` from the retained
`CouplingMasterHeaders`, the boundary workspace's left-bank facts and the
released native scratch. The coefficient page and all headers are read in
place. The exact final state restores the borrowed RHS tail on 93 and emits
the local guarded recovery RHS on 110 above its retained source suffix; every
other stack, including the factor page, is framed.

`packedBoundaryRecoveryRhs_exec` joins this pass to the complete inverse-fold,
boundary-publication and RHS-input program. Its boundary field is the actual
`boundarySolutionField` of the computed folded list. It derives the second
pass's workspace, native scratch, header, geometry and high scratch conditions
from the first stage's exact final state; no intermediate ready state or
control stream is assumed. Word fits come from the boundary solution's proved
fits. The final state changes only the owned solution suffix on 238, local
boundary field on 132, recovery RHS on 110, and released 116/167 controls;
93 restores to the caller's original contents. Costs are the sum of the
already-proved local handoff and retained-page coupling costs.

The placed coupling checked at 3202.7 MiB and the complete recovery-RHS endpoint
at 3219.1 MiB. The combined execution/axiom audit passed with a 3.5 GiB
aggregate guarded-build peak; whitespace validation passed. Recovery numerical
error/magnitude budgets at the selected common
format, the second packed interior solve and final field accuracy remain open.
The full solver's fresh-bank embedding, seam/setup reuse and final S4
assembly/time/live-storage gates also remain open.

The common-format recovery numerical bridge is now proved for arbitrary RHS
exponents. `boundaryHaloRecoveryTarget p target rowCount` simplifies to
`target + 3*Nat.size (8*p) + Nat.size rowCount + 10`: the larger recovery RHS
exponent cancels against the retained source allowance. Its allowance and
sizing lemmas prove exact equality of precision, stage headers and word width
with the normalized boundary setup. Existing normalization guards pay both
recovery word fit and coupling roundoff; `boundaryHaloRecovery_error_budget`
reuses the established recovery budget with the two guarded boundary bits.

`haloRecoveryRhs_spec` applies the existing guarded-row estimate once to the
actual `boundarySolutionField`, obtaining global RHS magnitude, word fits and
error against the exact Schur recovery RHS. `haloRecovery_interior_error`
transports any accurate interior solve through the existing Schur stability
lemma, independently of its cell schedule. Finally,
`haloRecovery_boundary_format_spec` chooses the exact interior solution from
dominance and proves that a second solve at the selected target, combined with
the retained boundary words, meets `2^-target` on the full halo. This is the
mathematical contract needed by the second executed packed pass, not an
assumed numerical inverse or an ambient publication program.

The precision/budget module checked at 3083.7 MiB, generic recovery accuracy at
3189.7 MiB and combined boundary-format accuracy at 3184.9 MiB. The combined
execution/axiom audit passed at 3.4 GiB aggregate peak; whitespace validation
passed. Runtime second
interior execution and preservation of boundary entries remain open. The
existing initializer requires fresh 125/130/138/140 and zero selected-length
master 128. A static second-pass placement can map these five roles to the
blank recovery ports 242/244/245/246/243, respectively, while retaining the
original key header, word width and coefficient page. This permits reuse of
`solvePackedHaloInterior_field_exec` without clearing the original pages or
assuming the old selected length is zero. The original 118 stage and 120 level
masters and the remaining high fresh ports must be carried through the solver
endpoint for that placement, in addition to the coupling-header record.

The second packed interior solver now has an executed placement beside all
retained pages. `packedRecoveryInteriorReg` composes six register swaps with
the ordinary 168-register inclusion: 125→242, 128→243, 130→244, 138→245,
140→246 and 157→247. Thus the old key width, selected length, word width,
coefficient page, row-width header and selected-length binary word remain
owned and unchanged. The new 128 and 157 roles start blank, so no zero-length
assumption or cleanup of the previous class selection is needed. Injectivity,
low-bank identity and avoidance of retained ports/factor registers are proved
structurally from the permutation.

`packedRecoveryInterior_field_exec` embeds the existing
`solvePackedHaloInterior_field_exec` unchanged, returning the actual local
output prefix, fitted field, interior error and caller stream frames. It also
returns explicit preservation of the old retained ports and the entire
168–241 numerical bank. The execution module checked at 2170.3 MiB before the
last frame additions.

`PackedRecoveryInteriorReady` packages precisely the existing initializer's
input interface. `packedRecoveryInteriorReady_of_retained` derives it from
retained coupling headers, native scratch, metadata, stage/level masters and
six blank fresh ports. The boundary setup and complete solve now export the
118 stage and 120 level masters and the remaining high fresh ports. Repeated
permutation reduction initially exhausted default heartbeats in the bridge;
factoring fixed-register and six relocated-role equalities removed that cost
without changing proof limits. The bridge checked at 3216.5 MiB and placement
at 1402.3 MiB.

The final placed execution checked at 2171.0 MiB, strengthened setup at
3335.8 MiB and complete solve at 3248.1 MiB. The combined execution/axiom
audit passed with a 5.2 GiB aggregate peak; whitespace validation passed.

Full recovery-RHS/second-pass composition, the boundary-field initial encoded
range and preservation of boundary words across all cell publications still
need closure. The existing numerical recovery theorem then applies to its
interior accuracy. Full solver embedding, seam/setup reuse and final S4
assembly/time/live-storage gates remain open.

Boundary words now have an exact frame through every packed interior solve.
`haloPackedOffsets_interior` identifies every generated cell window as a subset
of the halo interior. `haloGroup_scatter_off_interior_word` combines that fact
with the existing generic scatter-slice frame, preserving each complete word
outside the interior, including boundary words, for arbitrary publication data.

`PackedHaloWordFrame` packages this property with reflexivity and transitivity.
The key publication endpoint supplies it once; the arbitrary-key loop composes
it structurally, and generated-key execution, initialization, field decoding
and the placed recovery solver now export it. No runtime program or cost
changed. `PackedHaloWordFrame.read` transports the frame to actual decoded local
reads, and `.error` combines final interior accuracy with the initial boundary
accuracy directly on the final buffer. Thus boundary preservation no longer
needs a guessed off-interior decoded field or another publication program.

`haloRecovery_boundary_range` proves that the retained packed boundary field
already meets the second interior solver's initial encoded-range contract:
its stable boundary magnitude is below the recovery RHS exponent and hence
the interior output exponent. No normalization or buffer rewrite is needed.
The frame module checked at 2095.9 MiB and the encoded-range/numerical interface
at 3191.2 MiB. Nine sequential guarded checks passed across the strengthened
execution chain; maximum RSS was 3336.8 MiB for setup, 3248.2 MiB for the full
boundary solve and 2171.7 MiB for the placed second interior solver. The combined
execution/axiom audit passed (3.4 GiB aggregate peak); whitespace validation
passed. Full recovery-RHS/second-pass execution composition and final
physical-read accuracy remain to be joined, followed by the full solver
embedding and the broader S4 seam/setup-reuse, assembly and resource gates.

The recovery RHS and second interior solver now have an execution composition
lemma. `packedRecoveryRhsState` names the exact five-port RHS poststate, and
`packedRecoveryInteriorReady_after_rhs` derives the relocated initializer's
entire input record from the original retained state and that exact frame.
Headers, native scratch, metadata and fresh ports are transported once.

`packedRecoveryFinish_exec` consumes the already-verified
`packedBoundaryRecoveryRhs` execution and runs the placed second interior solve,
with time bounded by the supplied RHS execution time plus the existing interior
cost. It returns the final local encoded field, fits and magnitude, interior
accuracy, boundary-word frame, caller stream/left-bank frames, restored solution
suffix on 238 and preservation of retained pages/factors. The coefficient count
on 139 is now also carried through the placed interior endpoint. This is an
execution composition interface; instantiating it with the actual boundary
solver's solution and the selected common-format numerical theorem is still
required for the final complete halo caller.

`packedRecovery_read_error` transfers the numerical theorem's merged
interior/boundary field error to actual reads of the final local buffer. It uses
fitted-word decoding on interior coordinates and the exact word frame on the
remaining halo coordinates. No off-interior value of the newly decoded field
is assumed. The physical-read lemma checked at 3185.8 MiB, RHS-state readiness
at 3221.1 MiB and composed execution at 3217.9 MiB. The strengthened placed
interior checked at 2181.7 MiB. The combined execution/axiom audit passed at
3.4 GiB aggregate peak; whitespace validation passed. The complete halo caller,
full solver embedding and broader S4 assembly/seam/setup-reuse/resource gates
remain open.

`packedBoundaryRecovery_spec` now closes the local recovery caller from the
actual folded boundary solution and retained factor state. It runs the RHS
producer, obtains the exact interior comparison solution from dominance, runs
the second solve at the shared format, and proves the final error bound on
physical reads of port 132. It preserves caller streams, left banks, retained
coefficient pages/counts and factors, and restores the solution suffix. Its
cost is the sum of the existing input, coupling and interior costs.

The complete recovery theorem passed its guarded check at 3248.8 MiB. The
combined execution/axiom audit, including this theorem, passed (14921 build
jobs, 3.5 GiB aggregate peak). This starts at the solved boundary state: the
original setup-to-recovery composition, full S4 assembly, seams, setup reuse,
release and final time/live-storage gates remain open.

`packedHaloSolve_spec` now composes the original local setup interface with
both interior passes, the folded boundary solve and recovery. It chooses the
first interior comparison solution from dominance and obtains the boundary
solution's accuracy from the executed boundary endpoint; neither is a caller
oracle. It returns actual final packed reads within `2^(-target)` of the exact
halo solution, a fitted output field, restored ports 93/238 and the sum of all
existing setup/solve/recovery execution costs. Coefficient fits are derived
from the existing numerical bounds. The caller still takes the established
initial workspace/header and encoded-buffer contracts.

`Host.exec_extendStacks` factors the 242-to-248 handoff generically: an arbitrary
program executes in an extended blank bank with identical time and exactly the
extended poststate. `eq_extendStacks` reconstructs that state from its view and
fresh-bank frame. This avoids separate concrete transport proofs for all six
recovery registers. The extension module checked at 1389.1 MiB; the complete
local caller checked at 3249.4 MiB. The combined axiom audit passed (14922 jobs,
3.5 GiB aggregate peak), with only the approved axioms. Whitespace validation
passed.

This closes the local nonseam execution/accuracy composition, not S4. The full
caller input/output stream frames, owned-page/factor release, generated core
publication and tensor assembly, seam fallback dispatch, complete-key setup
reuse, and uniform final time/live-storage bounds remain open.

The local caller now preserves both caller streams explicitly. The existing
`constructedBoundaryFactor_spec` stream equalities are carried through the
prepared/placed factories, runtime release, geometry preparation and complete
boundary solve. The first interior pass supplies its stream frame through the
native-bank projection, and recovery composes it with its own frame. No runtime
code or cost changes were needed for this contract strengthening. Existing
constructed batch callers were updated for the stronger supplier result.
Nine sequential guarded checks passed across the affected downstream modules;
maximum RSS was 3334.6 MiB for setup. The prepared supplier checked at 3257.6 MiB.

`packedRecoveryRelease` reuses the existing coefficient-page disposer through
an injective placement that reads the retained word-width header on 130.
It consumes exactly the coefficient page on 138 and its metadata on 139/140,
restoring all disposal scratch. Recovery exports the required native scratch
facts from the second solver's actual ready state. `packedHaloSolve` now runs
this disposer after recovery and includes its cost; `packedHaloSolve_spec`
returns empty 138/139/140 together with the same fitted final buffer and
physical-read accuracy. This releases the owned coefficient page, not the
retained factor bank or remaining setup table.

The placed release checked at 2086.7 MiB, strengthened recovery at 3248.9 MiB,
and the complete caller including release at 3258.7 MiB. The combined axiom
audit passed (14927 jobs, 3.5 GiB aggregate peak); whitespace validation passed.
The remaining gates are factor/setup-table release and full scratch lifecycle,
generated core publication and tensor assembly, seam dispatch, complete-key
setup reuse, and uniform final time/live-storage bounds. S4 remains open.

The routed raw table now has an exact ownership relation through every local
solver wrapper. `preparedBoundaryFactory_spec` obtains it from the construction's
legacy-bank frame; packed placement, runtime release, routing, geometry and
both boundary endpoints preserve it. Thus port 220 contains exactly the generated
`bandTableWords` prefix followed by the caller's original port-220 suffix.
No blank-table assumption is introduced.

`packedTableRelease` places the existing structural `retirePackedBandTable`
program in the recovery bank. It reads the retained factor dimensions (204,
206 and 174), retires ragged columns in reverse order, and restores native
scratch. Its proof reuses the existing retirement execution theorem through
an injective register permutation, with identical time. The local caller now
runs this retirement after coefficient-page release, returns `F.R 220 = S.R 220`,
and charges `retirePackedBandTableCost` in `packedHaloSolveCost`. Output reads,
fitting and caller stream preservation continue to hold for the same final
state. Retained factors provide the dimensions; the caller supplies neither a
packed-size certificate nor external disposal controls.

The placed table retirement checked at 2055.0 MiB and the complete caller at
3275.6 MiB. The combined execution/axiom audit passed (14931 jobs, 3.5 GiB
aggregate peak). Nine sequential guarded checks of the strengthened downstream
modules also passed; maximum RSS was 3334.6 MiB for setup. Whitespace
validation passed. Factor-bank cleanup and its volume bound remain separate,
as do generated scheduling, seams, complete-key setup reuse, tensor assembly
and uniform final time/live-storage bounds. S4 remains open.

`BoundaryFactorStock` now packages the per-register bound needed to dispose of
the owned factor bank. `boundaryFactorStock_of_bounds` derives it from the
existing permanent-data and unfolding-header bounds, using the structural
factor-register coverage lemma. The live RHS port is excluded. The prepared
factory obtains these bounds from `constructedBoundaryFactor_spec`; all placed
factory, geometry, setup and boundary-solve wrappers now carry the stock fact.
`packedBoundaryFactorStock_of_high_frame` transports it across halo execution
once, rather than reproving every factor-page case.

`packedFactorOwnedIndices` selects the fresh high factor registers, excluding
the live RHS. Their injective placement avoids the raw table and both borrowed
source/result suffix ports. `packedFactorRelease_exec` applies the existing
`clearWords` execution theorem, with a list-induction sum bound for its cost.
The caller derives its stock premise from the constructed boundary result and
recovery's exact frame; no size certificate is supplied externally.

`packedHaloSolve` now runs coefficient-page disposal, raw-table retirement and
factor-bank disposal after recovery. Its final theorem returns an empty owned
factor bank in addition to restored port 220, empty coefficient-page metadata,
caller stream frames, the fitted output and physical-read accuracy. The
symbolic cost includes all three disposals. The full caller checked at
3284.0 MiB; the factor disposer initially checked at 3099.6 MiB. The combined
axiom audit passed (14933 jobs, 5.7 GiB aggregate peak). Thirteen sequential
guarded checks of the changed modules also passed, with maximum RSS 3342.9 MiB
for setup. The final factor-disposer check used 3097.7 MiB. Whitespace
validation passed.

This closes paid factor disposal for the self-contained local nonseam call.
It does not establish reuse across RHS calls or restore every low/new-bank
runtime header. Those contracts, the generated core schedule, seam fallback,
normalized complex/tensor assembly, complete-key setup reuse and uniform
selected time/live-storage bounds remain open. S4 remains open.

`preparedPackedSlice_exec` now generates the two symbol-count controls from
borrowed word-count and word-width headers, executes the existing restoring
packed slice, and releases the generated counts. Its exact state changes only
the destination prefix. The cost bound is
`offset*(12*w+9)+count*(16*w+9)+29`; it contains no ambient-prefix traversal.
The generic proof handles arbitrary intervals, headers, source/destination
suffixes, zero lengths and register placements.

`preparedCorePublication_exec` is its first geometry consumer. It publishes
`ownedCoreWords`, and transports the input halo's actual physical-read error
to the actual published core prefix. Both readers decode the same words, so
this step needs neither another fit premise nor another rounding allowance.
The core error remains the halo error, with no cell-count factor.

`packedHaloSolve_spec` now exports the retained word-width and the two native
scratch facts needed for publication. `packedHaloPublication_exec` embeds an
actual execution of `packedHaloSolve` in a 256-register bank beside eight
publication registers and runs the prepared core publisher on its returned
buffer. It proves the exact published prefix, preservation of the local halo
source, preservation of all other added registers and accuracy on the actual
published core reads. Its premise is an execution of the concrete local solver,
with the source/error/width facts returned by that solver; it is an execution
composition theorem, not a generated group theorem.

The prepared slice checked at 2080.4 MiB, owned-core specialization at
2041.5 MiB, strengthened local solver at 3288.2 MiB and execution composition at
3227.4 MiB. The combined axiom audit passed (14938 jobs, 3.4 GiB aggregate
peak); whitespace validation passed. Connecting generated descriptor/header preparation, the restoring
gather, repeated calls and ordered core publication remains open. The current
self-contained solver also does not supply complete-key setup reuse. Runtime
restoration, seam dispatch, normalized complex/tensor composition and selected
global time/live-storage bounds remain open; S4 remains open.

`PackedHaloInput` now packages the existing 54 geometry, numerical-format and
physical-workspace preconditions of the local solver. It adds no execution
premise or intermediate numerical oracle. `PackedHaloInput.run` instantiates
the concrete solver once from that record, returning the fields needed by
subsequent local callers. This avoids repeating the full register-level
hypothesis list in every composition proof.

`packedHaloCore_spec` now executes setup, both interior passes, boundary solve,
all proved page disposals and owned-core publication from this input contract.
It invokes the solver itself, so an intermediate execution is no longer a
caller premise. It returns the published core prefix and its actual-read
accuracy, fitting, user/caller-stream preservation, publication-header frames
and the sum of the local solve and generated-count publication costs.

The publication composition now returns equality of the entire embedded solved
bank. The publisher modifies only its new destination, so all local solver
postconditions can be transported through one view equality. Explicit shared
precision/width aliases and a separate input runner keep elaboration below
default limits; no heartbeat or recursion setting was raised.

The input contract checked at 3216.9 MiB, solver adapter at 3216.7 MiB,
strengthened publication frame at 3228.0 MiB and the direct core caller at
3231.5 MiB. The combined execution/axiom audit passed (14941 jobs, 3.5 GiB
aggregate peak); whitespace validation passed. This is a concrete local
nonseam real core call from the existing initial workspace contract. Generated
descriptor/header construction and gathering into that contract, repeated-call
runtime restoration, the complete group schedule, seam dispatch, complete-key
setup reuse, normalized complex/tensor composition and selected global
time/live-storage bounds remain open. S4 remains open.

Recovery now exports ownership of the remaining source prefix on 110:
a recovery-RHS block of `(b-a)*w` symbols, followed by the original local RHS
and its borrowed suffix. The fact comes from the second interior solver's
actual native-bank projection. The local solver, shared input runner and
core publication caller retain it, together with the word width and released
104/105/109 scratch. Publication's whole-bank view transports all these facts
without another numerical argument.

`haloBufferRelease_exec` generates the halo row count from the borrowed core
length and radius headers, then reuses `retireCountedLine` three times: once
for the local solution on 132 and twice for the RHS prefixes on 110. It clears
its generated counter on 255. Its exact poststate changes only 132 and 110 to
their borrowed suffixes; published cores, other stacks and original header
symbols are preserved. Its cost is local in core length, radius and word width,
including count generation and disposal. No scaled counter tape is assumed.

`packedHaloCoreRelease_spec` invokes the concrete setup-to-core caller and then
this disposal program. It returns the actual published core and its uniform
accuracy, fitting, stream/header frames, restored output/RHS suffixes and an
empty temporary halo counter. All runtime costs through this buffer lifecycle
are included. It does not restore every low/new-bank setup header or establish
factor reuse between calls.

The strengthened recovery checked at 3251.6 MiB, cleanup at 1945.2 MiB,
cleanup-ready core caller at 3234.3 MiB and complete core/buffer-disposal caller
at 3235.0 MiB. The combined execution/axiom audit passed (14943 jobs, 3.5 GiB
aggregate peak). The strengthened local solver and input adapter also passed
guarded checks at 3290.3 and 3223.7 MiB, respectively; whitespace validation
passed. Generated gathering/initialization, complete repeated-call
restoration and scheduling, seam dispatch, complete-key setup reuse, normalized
complex/tensor composition and selected global time/live-storage bounds remain
open. S4 remains open.

The input contract now separates `PackedHaloFrame` (the 51 setup, geometry and
source facts) from the three output-buffer facts in `PackedHaloInput`.
`packedBoundaryFactoryView_update_output` proves that the physical local output
lies outside the routed factory view. `PackedHaloFrame.update_output` therefore
preserves the setup contract during allocation, and `.with_output` combines
that frame with a proved length and encoded range. Existing solver callers
retain their inherited input-field API.

`allocateZeroLine_exec` reuses unary dimension multiplication and constant-symbol
copying to allocate exactly `N*w` zero symbols over an arbitrary output suffix,
restoring its controls. `encodedRange_zero_words` supplies the numerical range
for every precision/exponent. `prepareHaloBuffer_exec` obtains `w = 2*q+8` from
the retained precision header and `N = coreLength+2*radius` from the borrowed
publication headers, allocates this output and clears all private dimensions.
Its exact frame changes only port 132; every preparation cost is included.

`prepareHaloBuffer_input` derives precision and native scratch from the setup
frame, aligns the original and normalized working widths via the shared-format
identity, and proves that the actual allocated poststate satisfies
`PackedHaloInput`. `Host.extendStacks_updateR` transports this allocation across
workspace extension once. No preallocated output, range certificate or scaled
allocation counter is supplied by the caller.

`preparedHaloCore_spec` now runs allocation, the concrete core solver,
publication and owned-page/buffer disposal from `PackedHaloFrame`. It returns
the published core and actual-read accuracy, fitting, caller streams, the
original output suffix on 132, the RHS suffix on 110, and publication-header
frames. Its total bound includes allocation. This begins with the existing
setup/source frame and core/radius masters; generated gathering and initial
header construction are still separate obligations.

The frame transport checked at 3220.1 MiB, zero allocator at 1954.3 MiB,
allocation program at 1940.1 MiB, executed input initializer at 3236.0 MiB and
combined initialized core caller at 3242.6 MiB. The combined execution/axiom
audit passed (14948 jobs, 3.5 GiB aggregate peak). Workspace extension and the
refactored input/runner modules also passed guarded checks at 1389.9, 3216.0
and 3218.8 MiB, respectively; whitespace validation passed. Complete repeated-call
restoration, generated grouping/gathering/header execution, seam dispatch,
complete-key setup reuse, normalized complex/tensor composition and selected
global time/live-storage bounds remain open. S4 remains open.

### Generated core counted origins (2026-10-29)

`countedOriginListHost_exec` now factors the executed origin publisher over an
arbitrary list emitted by a verified table program. It scans fixed-width words
to derive the unary count, publishes their binary real coordinates, preserves
the borrowed output suffix and off-bank frame, and retains the bound
`steps*tblC W V + origins.length*(8*V+6)+6`. The halo length-group host is a
specialization of this same proof.

`generatedCoreCountedHost_exec` instantiates it with `generatedCoreGatherCode`:
the machine computes the core count from ambient size and core width, filters
fitting halos by movement length, and emits the coordinate origins and their
owned count. Neither the origin list nor its count is an input. This is a
movement interface, not numerical setup reuse. Converting these origins to
restoring-gather controls, constructing the full local solver frame, restoring
the runtime bank across calls, setup reuse, seams, tensor composition and the
uniform resource bounds remain open. S4 remains open.

Verification: the new generic and core modules checked at 1980.2 MiB and
1955.7 MiB peak RSS. The coupling-interval build passed 14,952 jobs and its
approved-axiom audit (10.9 GiB aggregate peak); `git diff --check` passed.

### Executed generated core sweep (2026-10-29)

`preparedOriginAdvanceControls_exec` now prepares and releases the advance table
for an arbitrary ordered origin list. It restores every register except the
control destination, including the binary origins, their unary count, borrowed
width headers and conversion scratch. Its movement bound uses the structural
`originAdvances_sum_le` lemma, so total emitted movement is at most one ambient
line. The halo converter is a specialization of this proof.

`preparedCoreAdvanceControls_exec` instantiates that interface with the core
geometry and proves the exact `windowAdvances` controls used by the restoring
gather. `generatedCoreControls_exec` then composes the actual core enumeration,
counted publication, origin-table release and advance conversion. It assumes
native scalar table headers, not an origin list or count.

`generatedCoreGather_exec` connects that program to `coreGather_exec`: the
machine emits the concatenated fitting halo slices on register 108, preserving
the ambient source on 110 and all other caller data outside the released table
and the owned origin/count/control streams. For packed ambient input,
`coreGather_packed` identifies these slices with the packed local intervals.
The cost is the generated-control cost plus the existing one-sweep gather bound;
there is no per-halo ambient traversal. Empty groups remain a separate branch.

Constructing the native table from retained binary geometry, routing the gathered
words into the real solver frame, repeated-call restoration, complete setup-key
reuse, seam dispatch, tensor composition and uniform time/live-storage bounds
remain open. S4 remains open.

Verification: the generic converter, core converter, generated controls and
generated gather checked at 2089.1, 2065.3, 2082.3 and 2082.4 MiB peak RSS.
The coupling-interval build passed 14,957 jobs and its approved-axiom audit
(10.4 GiB aggregate peak); `git diff --check` passed.

### Initialized core sweep from retained geometry (2026-10-29)

`preparedCoreGather_exec` loads the real core controller table from retained
binary ambient size (145), core width (150), radius (152), halo length (165),
empty zero source (154), and unary binary-word width (163). It embeds the
previous generated sweep into the 168-register bank and restores the entire
controller table to its initial blank contents. The loader cost is
`112*V+137`; all retained geometry and the ambient source restore exactly.

`prepareCoreGatherHeaders_exec` copies the unary workspace-width header and
decodes the retained binary halo length using the existing structural
`toUnary_exec_linear` proof. `initializedCoreGather_exec` composes that header
construction, table loading, origin enumeration, movement conversion and the
restoring gather, then retires both temporary unary headers. Its only changed
registers are the gathered batch (108), generated controls (91), binary origins
(109) and emitted count (116); all left stacks, retained headers, ambient input
and unrelated caller data restore. The complete explicit cost is
`initializedCoreGatherCost`.

`initializedCoreGather_packed_exec` identifies the executed batch with the
concatenation of packed fitting halo intervals of the ambient Gaussian line.
Neither initialized table state, origin/control streams, a supplied group count,
nor the temporary unary halo-length/workspace-width headers are input oracles.
The scalar word-width counter and retained binary geometry are still inputs.

Routing this batch into the actual local solver frame and consuming its owned
origin/count/control streams remain next integration steps. Repeated-call solver
restoration, complete setup-key reuse, seams/full-system fallback, tensor
composition and final uniform time/live-storage bounds remain open. S4 remains
open.

Verification: the loader/sweep, unary-header constructor and initialized packed
sweep checked at 2108.9, 1929.7 and 2098.8 MiB peak RSS. The coupling-interval
build passed 14,960 jobs and its approved-axiom audit (3.4 GiB aggregate peak);
`git diff --check` passed.

### Executed queued halo attachment (2026-10-29)

`PackedHaloSetup` separates numerical/header readiness from the local RHS
prefix. `PackedHaloFrame` adds the actual source equation; its previous
`hready` interface follows from these two facts. Source replacement transports
the setup structurally through the existing injective register embeddings, and
output initialization preserves this split contract.

`takeCountedLine_exec` consumes one packed line from an arbitrary queue using
retained row and word-width counters. It preserves symbol order, appends the
line before the borrowed destination suffix, restores all scratch/count ports,
and pays `rows*(12*wordWidth+9)+12`.

`attachQueuedHalo_exec` derives both counters from retained binary halo length
and precision, consumes the next halo from queue 256 into source 110, and
retires every temporary control. `attachQueuedHalo_frame` derives precision and
scratch readiness from `PackedHaloSetup`, proves the transferred words have the
required physical length, and constructs the actual solver frame. The ambient
source stays as the borrowed suffix, so the existing local solver's buffer
release can restore it without a separate source copy. The unconsumed queue and
all unrelated registers are preserved.

This establishes an executed queue-to-frame bridge. Composing it with the real
local core execution, connecting generated gathering to this queue placement,
full repeated-call runtime restoration, complete setup-key reuse, seams,
tensor composition and uniform final resource bounds remain open. S4 remains
open.

Verification: the source-independent input, source transport and executed
queue-to-frame bridge checked at 3222.3, 3225.5 and 3232.0 MiB peak RSS. Explicit
builds of every accumulated changed Lean module passed: 15,135 jobs for the
foundational dependency closure and 15,443 jobs for the remaining modules,
including the approved core-setup, packed-coupling and coupling-interval axiom
audits. The guarded aggregate peaks were 37.3 and 35.0 GiB. New-file trailing
whitespace was removed before committing; staged whitespace checks passed.

### Concrete queued core execution (2026-10-29)

`queuedHaloCore_spec` now composes the executed queued-halo attachment with
`preparedHaloCore_spec`, including output allocation, both interior passes,
boundary solve/recovery, publication and local buffer/factor disposal. It
consumes exactly the first packed halo from queue 256, publishes the owned core
on 248 with the existing physical-read error bound, restores the borrowed
ambient source on 110 and output suffix on 132, and preserves the remaining
queue and every added header outside the published output and consumed queue.
The radius/core publication headers and added attachment counters restore. Its time
bound is the sum of attachment and concrete local-core costs; no local-solver
execution callback is assumed.

The caller still establishes the source-independent numerical/header setup and
the halo's binary coordinate fields. Connecting the generated group to queue
placement and repeated setup/header construction, restoring the complete low
runtime bank across calls, complete setup-key reuse, seams/full-system fallback,
complex/tensor composition and final uniform bounds remain open. S4 remains
open.

Verification: `queuedHaloCore_spec` checked at 3246.7 MiB peak RSS. The
coupling-interval integration build passed 14,965 jobs and its approved-axiom
audit (5.1 GiB aggregate peak); whitespace checks passed.

### Protected direct queue gathering (2026-10-29)

`queuedCoreGather_spec` places the initialized core sweep through any injective
register map. The generic `writeRight`/`embOvr_writeRight_view` law transports
its finite output writes structurally. The spent movement-control stream is
retired, leaving exactly the batch, origin stream and generated count as output
writes. `coreGatherControls_length_le` pays that retirement with at most one
ambient line's movement and one delimiter per origin; it introduces no ambient
traversal per halo.

`protectedCoreGather_spec` instantiates the shared execution proof with an
injective placement built from swaps. The batch is generated directly on queue
256, origins on 257 and the group count on 261. Retained ambient/core/radius
geometry uses external ports 264/265/266, the empty binary zero source uses 268,
and the temporary word width uses 267. Word width is generated from retained
precision rather than assumed on a native scratch register. Both temporary
word width and spent movement controls return blank, all external geometry
sources restore, and every native solver register below 256 restores exactly.
There is no second copy of the gathered batch into the solver queue.

This removes the gather/solver register conflict. Composing the protected sweep
with concrete queued calls, consuming origin/count streams and constructing
successive local geometry, complete low-runtime restoration between calls,
complete setup-key reuse, seams/full-system fallback, complex/tensor composition
and final uniform time/live-storage bounds remain open. S4 remains open.

Verification: right-write transport, core movement/control bounds, generic
queue placement and protected gathering checked at 1388.8, 2063.4, 2084.9 and
2100.7 MiB peak RSS. The coupling-interval integration build passed 14,968 jobs
and its approved-axiom audit (3.4 GiB aggregate peak); whitespace checks passed.

### Generated batch to concrete first-core execution (2026-10-29)

`ProtectedCoreGatherInput` packages only scalar bounds, ordinary source/header
contents and blank workspace facts; its `run` theorem invokes the existing
executed gather rather than taking an execution premise.

`gatheredHaloCore_spec` now composes protected generation and gathering with the
actual queued solver/publication. For a generated fitting group whose first
index is `k`, the physical batch on 256 supplies the first halo RHS. The machine
solves and publishes core `k` on 248 with the existing physical-read error,
restores the borrowed ambient source and output suffix, and leaves exactly the
remaining generated halo windows on 256. Geometry/working-format matching and
native-bank preservation are proved through the composition; no gathered
source or local execution callback is assumed.

The caller establishes the source-independent numerical/header frame with its
three owned coordinate slots canonically overlaid, and supplies those slots
blank. The executed program now constructs the first local coordinate headers.
The generated RHS, origin stream and count
on 256/257/261 now all advance to the remaining indices `ks`. Generating
successive local geometry, complete low-runtime restoration for repeated calls,
full setup-key reuse, seams/full-system fallback, complex/tensor composition and
final uniform bounds remain open. This is a generated batch connected to its
first real local call, not a completed group loop. S4 remains open.

Verification: the protected gather contract and composed generated-core
execution checked at 2067.8 and 3250.1 MiB peak RSS. The coupling-interval
integration build passed 14,970 jobs and its approved-axiom audit (3.5 GiB
aggregate peak); whitespace checks passed.

### Synchronized generated group cursors (2026-10-29)

This discard-only step was superseded by the first-halo header constructor below.

`advanceGroupCursor_exec` is a generic five-register proof: consume one
fixed-width binary origin word and one tick of its unary count, restoring both
scratch stacks and all other state, in exactly `6*V+7` steps. It reuses the
structural counted-prefix disposal proof.

`gatheredHaloCore_spec` executes this advancement between protected gathering
and the first concrete solver call. Scratch ports 269/270 lie outside the solver
bank. The remaining RHS windows, binary origins and unary count are now all
indexed by `ks`, including when `ks` is empty. The borrowed source, published
core accuracy, high-header frame and other previous guarantees are retained.
This closes cursor alignment; local-header construction and the complete
runtime invariant for repeated calls remain open, along with the other S4 gates.

Verification: the generic cursor step and cursor-aligned gathered-core theorem
checked at 1931.9 and 3252.7 MiB peak RSS. The coupling-interval integration
build passed 14,971 jobs and its approved-axiom audit (3.5 GiB aggregate peak);
whitespace checks passed.

### Executed first-halo coordinate headers (2026-10-29)

`prepareHaloHeaders_exec` reuses `takeBinaryUnaryKey_exec`, unary copy and the
structural binary-to-unary decoder. Starting with blank owned slots, it consumes
the generated origin word, retains that binary origin, constructs unary lower
and upper coordinate masters from the origin and retained binary halo length,
and advances the unary group count. All scratch stacks and borrowed headers
restore. The bound is `10*a+6*L+28*V+23`.

`haloHeaderBank` describes the input frame with only these three owned slots
canonically overlaid. Readiness on that view does not require their values in
the incoming physical bank: the constructor establishes the exact view by
execution. Generic embedding/extension laws for `haloHeaderR` transport the
three writes without repeating numerical readiness proofs.

`gatheredHaloCore_spec` now runs this construction between generation/gathering
and the first concrete solve. Binary origin 155 and unary coordinate masters
141/142 are no longer supplied initialized by the caller. RHS, origin and count
queues remain synchronized on the remaining indices after publication. This is
first-entry initialization, paid once per group; subsequent cores must advance
retained masters monotonically rather than rebuild unary absolute coordinates.
The repeated-call runtime, successive geometry, setup reuse, seams, complex and
tensor composition, and uniform final bounds remain open. S4 remains open.

The superseded discard-only cursor helper can be restored from `86c84f13`.

Verification: the header constructor/transport module and composed first-core
execution checked at 1956.5 and 3276.2 MiB peak RSS. The coupling-interval
integration build passed 14,971 jobs and its approved-axiom audit (3.5 GiB
aggregate peak); whitespace checks passed.

### Executed shared group dimensions (2026-10-29)

`prepareCoreDimensions_exec` constructs the unary radius and core-length
masters from retained binary radius and halo length. It decodes each binary
header once, then removes the two radius margins from the decoded halo count,
restoring all scratch and both binary sources. The cost is
`6*L+18*radius+22*V+24`.

`gatheredHaloCore_spec` now executes this preparation once after generation and
before coordinate initialization. It obtains `L = coreLength + 2*radius` from
the generated group's membership specification. Registers 249/250 are supplied
blank, not as initialized unary inputs; the executed output retains their exact
tick streams after the real local solve. These shared dimensions are available
for later group entries without reconstruction. The borrowed source,
publication accuracy and synchronized remaining queues are unchanged.

The repeated-call runtime invariant, monotone coordinate updates, full setup-key
reuse, seams/full-system fallback, complex/tensor composition and final uniform
bounds remain open. S4 remains open.

Verification: the shared-dimension constructor and composed core execution
checked at 1944.2 and 3290.9 MiB peak RSS. The coupling-interval integration
build passed 14,972 jobs and its approved-axiom audit (3.5 GiB aggregate peak);
whitespace checks passed.

### Retained numeric and geometry headers after real calls (2026-10-29)

The recovery frame now exposes the union of the existing numeric master ports,
binary interval-geometry ports and private retained runtime roles. A small
placement check verifies those physical ports once. The generic
`packedRecoveryRetained_frame` transports the existing placed execution frame;
its proof is isolated from numerical state to avoid elaborating the full solve
while proving register equalities.

`PackedHaloRetainedHeaders` packages the numeric masters, binary geometry,
stage and level, with a structural frame rule. The record is now returned by
the closed local solver and carried through publication, buffer retirement,
queued execution and `gatheredHaloCore_spec`. In particular, the actual output
still supplies the lower/upper coordinate-master lengths and binary origin,
interval length and workspace width. The executable programs and charged costs
are unchanged. This is the retained data needed for monotone coordinate updates
and reusing already constructed ambient geometry.

This does not yet restore the complete low/native runtime or establish the
next local call's setup predicate. Those invariants, monotone updates, full
setup-key reuse, seams/full-system fallback, complex/tensor composition and
final uniform bounds remain open. S4 remains open.

Verification: the integration build passed 14,973 jobs and its approved-axiom
audit. Guarded single-file checks peaked at 2130.5 MiB for the shared frame,
2186.2 MiB for recovery, 3294.8 MiB for the solver and 3286.6 MiB for the
gathered core, all below the 4 GiB module budget.

### Native scratch restoration after boundary recovery (2026-10-29)

`packedBoundaryRecovery_spec` now exposes the structural native postcondition:
every right register below 117 is empty except width register 93 and source
register 110. This includes the consumed iteration register 116. The proof
projects the existing `PackedHaloReady.native` equality once for an arbitrary
register, rather than reducing it to eight selected release slots. The solver's
release interface derives those eight slots from this stronger postcondition.
The executed program and its costs are unchanged. Transporting the full native
invariant through disposal, publication and buffer retirement remains necessary
before establishing readiness for the next core; this is not yet a group loop.
The integration build passed 14,973 jobs and its approved-axiom audit; the
guarded recovery check peaked at 3247.3 MiB.

### Native scratch through the closed generated core (2026-10-29)

`PackedHaloNativeClean` names the native right-scratch invariant, retaining only
width register 93 and borrowed source register 110. The closed solver transports
recovery's arbitrary-register proof through coefficient, table and factor
retirement. The publication, buffer-retirement, prepared, queued and gathered
core specifications now return the same invariant on their native prefix views.
Placed calls reuse their existing exact projection equalities; buffer retirement
only changes output 132 and the exempt source 110. No executable operation or
charged cost changes.

Thus the generated first-core output now exposes both native scratch and the
retained numeric/geometry headers. This still does not establish the next
`PackedHaloSetup`: runtime workspace roles, coordinate advancement, geometry
updates and complete setup-key reuse remain to be composed. The generated group
loop and the other global S4 obligations remain open.
Verification: the 14,973-job integration build and approved-axiom audit passed.
Guarded single-file checks peaked at 3309.1 MiB for the solver and
3288.7 MiB for the gathered core.

### Binary-difference advancement of retained masters (2026-10-29)

`advanceHaloMasters` subtracts the retained binary origin from the next binary
origin, converts the difference twice and prepends those ticks to the two unary
coordinate masters. It then clears its difference word. Its generic execution
theorem preserves every other stack, including both input words and arbitrary
endpoint suffixes, and restores all four scratch stacks. The charged bound is
`12*(next-old)+32*V+22`; it never scans the existing unary coordinates.
`advanceUnaryPair` factors the shared conversion proof over arbitrary registers.

Ordered generated origins justify nonnegative movement; the sum of the decoded
differences can therefore be charged to total movement rather than the sum of
absolute origins. The new primitive does not yet consume the next generated
origin packet, install that binary origin or update the remaining interval
metadata. Those bridges and the full group loop remain open, as do complete
setup reuse and the remaining global S4 obligations.
Verification: the guarded single-file check peaked at 1407.8 MiB. The
14,974-job integration build and approved-axiom audit passed.

### Consume ordered origins while advancing coordinate headers (2026-10-29)

`advanceHaloHeaders` now takes the next fixed-width binary origin from its
queue, advances both retained unary endpoint stacks using `advanceHaloMasters`,
replaces the old retained binary origin and consumes one unary group-count tick.
Its generic poststate changes exactly those five registers and restores every
temporary stack, preserving arbitrary queue/count suffixes and endpoint contents.
The bound is `12*(next-old)+46*V+37`; absolute unary origins are never rebuilt.
Two uses of the existing `takePrefix` preserve the binary packet order.

This is the executable cursor/header step for successive generated cores. It
still needs placement into the gathered-core ABI and propagation of the updated
interval metadata. Next-call setup readiness, factor/setup reuse, the full loop
and the remaining global S4 obligations are still open.
Verification: the guarded module check passed without warnings at 1961.2 MiB
peak RSS. The 14,975-job integration build and approved-axiom audit passed.

### Generated-core placement and amortized coordinate movement (2026-10-29)

`advanceQueuedHaloHeaders` specializes the generic packet/header step to the
272-register generated-core ABI: width 163, origin queue 257, retained origin
155, endpoint masters 141/142 and group count 261. It borrows native scratch
104/105 and high scratch 269--271, restoring them all; no new register bank is
allocated. Its theorem consumes the native-clean invariant already returned by
`gatheredHaloCore_spec`. The explicit poststate has a five-slot frame theorem,
transports `CouplingMasterHeaders` from `[x,x+L]` to `[y,y+L]` and preserves
native cleanliness. Arbitrary endpoint symbols and queue suffixes remain valid.

`haloHeaderSweepCost_le` proves the structural ordered-list bound
`12*(s-x)+count*(46*V+37)`. Thus only packet-width work is charged per origin;
unary work is charged once to total forward movement. The proof applies to
arbitrary ordered origins and instantiates generated geometry last.

Interval metadata still needs its translated binary endpoint words before the
next solver call. The full group loop, next-call workspace readiness, complete
setup reuse and all remaining global S4 obligations remain open.
Verification: guarded checks peaked at 1967.7 MiB for the generic sweep bound
and 2119.7 MiB for its concrete placement. The 14,976-job integration build
and approved-axiom audit passed.

### Structural binary translation for retained halo endpoints (2026-10-29)

`translateBinaryWords_exec` proves one structural execution theorem over an
arbitrary list of distinct binary words, with a shared encoded displacement.
The existing binary adder updates each target once, preserves the displacement
and restores the three shared scratch stacks. Nonoverflow bounds discharge the
modular arithmetic, and a structural `writeRight` list describes the exact
poststate. Its exact time is `count*(8*V+8)+1`.

`translateHaloEndpoints_exec` instantiates that language for physical words
149,151,156,164 on the generated-core ABI. Given the movement `y-x` on 104, it
translates the old lower/upper/interval-end/extended-end words to the new ones in
exactly `32*V+33` steps. All other stacks, including the already installed origin
155 and retained ambient geometry, stay unchanged. This avoids rebuilding unary
ambient dimensions and avoids four independent arithmetic proofs.

The displacement must still be computed from retained old/new origins and
cleared after this operation. That composition, the full metadata invariant,
next-call workspace readiness, setup reuse and the full generated loop remain
open along with the other global S4 obligations.
Verification: guarded checks peaked at 1404.0 MiB for the generic translator
and 1395.8 MiB for the endpoint instance. The 14,978-job integration build
and approved-axiom audit passed.

### Executed advancement restores complete interval metadata (2026-10-29)

`refreshHaloEndpoints_exec` now computes the movement from the installed origin
155 and retained old lower endpoint 149, runs the structural four-word
translation and clears the displacement word 104. Its exact cost is `42*V+43`;
its exact poststate changes only the four coordinate-dependent geometry words.

`advanceHaloMetadata_exec` composes the real origin-queue/header step with this
refresh. It starts with ordinary retained interval metadata, a next-origin
packet, the group count and native/high scratch readiness. It consumes the
packet/count, advances both unary endpoints and all translated binary endpoint
words, and returns the complete `CouplingIntervalMetadata` record for the new
interval. Ambient dimensions, band and local length are retained. The cost is
`advanceHaloHeadersCost V (y-x)+42*V+43`, so unary work still depends only on
movement. `advancedHaloMetadata_geometry` isolates the fixed-layout metadata
proof from execution and numerical solver state.

Next-call workspace readiness, complete setup-key/factor reuse, the generated
core loop and remaining global S4 obligations are still open.
Verification: guarded single-file checks peaked at 1401.3 MiB for endpoint
refresh and 2123.9 MiB for complete metadata advancement. The 14,980-job
integration build and approved-axiom audit passed.

### Reusable postcondition for executed halo metadata advancement (2026-10-29)

The structural right-write language now has `writeRight_R_off`, a generic
spectator-stack rule. `advancedHaloMetadata_frame` uses it to expose the nine
owned coordinate/cursor slots of the complete advancement; all other right
stacks retain their contents. The native scratch proof uses this frame for an
arbitrary low register, without enumerating numerical states.

`advancedHaloMetadata_headers` transports the complete retained-header record:
precision, stage, level, numeric masters and binary interval geometry, with the
new lower/upper coordinates. `advanceHaloMetadata_spec` now returns that record,
native cleanliness, restored high scratch and the exact final state from the
actual execution. This gives subsequent composition one reusable contract.
The program and charged cost are unchanged.

This does not restore the solver's remaining workspace protocol or resolve its
fresh-geometry setup assumption. Those invariants, complete setup reuse, the
full generated loop and remaining global S4 obligations are still open.
Verification: guarded checks peaked at 1386.4 MiB for the write-frame helper
and 2133.7 MiB for the complete metadata contract. The 14,980-job integration
build and approved-axiom audit passed.

### Factor-factory entry with retained geometry (2026-10-29)

`routedPackedBoundaryFactoryRetainedGeometry_spec` runs the existing
`routedPackedBoundaryFactoryRelease` with an already populated interval geometry
bank. Its output includes the same numerical factor, stock, table, native and
buffer guarantees as the initializing entry, and preserves the full geometry
record using the factory's existing retained-header frame. It omits the
geometry-initializer program and the charge
`(s+t+band+a+b)*(4*V+10)+56*V+77`. No blank-geometry premise is required.

`CouplingIntervalMetadata.of_frame` factors the geometry transport once and is
also used by the retained-header record's frame rule. The retained factory entry
reuses the original executed numerical theorem, rather than duplicating its
construction or assuming a numerical execution callback.

This entry still constructs fresh factors. Threading it through the boundary
solve and closed-call interfaces, restoring other workspace roles, complete
setup/factor reuse and the generated group loop remain open, along with the
other global S4 obligations.
Verification: the retained factory module checked at 3203.5 MiB peak RSS.
The 14,981-job integration build and approved-axiom audit passed.

### Shared boundary-setup proof for fresh and retained geometry (2026-10-29)

`packedBoundaryFactoryGeometryUsing_spec` gives both geometry entries one
execution interface, with a conditional blank-bank/retained-metadata premise
and the corresponding initialization charge. Its two branches instantiate the
existing closed factory theorems; neither supplies a numerical callback.
`packedHaloBoundarySetupUsing_exec` now proves the complete factor/RHS setup
once over that interface. Retained mode executes the factor supplier directly,
then the same real boundary-data producer, preserving all numerical accuracy,
stock, workspace and header guarantees while omitting geometry initialization.

The original `packedHaloBoundarySetup_exec` is a short proof specializing this
shared theorem to fresh geometry, so existing callers retain their interface.
The existing RHS/accuracy proof is not duplicated. Closed boundary-solve/recovery
interfaces must still expose the retained mode. Other workspace restoration,
complete factor/setup reuse, the generated loop and remaining S4 obligations
remain open; retained geometry alone does not imply factor reuse.
Verification: guarded checks peaked at 3207.5 MiB for the factory-mode interface
and 3351.3 MiB for shared boundary setup. The 14,982-job integration build
and approved-axiom audit passed.

### Retained geometry through the closed local solver (2026-10-29)

`packedHaloBoundarySolveUsing_exec` now carries the fresh/retained geometry mode
through the actual prepared residual solve, using the shared setup theorem.
`packedHaloSolveUsing_spec` carries it through boundary solution, interior
recovery and all coefficient/table/factor releases. Retained mode accepts the
already translated interval metadata instead of blank geometry slots, skips
geometry initialization, and returns the same physical-read accuracy, retained
headers, native cleanliness, buffer and owned-page guarantees. The residual,
accuracy and recovery proofs are shared across both modes.

`packedHaloSolveUsingCost` records the mode-dependent charge once. The original
programs, cost function and theorem interfaces specialize the shared definitions
to fresh geometry, preserving existing callers. Retained mode removes the
ambient/unary geometry-initialization term; it still constructs and releases
fresh factors. Publication/queue interfaces still need the retained mode and the
remaining workspace invariants before successive calls can be composed.
Complete setup-key/factor reuse, the full group loop and other global S4
obligations remain open.
Verification: guarded checks peaked at 3270.0 MiB for boundary solve and
3313.6 MiB for the closed solver. The 14,982-job integration build and
approved-axiom audit passed.

### Shared call records and frame rules for both geometry modes (2026-10-29)

`PackedHaloSetup`, `PackedHaloFrame` and `PackedHaloInput` now carry an optional
geometry mode, defaulting to the original fresh entry. All numerical/workspace
fields remain shared; only `PackedHaloGeometryInput` distinguishes a blank bank
from retained metadata. Its structural frame rule transports either form using
one physical geometry-bank frame. Source attachment and output allocation now
preserve both modes through the existing setup/frame constructors.

`PackedHaloInput.runUsing` executes the corresponding closed solver directly
from that record. The original `run` specializes it to fresh mode. The records
still contain ordinary mathematical/input/workspace facts, with no assumed
numerical intermediate or execution callback. This supplies the shared proof
language needed for retained publication and queued-call interfaces without
copying the setup record or its transport proofs.

Publication/queue mode propagation, remaining next-call workspace restoration,
complete setup-key/factor reuse, the generated loop and the remaining global
S4 obligations remain open.
Verification: guarded checks for the four changed contract/frame modules peaked
at 3223.0, 3224.5, 3228.0 and 3225.8 MiB respectively. The 14,982-job
integration build and approved-axiom audit passed.

### Retained geometry through publication and queued core execution (2026-10-29)

`packedHaloPublicationUsing_exec`, `packedHaloCoreUsing_spec` and
`packedHaloCoreReleaseUsing_spec` now share publication, physical-read error
restriction and owned-buffer retirement across geometry modes. The actual
retained-mode solver runs from `PackedHaloInput`, publishes only the owned core
and restores the borrowed source/output suffixes. Native cleanliness and retained
numeric/geometry headers reach the released output in both modes.

The zero-allocation and queue-attachment frame theorems are mode-polymorphic.
`preparedHaloCoreUsing_spec` and `queuedHaloCoreUsing_spec` compose them with the
closed publication/release path. The latter consumes an actual queued packed
RHS and returns the remaining queue with the original source restored. The old
program/theorem names specialize the shared path to fresh geometry, and costs
use `packedHaloSolveUsingCost`; numerical, publication and frame proofs are not
duplicated.

This establishes the queued retained-mode call from its ordinary setup record;
it does not construct that record from a preceding call's complete workspace.
That restoration, complete setup-key/factor reuse, generated group iteration and
remaining global S4 obligations remain open.
Verification: all seven changed call/frame modules passed guarded checks, with
peaks from 3230.3 to 3251.9 MiB. The 14,982-job integration build and
approved-axiom audit passed.

### Checked protection of geometry from factory scratch (2026-10-29)

The readiness audit exposed a physical alias in the unprotected factory entry.
A guarded diagnostic proved the old retained setup forces zero word width.
The protecting permutation now maps `[147,148,149,150,151]` to
`[158,159,160,161,162]`. These destinations are outside the interval metadata
bank. One closed placement check identifies the preimages of all geometry
ports; a generic projection/frame argument proves that the existing factory
header frame preserves actual retained geometry under the permutation.

The protected factory program is defined, but its execution theorem and the
readiness/mode interfaces still require integration. This corrects a substantive
gap in the earlier retained-mode milestones rather than closing the successive
call invariant. Complete setup reuse, iteration and global bounds remain open.
Verification: the protecting-placement module checked at 3189.4 MiB peak RSS;
the separate overlap diagnostic checked at 3186.1 MiB. The 14,983-job
integration build and approved-axiom audit passed.

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


The integer-column generator and runtime encoder are now composed in
`ScalarPlacement.generateEncodedColumn_exec`: one executed 117-tape program
starts from the retained factor page and ordinary headers, initializes and
iterates the integer column, generates/releases encoding counters, and emits
runtime column words on tape 111. It retains the signed raw column, factor page
and arbitrary borrowed suffixes. The combined bound is
`prepareCost 0 W + M*(integerIterationCost L W+5) + L*(30*W+6*(2*q+8)+32) +31*W+6*P+79`.
At M=j+1 the emitted words have inverse-column error at most 2^-j when j+2≤q.
Factor-page generation, reciprocal/reversed-branch encoding, final sizing
headers and combined setup storage/uniform costs remain open; S3 is incomplete.


The second generator no longer needs a supplied reversed word bank:
`generateReversedColumn_exec` constructs `reversedColumnWords` on tape 113
from the encoded first column on tape 111. It saves/restores the head word,
reuses the structural coefficient-word reversal, and prepends zero. Both
borrowed suffixes and all other tapes are restored. Length/word counters are
generated from retained L/q headers and released; the exact cost is
`(L-1)*(16*(2*q+8)+21)+4*L+12*(2*q+8)+4*q+31` for L>0.
Signed decoding and error ≤2^-j are proved at iteration j+2, q≥j+2.
The guarded S3 audit passes 4478 jobs at 2.6 GiB combined peak.
Reciprocal encoding, factor-page generation, final sizing and combined
setup/cost/storage remain open, as do the outer full-line S3 obligations.


The inverse-generator setup is now composed end to end from the retained factor
page: `ScalarPlacement.generateGenerators_exec` initializes and iterates the
integer column, emits the first runtime generator on tape 111, constructs the
shifted reverse on tape 113, and computes the reciprocal on tape 96. It generates
`2^(q+P*n)` from ordinary headers, copies the positive signed corner into the
existing binary restoring divider, converts and crops the quotient to runtime
width, and releases numerator, binary workspace and counters. The raw column,
factor page and borrowed suffixes remain explicit and preserved.
`generatorBank_accuracy` proves stage error ≤2^-j for all three actually decoded
banks at n=j+2 and q≥j+2. Division alone costs at most `W*(12*W+93)+75`;
the complete reciprocal constructor costs at most
`W*(12*W+128)+6*(2*q+8)+4*q+134`. `generatorSetupCost` adds these executed
phases to column iteration and reversal without claiming a uniform S3 bound.
The guarded axiom audit passes all 4486 jobs at 2.6 GiB combined peak.
The retained dense square factor page is still supplied, and final sizing/header
generation, packed payload assembly/release and combined peak/uniform cost
matching remain open. Gathering/scheduling, halo cuts and complex/boundary/
coupling/recovery/full-line composition also remain open. S3 is incomplete;
this checkpoint does not change the proved multiplication saving.


The generator setup now publishes its retained runtime page rather than three
separate temporary banks. `sizedGeneratorSetup_exec` generates
`W=integerSetupWidth P q (M+1) 0=P*(M+2)+q+5` from ordinary P/M/q headers,
derives all iteration/encoding/division width inequalities when q≤2*(M+1),
constructs both generators and the reciprocal, releases the raw integer column,
and packs `[column; shifted reverse; reciprocal]` above the original tape-110
payload. The page has exactly `(2*L+1)*(2*q+8)` symbols; physical offsets i,
L+i and 2L retain the proved signed-decoding errors ≤2^-j.
`packGeneratorsCost` pays raw-column release and assembly:
`12*L*W+18*L*(2*q+8)+18*L+8*(2*q+8)+4*q+44`.
`releaseGeneratorPage_exec` generates/releases its own page count, with bound
`26*L*(2*q+8)+14*(2*q+8)+9*L+4*q+30`.
`sizedGeneratorRelease_exec` releases the page, readiness counters, generated
iteration and width headers, restoring the complete original bank, factor page,
unary header symbols and arbitrary borrowed suffixes. Its bound is
`releaseGeneratorPageCost L q+2*(W+topN W+(M+1))+9+2*W+2`.
The guarded S3 axiom audit passes all 4493 jobs at 2.6 GiB combined peak.
This is single-cell generator-page assembly and teardown, not a complete input
ABI transition or an execution-wide peak-space theorem. The dense factor page is
still supplied. Coefficient/factor and weight-table generation, remaining runtime
headers, repeated/batched page assembly, full input/output ABI composition,
combined peak/uniform costs, gathering/scheduling, halo cuts and complex/boundary/
coupling/recovery/full-line composition remain open. S3 remains incomplete;
the proved multiplication saving is unchanged.


The factor page is now constructed internally by the numerical setup entry:
`ScalarPlacement.numericalGeneratorSetup_exec` composes `factorFactory_exec`
with the checked inverse-generator and packed-page constructors. Numerical
binary table headers P/s/t/u/band/L and ordinary unary iteration/precision/row
headers are input encodings; no pi table, exponential samples, distance vector,
matrix rows, factor page, inverse column or reciprocal is provided.
The proof first shows that unreduced Gaussian arguments `u*t*k²/s` give exactly
the existing corrected exponential samples. The table machine generates pi once,
branches around diagonal/out-of-band entries, evaluates the corrected routine
once per retained distance, and explicitly clamps the subtraction-by-two at zero.
A structural word proof constructs each Toeplitz row from a reversed prefix and
a forward prefix of that distance vector; a paid scanner emits descending rows,
restores the original unary count symbols and releases all per-row work.
The coefficient table's 63-register workspace and temporary distance vector are
released before the factor page feeds the existing generator program.
`factorFactoryCost` charges the table instructions (`tblC V W` per atom),
row/page assembly and cleanup. The distance stream uses at most
`L*(310*P+114)+160*P+450` atoms, with explicit non-overflow condition
`u*t*(L+1)^2*2^(13*P+8)<2^V`, W≤V. There is no execution oracle or setup cost
assumption. `numericalGeneratorRelease_exec` releases runtime/factor pages and
generated iteration/readiness state, restoring every original bank field outside
the consumed, owned binary table-header workspace. Factor-page release costs at
most `12*L²*W+15*L²+9*L+18`.
The guarded S3 axiom audit passes all 9724 dependency jobs at 2.6 GiB combined peak.
This does not establish S3 completion: numerical table headers and their two
word-width counters still need the outer loader/generation bridge; weight-table
generation, remaining runtime headers, repeated/batched pages, full input/output
ABI composition, execution-wide peak/uniform cost matching, gathering/scheduling,
halo cuts and complex/boundary/coupling/recovery/full-line composition remain open.
The dense page's L²*W storage remains an explicit cost/space obligation. The proved
multiplication saving is unchanged.


The numerical table loader is now part of the executed setup:
`ScalarPlacement.headerGeneratorSetup_exec` starts with ordinary unary P/M/q/L
headers, owned unary s/t/u/band headers on 97--100, and clean native/table work.
It generates the setup width W, computes a logarithmic arithmetic workspace
`V=W+13*P+size(t)+size(u)+2*size(L)+size(band)+16`, initializes all 48 binary
table variables and both table counters, and loads the six actual header values.
`unarySize_exec` reuses the gamma writer's structural halving loop, retaining
original input symbols and appending `Nat.size n` ticks within `19*n+8` steps.
The generated V proves every header fits and
`u*t*(L+1)^2*2^(13*P+8)<2^V`; no initialized binary state, boundedness hypothesis,
width counter, sample, factor page, inverse column or reciprocal is supplied.
The same entry then runs the coefficient/factor factory and packed inverse setup.
`headerGeneratorRelease_exec` releases runtime/factor pages, table words,
readiness/iteration counters and the generated setup-width slot. All borrowed
stacks, original header symbols and arbitrary payload suffixes return; the
explicitly owned geometry inputs are consumed.
`headerGeneratorSetupCost` includes both width generators, table initialization,
all six retained-source binary loads, geometry cleanup and numerical setup.
The loader charges `(P+s+t+u+band+L)*(4*V+10)+36*V+61` steps, so unary geometry
reading is explicitly paid and still needs the outer amortized cost match.
The guarded S3 axiom audit passes 9731 dependency jobs at 2.6 GiB combined peak.
This closes the supplied table-state/width-counter gap. Weight-table generation,
remaining runtime-cell ABI/parameter composition, repeated/batched page assembly,
execution-wide peak and uniform cost matching, gathering/scheduling, halo cuts
and complex/boundary/coupling/recovery/full-line composition remain open.
S3 is incomplete and the proved multiplication saving is unchanged.

### S4 reverse tile routing (2026-10-30)

`PhaseCellReplicaChunkInverse` proves equal-chunk swap involution and cancellation
of an arbitrary volume-preserving schedule by its reverse. Instantiating the
canonical schedule restores replica-major order for arbitrary computed payloads;
symbol order inside each packet is retained. `generatedChunkTileUsing_exec`
shares the actual dimension-bank generation, stage execution, frame and disposal
proof between forward and reversed schedules. `generatedChunkTile_inverse_exec`
executes the reversed schedule with the same exact bill as forward routing.
The routing audit checks these endpoints, and the forward packed/padding audits
pass after the refactor. Packed inverse composition and executed dummy removal
remain open.

The next integration gate is a common external packet format: the numerical
input shift converts scale at fixed word width, whereas routed packets must
cross between a common width and key-dependent numerical widths. Its actual
conversion, restoration and linear bill must be proved before identifying these
interfaces. Then close one tile through numerical batches, inverse routing and
count-based dummy removal, before extending the global scheduler. Tile capacity,
setup amortization, complete bulk gathering, tensor/R4 composition and total
simultaneous stock remain required; S4 is incomplete.

`PhaseCellPacketWidth` now specializes the existing structural word passes to
both sides of that width interface. `narrowPackets_exec` crops W-bit complex
coefficient streams to w≤W bits with no unsignedness assumption, retaining the
same Gaussian integer encoding at cost N*(4W+2w+14)+4.
`widenPackets_exec` sign-extends an arbitrary list of numerical results satisfying
`TopFitsZ w` to W≥w bits at cost N*(6W+10)+4. Both programs restore all controls
and scratch and change only the source stream. Narrowing changes representation
width, not fixed-point precision: the separate existing input scale conversion
is still required. The signed-fit hypotheses, generated conversion counters,
placement and composition with actual numerical batches remain integration gates.

`PhaseCellPacketWidthControls` closes the supplied difference-counter premise.
A shared `withWidthDifference` program copies the retained external width,
subtracts the retained numerical width, runs the actual adapter and clears the
generated difference. Its exact setup/disposal overhead is
`4W+4w+2*(W-w)+10`, preserving the original width-header symbols.
`generatedNarrowPackets_exec` and `generatedWidenPackets_exec` instantiate this
wrapper with the concrete word passes, restoring all original controls and work
and changing only the owned payload. The narrowing adapter also uses an
initially blank zero control; no initialized generated counter is supplied.
Placement, numerical signed fits, fixed-point scaling and composition with the
actual tile batches remain open; these interfaces alone do not complete S4.

`PhaseCellCommonWidthInput.commonWidthInput_exec` composes generated narrowing
with the existing generated numerical input-scale batch. It starts with W-bit
complex packets, retained W/w unary headers and the ordinary borrowed binary
inverse scalar bank; it ends with exactly the w-bit stream of `2^d*z`, where
`E=inverseExecutionExponent ...`, `w=8E+8`, and `d=4E-p-1`. All controls and the
scalar bank restore, and only source 110 changes. Width setup, cropping, scalar
header generation, scaling and cleanup are included in the composed bill.
`commonWidthInput_value_fits` proves the output has value `value p z / 2` at
precision `4E` and fits w signed bits, using the unit input bound.
This is the actual width/scale handoff, not execution of the numerical solver.
The common W and key-specific w retained headers still need outer generation;
key-batch placement, output normalization/widening and complete tile composition
remain open.

`PhaseCellCommonWidthOutput.commonWidthOutput_exec` supplies the reverse format
handoff: the actual generated inverse rounding batch emits `2p+13`-bit words,
then the generated signed widening pass returns them at common width W. It
derives the signed fits needed for widening from the decoded magnitude bound
`norm(value (4E) (symZ (8E+8) z)) <= 8*2^(p+8)`, using the existing rounding
bound. No independent output fit or execution oracle is assumed. The total bill
includes rounding plus width setup, widening and disposal. Only source 132
changes, with original scalar state, retained width headers and scratch restored.
The numerical solver still must supply this decoded magnitude bound at the
actual output port; full tile/key placement and complete numerical composition,
inverse packed routing, dummy removal and the global S4 gates remain open.

### S4 packed return routing (2026-10-30)

`generatedChunkPlanesUsing_exec` now shares the two-plane bank lifecycle and
frame/stock argument over arbitrary payload lists and any stage list drawn from
the generated schedule. The forward public theorem is a thin specialization.
`generatedChunkPlanes_inverse_exec` specializes the same proof to reversed
stages and key-major input, preserving the forward bill. The structural
`chunkStageBits_length` lemma supplies common-volume preservation.
`PhaseCellPackedInverseChunkTile.packedGeneratedChunkTile_inverse_exec` closes
the packed return path with the existing codec: key-major paired Boolean words
are decoded, both planes execute reversed generated stages, and replica-major
paired words are reassembled. Source and owned count are the only changed right
stacks; all other bank/control stacks restore. The actual program uses the
reversed stage list, while its bound is the same forward packed tile cost.
No numerical execution or factor reuse is assumed by this routing theorem.
Executed dummy removal, key padding, key-batch placement and numerical composition,
total setup amortization, bulk gathering and global S4 resource gates remain open.

### S4 real-replica return (2026-10-30)

`PhaseCellRemoveDummyPrefix` executes position-based erasure after computation:
it copies the current payload length, subtracts a borrowed retained real-symbol
count, drops exactly the difference and clears its generated counter. Dummy
symbols are arbitrary, so numerical dummy results need not be zero. All original
counter symbols and scratch restore, and only the source changes. Exact cost is
`10*dummyLength+8*realLength+14`, at most `10*paddedLength+14`.
`removeDummyReplicas_exec` derives the remaining rectangular array from the
actual suffix length after removing `(capacity-realReplicas)*keyCount*wordWidth`
symbols; no output encoding witness is supplied.
`PhaseCellPackedRealReplicaReturn.packedRealReplicaReturn_exec` composes actual
packed inverse routing with that erasure. It returns the computed real-replica
suffix in order, with the forward packed routing bill plus `10*tileVolume+14`.
The routing count is consumed, the borrowed real-length header is preserved,
and all other right stacks restore. The retained real-length header must still
be generated/preserved by the outer tile lifecycle. Key padding, numerical batch
placement/composition, bulk gathering and global S4 resource gates remain open.

`PhaseCellRetainedReplicaPadding.retainedReplicaPadding_exec` now generates the
borrowed real-symbol count needed by the return path. Before padding, it scans
the actual owned source with `ucopy` into a fresh retained register, then runs
the existing generated replica padding. The returned paired arrays and exact
real suffix come from the executed padding theorem. Only the source and the
owned retained counter change, all scratch restores, and the combined cost is
at most `33*tileVolume+24`. The counter contains exactly `N*keyCount*packetWidth`
ticks and needs no supplied length witness beyond the input packet layout.
It must be kept outside routing/numerical scratch by the outer placement.
Its use for output erasure requires returned rows with the same common packet
length; interfaces changing row lengths must generate the corresponding output
count instead. Capturing the count does not yet compose numerical execution or
close the full tile lifecycle, key padding, scheduling or global S4 bounds.

### S4 counts across halo/core length changes (2026-10-30)

The fixed-key published batch returns owned cores, which may be shorter than
input halos. An input-symbol count therefore cannot automatically serve as an
output-symbol count. `PhaseCellReplicaCount.replicaCount_exec` derives N from
the actual replica-major source: generate row width K*W from retained key and
packet widths, scan whole rows with the existing restoring `countWords`, then
clear the generated width. Only the fresh retained replica counter changes;
source, header symbols and scratch restore. Its bill is
`K*(4W+9)+N*(6KW+6)+2KW+10`.
`PhaseCellReplicaCountRemoval.replicaCountRemoval_exec` generates the real
output-symbol count N*outputRowWidth, removes arbitrary computed dummy packets,
then clears the generated count. Only the output source changes. The bill is
`10*dummySymbols+14*realSymbols+9*N+20`. Both programs use structural existing
count/product/erasure proofs. This permits halo-to-core row shrinkage without
identifying incompatible packet lengths. The outer lifecycle must still place
and preserve the replica counter, generate output row dimensions and compose
these programs with actual numerical batches and inverse routing. S4 remains open.

`PhaseCellCountedReplicaRemoval.countedReplicaRemoval_exec` now generates the
output row width K*W and real-symbol count N*K*W from retained replica/key/width
headers, derives the surviving rectangular array from the actual suffix, removes
dummy rows and clears both generated counters. Its complete bound is
`K*(4W+9)+14*capacity*K*W+9*N+2*K*W+26`; only the payload changes.
`PhaseCellPackedCountedReplicaReturn.packedCountedReplicaReturn_exec` composes
this with the executed packed inverse route. It requires the retained replica
count N rather than a supplied real-symbol counter, uses current output packet
width W, and restores the generated row/real counters and other scratch. The
codec count is consumed, matching its owned input contract. Its bill includes
the inverse packed route plus all output dimension generation and erasure.
This closes the return path's dependency on input halo-symbol length. The outer
numerical lifecycle must still preserve the replica count through factor reuse,
place the output at this ABI, and supply actual result planes. Key padding,
bulk scheduling, numerical composition and global resource bounds remain open.

### S4 numerical streams enter return routing (2026-10-30)

The fixed-key archive publication theorem already returns core batches in input
order (`List.Forall₂`), despite reversed accumulation in the numerical loop.
`PhaseCellNumericalRoutingData` derives genuine paired Boolean arrays from the
actual coefficient stream using the existing pair round-trip law and structural
array views. `cstream_keyBatches_view` matches publication's nested shape: K
ordered batches, N rows per batch, L coefficients per row, at coefficient width w
produce key-major packets of width L*w. No unsignedness, numerical fits or
externally supplied plane witness is needed for this encoding step.
`PhaseCellNumericalReplicaReturn.numericalReplicaReturn_exec` accepts an actual
`cstream`, derives its planes internally, and executes packed inverse routing
plus generated output-count dummy erasure. Its bill and frame are inherited
from the checked counted return program. It does not execute the numerical
solver: outer placement and composition with factor setup, numerical batches,
format normalization, key padding and global S4 bounds remain required.

### S4 coefficient-level packet routing (2026-10-30)

`PhaseCellPacketEncoding` proves structurally that any fixed-width encoding
commutes with replica/key packet layouts. It factors a packet's coefficient and
bit indices through `finProdFinEquiv`, rather than checking concrete indices.
`PhaseCellCoefficientPackets` instantiates the law with complex coefficient bits:
`cstream` of a coefficient array is exactly the paired packet word of its real
and imaginary bit arrays, in either replica-major or key-major order. No signed
fit is required for encoding.
`coefficientChunkTile_exec` now states the actual generated counted forward route
as `cstream w (replicaKeyWords f)` to `cstream w (keyReplicaWords f)`, where each
packet contains L coefficients and has symbol width L*w. Its source-derived
counter restores. `coefficientInverseChunkTile_exec` states the reversed route
as the opposite exact coefficient-stream transformation, with the existing
owned codec count consumed. Both are thin specializations of checked programs
and inherit their bills and frames. This makes the numerical meaning of routed
packets explicit rather than leaving only existential Boolean views. Short-tile
coefficient padding, actual numerical batch composition and global S4 gates
remain open.

### S4 short tiles retain numerical coefficient semantics (2026-10-30)

`PhaseCellCoefficientPaddingData` proves that zero coefficient prefix padding
commutes with `cstream` encoding. Its rectangular witness contains whole zero
replicas before the original coefficients, and dropping those coefficient rows
recovers the exact original array. `coefficientReplicaPadding_exec` identifies
that coefficient stream with the existing executed symbol padding, with the
same `29*tileVolume+20` bill and restored controls.
`PhaseCellPaddedCoefficientChunkTile.paddedCoefficientChunkTile_exec` composes
this with the actual generated counted forward route. The input is an actual
short coefficient tile, and the output is `cstream w (keyReplicaWords g)` for
the derived zero-padded coefficient array g. Both the exact zero-padding law
and original coefficient suffix are retained in the conclusion. No Boolean
encoding certificate is a caller premise, and setup/counting/routing/cleanup
use the existing padded tile bill and caller frame. Dummy numerical inputs
therefore have genuine zero coefficients. This closes short-tile coefficient
padding and routing semantics, but not the executed numerical batches, key
padding, bulk scheduling or global S4 time/stock/tensor gates.

### S4 isolate a key before numerical conversion (2026-10-30)

The common-width normalizer owns its entire source stream. Applying it directly
to a routed queue would convert later key batches at the current key's widths.
`PhaseCellTakeKeyBatch` avoids that: generate the total N*packetWidth prefix
count from retained dimensions, take that prefix in order and clear the count.
The remaining queue suffix and all dimensions/scratch restore. Its complete
bill is `N*(12*packetWidth+9)+12`; the coefficient specialization places exactly
one key's coefficient stream on an initially blank numerical source.
`PhaseCellKeyBatchInput.keyBatchInput_exec` composes extraction with actual
common-width narrowing and generated numerical scale conversion. It preserves
the untouched later-key suffix and borrowed scalar bank, restores scratch, and
produces the precise normalized coefficient stream on native source 110. All
extraction and normalization costs are included. The queue is temporarily on
port 15 for this conversion stage; it must be placed outside live solver work
before invoking the full numerical lifecycle. This is a composed input stage,
not execution of factor setup or the numerical solve. Remaining S4 gates include
solver placement/composition, key padding, bulk scheduling and total resources.

### S4 protect the routed queue through the native solver (2026-10-30)

`PhaseCellKeyBatchPlacement.keyBatchInputReg` embeds the input stage into 306
registers, moving only queue 15, replica count 16 and common width 11 to physical
303, 304 and 305. The embedding is proved injective structurally; numerical source
110 and the scalar bank retain their native positions.
`protectedKeyBatchInput_exec` lifts the actual isolate/narrow/scale program with
exactly the same bill. Its explicit final state updates only queue 303 to the
untouched suffix and source 110 to the normalized batch. All other physical
registers, including the retained count/width and the native low-bank background,
restore. No input-stage execution callback is supplied.
The ordinary solver embedding `keyBatchSolverReg` uses registers 0--302.
`keyBatchSolver_exec` specializes the existing embedding simulation: any proved
native solver execution lifts at the same step count and preserves both stacks
of every retained high register. This is a structural frame lemma, not a solver
execution oracle or a complete key lifecycle. The actual numerical/factor batch
must still be instantiated against this low-bank view, followed by protected
output normalization, accumulation and tile/global S4 composition.

### S4 use the packed numerical entry, not the ambient caller (2026-10-30)

Inspection of `gridFamilyInverseBatch_spec` confirms that the 303-register
normalized caller still consumes an ambient `chirpLine s` per replica. Its
conversion/placement lemmas are checked adapters, but composing that caller
would not establish S4's local-volume bound. The actual S4 numerical supplier
remains the packed 263-register published batch. Do not use the ambient caller
to discharge the packed solve gate.
`PhaseCellPackedInputConversion` now supplies the required local conversion over
an arbitrary tape bank. Generated narrowing and numerator shifting operate only
on the isolated coefficient stream; the remaining-width counter is generated
and cleared. `PhaseCellPackedInputShiftHeader` computes `d=q-p-1` from retained
unary numerical/input precisions with exact cost `4q+4p+9`. Its value/fit lemma
proves that the shifted p-grid input is half its original value at precision q
and fits the packed native width `2q+8`.
`preparedPackedInput_exec` composes generated shift setup, local narrowing,
scaling and shift disposal, restoring all headers and scratch and changing only
the local source. The full cost is `4q+4p+9 + packedInputConversionCost W (2q+8)
(q-p-1) coefficientCount + 2*(q-p-1)+2`. It needs no scalar table, ambient source,
initialized shift or remaining-width counter. Numerical word-width generation
can reuse `generateWordWidth` from the retained q header. Actual packed-bank
placement, factor/batch execution, complex assembly, output conversion and the
remaining global S4 gates still require composition.

### S4 concrete packed-bank input placement (2026-10-30)

`PhaseCellPackedKeyInput.packedKeyInput_exec` runs beside the actual packed
263-register numerical bank in a 276-register file. Queue 263, current batch
replica count 264, common coefficient width 265, input precision 266 and packet
width 267 are external. It isolates one key's local prefix into native source
110, generates native word width from retained precision 119, generates and
executes the local width/scale conversion, then clears generated width work.
The explicit final state changes only source 110 and queue 263. Every other
native setup/metadata register and external scratch restores. The bill is
`packedKeyInputCost`, including extraction, width/shift generation, conversion
and disposal; no ambient full-line caller is invoked.
`packedKeyInputCounted_exec` additionally copies the current batch replica count
to initially blank native publication counter 251, at cost `4*N+4`. This N is
all replicas processed by the current key, including dummy replicas in a padded
tile. The real-replica count used for final erasure must remain separately
protected by the outer tile placement.
`PhaseCellPackedKeyPlacement` embeds the 263-register solver in the low bank.
The input's native-bank view changes only RHS 110, and lifting any proved native
packed execution preserves both stacks on all external ports with no added
steps. Actual factor/batch execution must still be instantiated against that
view; the native 251 dimension also needs outer disposal after use. Complex
assembly, output normalization, key padding and global S4 gates remain open.

### S4 actual protected factor/reuse/publication execution (2026-10-30)

`PhaseCellProtectedPackedHaloBatch.protectedPackedHaloGeometryPublishedBatch_exec`
now instantiates the concrete 263-register geometry/factor/published-batch
execution theorem inside the 276-register protected layout. Its premises are
that supplier's actual geometry, native bank readiness, precision, dominance,
input bounds and solution facts, plus procedure-table embedding equalities;
there is no solver execution premise or fabricated postcondition.
The resulting execution includes the native factor construction, reuse over
all replicas, numerical batch, release and owned-core publication. The native
step bound is unchanged. Both stacks on every register 263--275, including the
remaining-key queue and retained headers, are preserved. The conclusion exposes
the physical output on 253 as the ordered encoded core stream, exact replica
count preservation (`Ds.length = inputs.length`), and `List.Forall₂` core
accuracy. Native source consumption, owned factor cleanup and the supplier's
other restored fields remain explicit through its projected final bank.
This closes the protected concrete solve supplier, but does not yet compose
input conversion with its native readiness or prove the global tile machine.
Complex real/imaginary assembly, local output normalization, count disposal,
key padding, scheduling and total S4 resource gates remain open.

### S4 executed local input establishes field readiness (2026-10-30)

`PhaseCellPackedBatchInputData` proves pointwise conversion commutes with local
interval storage and ordered batch flattening. The converted flat source is
exactly the packed numerical supplier's per-replica encoding of fields
`2^(q-p-1)*F`. Local batch size is `replicaCount*(b-a)`, and unit p-grid fields
automatically satisfy every nonnegative RHS-exponent bound after conversion.
`PhaseCellPackedKeySetupFrame` projects the input stage's queue/source/count
updates into the native 242-register factory bank. Only source 110 changes in
that view. The existing `PackedHaloSetup.update_source` theorem transports all
setup fields once; native publication counter 251 and external queue 263 cannot
alter factory metadata.
`packedKeyFieldsInput_exec` joins these laws to the actual counted input program.
Starting from setup readiness and a common-width local field batch, it produces
the exact shifted-field RHS ABI, preserves `PackedHaloSetup`, derives all
per-replica RHS magnitude bounds, and supplies the native publication count.
The remaining-key suffix stays external; it is not a borrowed suffix on native
RHS 110. Its bill is the checked local input bill, with no ambient volume term.
The concrete solver call still needs the other native view/geometry premises
instantiated after this stage. Complex assembly, output conversion, tile/global
execution and resource bounds remain open.

### S4 shared readiness language at the concrete batch call (2026-10-30)

`PhaseCellPackedKeyInputViews.PackedKeyBankViews` packages the protected/native,
publication and extended factory/batch view equalities. `input_update` transports
all three through the input stage's queue, RHS and publication-count writes in
one structural step; `factory_view` identifies the same factory projection used
by setup readiness. These laws use arbitrary states and words, with no concrete
case enumeration over payloads or replicas.
`PhaseCellPackedHaloBatchFromSetup.packedHaloBatch_from_setup_exec` invokes the
actual protected numerical batch using the existing `PackedHaloSetup` record
and this view record. Geometry, precision, factory readiness, dominance and
related scalar premises are extracted from setup once. Only batch-source and
per-input bounds, the batch workspace, and core-publication conditions remain
separate. `packedHaloBatchCostFromSetup` names the existing exact supplier bound;
its execution, ordered outputs, accuracy and external frame are unchanged.
This closes the repeated-readiness proof interface for the numerical call.
Sequencing input and the actual batch still requires instantiating these records
and remaining publication/workspace facts at the input's final state. Complex
assembly, output conversion and the global S4 gates remain open.

### S4 sequenced local input and concrete real batch (2026-10-30)

`PhaseCellPackedKeyRealBatch.packedKeyRealBatch_exec` now executes the full
sequence of counted local input preparation and the concrete protected
geometry/factor/reuse/release/core-publication batch. It starts with unit p-grid
halo fields in the external key queue, initial setup/view records and the stated
workspace/publication geometry. The input stage establishes the shifted-field
source ABI, per-input magnitude bounds and native replica count. View transport
and `PackedHaloSetup` supply the actual numerical call's readiness; there is no
execution callback or assumed intermediate numerical result.
The native result is tied to actual input precision/width via
`boundaryHaloTarget_sizing`, with width `2q+8`. The conclusion gives ordered
physical core outputs on 253, exact output replica count and the real-core
accuracy relation. It also preserves the later-key queue, restores archive 132
and table 220, clears factor-owned registers, and exposes native 248/252 cleanup
and the retained owned 251 count. The bill is the sum of `packedKeyInputCost`,
publication-count initialization and `packedHaloBatchCostFromSetup`. All external
fields restore except queue 263 advancing to its untouched suffix.
This closes actual input-to-real-core sequencing for one complete key. Complex
assembly must reuse the same key factors across real/imaginary RHS replicas;
output normalization, owned-count disposal, full tile/key/global scheduling and
uniform simultaneous resource bounds remain open. S4 is incomplete.

### S4 one ordered component batch per complete key (2026-10-30)

`PhaseCellExpandComplexFields.expandComplexFields_exec` executes expansion of
the current key's local complex packets into all real RHS packets followed by
all imaginary RHS packets, in original replica order. It generates the prefix
symbol count from retained replica/packet dimensions, preserves the later-key
suffix, and restores conversion scratch. The active replica header becomes
2N while a fresh owned header retains N for output pairing and restoration of
the original header symbols. Its bill is `N*(26*(L*W)+17)+34`.
`complexComponentFields` describes those actual ordered fields;
`packedBatch_components` identifies their packed source and
`complexComponentFields_norm_le` supplies the unchanged unit-input bound.
The proofs are structural in the coefficient/field lists and arbitrary register
ports, without ambient line scans or finite payload enumeration.
`PhaseCellPackedComplexInputCheck` audits this controller separately from the
numerical supplier. Invocation of the real batch on these fields, output
pairing/normalization and owned-counter disposal still require composition;
this input preparation does not complete a complex key or S4.

### S4 exact setup/repeated-work split for the packed key (2026-10-30)

`PhaseCellPackedKeyBatchCost` decomposes the actual bill returned by
`packedKeyRealBatch_exec`, including conversion and native count initialization,
as its zero-replica accounting constant plus N times a named per-RHS cost.
Conversion, core publication and the protected numerical batch each have a
structural affine identity. `packedHaloBatchCostFromSetup_zero` identifies the
numerical constant with the existing `packedHaloSetupReleaseCost true` supplier
plus explicit header/core-publication controls. Thus the factor construction,
geometry and final release are outside the repeated-RHS charge.
`packedKeyRealBatchCost_two_components` proves a 2N real batch doubles only
the per-RHS charge. This is an exact accounting identity, not yet a selected
asymptotic bound: the setup constant must still be connected to the selected
key/tile allowance, and repeated work to the local-volume arithmetic bound.
The extended protected-batch axiom audit passes; the cost module checks at
about 3.2 GiB under default proof limits. Global time and simultaneous stock
are still open, as are complex output assembly and full schedule execution.

### S4 local complex output pairing and owned-count release (2026-10-30)

`PhaseCellPairComplexPrefix` pairs consecutive real and imaginary coefficient
batches in place, preserving the later-key suffix and restoring all private
buffers. `PhaseCellPairComplexKey` generates its symbol count from retained N
and the output-core row width; input halos and output cores need not have equal
lengths. Its bill is `N*(16*rowWidth+9)+14`. `releaseComplexCounts_exec` restores
the original replica-header symbols and clears the owned N and native 2N
counters in `10*N+8` steps, preserving all other stacks.
`PhaseCellPairPackedBatches.pairPackedBatchHalves_exec` consumes a single list of
2N numerical outputs, splits that actual list at N, and emits exactly N paired
local packets. The source and destination identities preserve replica order
and ambient field coordinates. Structural list laws connect flat coefficient
pairing with packet/field pairing; no output decomposition witness is supplied.

`PhaseCellPackedPairAccuracy` proves component identities for decoded words
without a Fits premise, including fixed-width reduction. This matches the
actual real numerical supplier, whose error contract concerns decoded packets
rather than representability of its arbitrary integer field representatives.
`pairedComponentFields_accuracy` combines the two scalar errors once per
replica, without a packet-length or replica-count multiplier. The independent
`PhaseCellPackedComplexOutputCheck` audits execution, count release, data order
and accuracy. Checked modules remain below 3.1 GiB with default proof limits.
These are the output-side contracts for one complex key. They still need
sequencing with component input and the actual numerical call, precision/common
format normalization and full tile/schedule execution. Selected time and peak
stock remain open; S4 is incomplete.

### S4 executed complex finish consumes one scalar certificate (2026-10-30)

`PhaseCellPackedComplexBatchAssembly.packedBatchHalves_accuracy` splits the
single ordered scalar accuracy certificate at the original replica count and
derives the complex certificate for those same output halves. The caller does
not supply separate component certificates, a decomposition, or a complex
accuracy witness. `packedComplexBatchAssembly_exec` ties that certificate to
the actual executed pairing output and derives its N-packet count.
`packedComplexBatchFinish_exec` then sequences this assembly with owned-count
release and exact replica-header restoration. The complete output-side bill is
`N*(16*(L*w)+19)+22`; the returned fields, emitted packets and complex accuracy
refer to the same paired list. Other stacks restore and the borrowed output
suffix remains intact. The extended output axiom audit passes, and the module
checks at about 3.0 GiB under default proof limits.
This closes the restored output operation given the actual real batch output
and its ordered scalar certificate. Component input, concrete numerical
invocation, output-row header generation and this finish still need sequencing;
normalization/common formatting, selected time/stock and full schedule execution
remain open. S4 is incomplete.

### S4 local normalization preserves later keys (2026-10-30)

`PhaseCellPackedRoundAccuracy.packedIntervalRead_finalRound` identifies the
normalized packed reader with `rhoC p` applied to the scaled old physical reader.
It handles the old word's fixed-width reduction explicitly and derives output
Fits from the magnitude bound. `packedFinalRound_accuracy` obtains that bound
from the actual decoded error (at most one) and the target norm bound; it adds
one rounding allowance `2/2^p` and scales the old error by `1/2^j`.
`packedFinalRoundBatch_accuracy` transports an ordered replica certificate with
the same error, without a packet-volume or replica-count multiplier.

`PhaseCellRoundPackedPrefix.roundPackedPrefix_exec` isolates only the counted
current-key prefix, runs the existing generated signed-rounding program on that
private buffer, and returns it before the untouched later-key suffix. Its scalar
bank, prefix counter and all scratch restore. For n coefficients, scalar width B,
input width w and rounded width k = p+E+5, the bill is
`13*tblC B 0+16*w+44*B+48+n*(20*w+4*k+23)`; it is independent of the suffix length.
The rounding controls are generated by the existing scalar program, while the
scalar bank and prefix-count readiness remain premises for outer composition.
The independent `PhaseCellPackedRoundCheck` audits the reader, error and actual
execution proofs. Both modules check below 3.2 GiB with default proof limits.
Common-width publication, generated caller dimensions, numerical/complex/rounding
sequencing and the global selected execution/time/stock gates remain open.

### S4 counted packed normalization returns its own accuracy (2026-10-30)

`PhaseCellRoundPackedKey.roundPackedKey_exec` generates the local normalization
prefix count from retained replica and packet-width headers, executes rounding,
and clears that owned count. All dimension symbols, scalar state and scratch
restore. Its bill separates fixed scalar/header work, N times packet-count work,
and coefficient-wise rounding; it contains no later-key suffix or ambient scan.
`PhaseCellRoundPackedBatch.roundPackedBatch_exec` instantiates this actual program
on the packed field list, derives the coefficient count from the local interval,
and identifies the emitted rounded fields using `packedBatch_round_source`.
The same conclusion supplies their ordered normalized accuracy and unchanged
replica count. Neither the transformed output nor the normalized certificate is
an input premise. This uses the generic generated rounding pass directly,
without the ambient 303-register inverse caller.
The extended local rounding audit passes; both new modules check below 3.2 GiB
under default proof limits. Scalar-bank initialization, common-width publication,
sequencing with the concrete numerical/complex batch and global selected
execution/time/stock gates remain open. S4 is incomplete.

### S4 shared owned-prefix transformation (2026-10-30)

`PhaseCellTransformPrefix.transformPrefix_exec` proves isolation, a restoring
local transformation and prefix return once over arbitrary symbol lists. Its
routing charge is `6*inputLength+4*outputLength+10`, independent of the borrowed
suffix. `isolatedPrefixState` names the intermediate bank with the suffix parked
on the source and the owned prefix on private work. The local transformation
must have an actual execution preserving every other stack; the concrete
rounding and widening programs instantiate this generic proof.
`PhaseCellRoundPackedPrefix` now uses this language instead of repeating the
transfer/move/final-frame argument. Its external program, statement and bill
are unchanged up to unfolding. The shared proof checks near 1.9 GiB and the
rounding instance near 3.1 GiB with default proof limits.

### S4 common-width publication preserves the key suffix (2026-10-30)

`PhaseCellWidenPackedPrefix.widenPackedPrefix_exec` instantiates the shared
prefix transformation with the actual generated signed-width conversion. It
emits the identical coefficient list at common width W, restores all retained
width/count symbols and scratch, and preserves the later-key suffix. The width
difference is generated and disposed by the existing conversion program.
For n coefficients of width w, the complete bill is
`4*W+4*w+2*(W-w)+24+n*(6*w+10*W+10)`, with no suffix-length term.
The strict output Fits already derived by normalization suffices for its signed
representability premise; the packed rounding accuracy theorem allows the final
common width directly, so widening introduces no additional numerical error.
The extended local rounding audit includes the shared transformation and actual
widening execution. Widening checks near 2.1 GiB; the affected rounding/batch
endpoints rebuild and audit successfully. Generating the common-publication
caller headers and sequencing it with rounding/numerical execution remain open,
along with selected time/stock and the global schedule. S4 is incomplete.
