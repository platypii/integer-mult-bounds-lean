# Components

Summaries of the checked components in `IntegerMultBounds/`, grouped by directory. Each entry says what is proved and what remains open. Paths are relative to `IntegerMultBounds/`.

## Machine

Machine model, execution, composition, and tape routines.

- `Machine/Composition.lean` and `Machine/Hoare.lean`: a concrete sequential
  composition of finite transition tables, exact execution with one extra
  transition, preservation of all tapes and heads at the connection, and
  time-bounded contracts derived from actual runs. The existing tape scan is
  connected to this contract interface. The design draws on [complexitylib](https://github.com/SamuelSchlesinger/complexitylib)'s
  composition approach (commit `3f4b5fe`); no external machine semantics or
  runtime assumptions are imported.
- `Machine/Loop.lean`: a concrete finite-state while loop testing only scanned
  symbols, exact body-plus-two-transition iteration cost, and a telescoping
  potential rule charging variable body runtimes. It introduces no counter
  comparison scans or output rewinds. Client routines must still establish
  the invariant and pay for their actual tape execution.
- `Machine/Frame.lean`: finite-table tape extension and reindexing, with
  exact-step simulation and time-contract transport. Extra tape contents and
  heads are preserved literally, without parking assumptions or runtime
  overhead. Combining extension and reindexing places fixed routines in a
  larger fixed tape bank; it does not provide random access to fields on a tape.
- `Machine/Counter.lean`: executable fixed-width binary increment, its exact
  modular value, and an amortized bound of `2*n + width` bit flips from arbitrary
  initial contents.
- `Machine/Rewind.lean`: a one-state backwards scan over any finite alphabet,
  with exact runtime to a sentinel, arbitrary integer head origins, complete
  tape preservation, and a Hoare contract.
- `Machine/Alphabet.lean`: finite-alphabet encodings preserve exact execution,
  halting, and time contracts; the widening instance preserves blank, bits,
  and separator. Decoding also simulates arbitrary larger-alphabet tapes.
  That weaker observation does not itself preserve foreign marker symbols;
  their preservation requires a separate locality invariant.
- `Machine/Protected.lean`: exact alphabet simulation on a proof-side region
  of each tape, with arbitrary larger-alphabet cells retained literally outside
  that region. Head-trajectory hypotheses establish preservation of foreign
  markers and exact runtime; halting also requires the final read in-region.
- `Machine/BitTape.lean` and `Machine/CounterTape.lean`: a three-state tape
  implementation of that increment, with exact carry and return runtimes,
  overflow handling, preservation of cells outside the bit segment, and a
  compositional time contract. A fixed four-state cyclic controller performs
  `n` increments within `8*n + 2*width` actual transitions from arbitrary initial
  contents, counting loop-control steps. This proves finite-prefix execution;
  a terminating stream scheduler remains to be built.
- `Machine/BinaryAdd.lean`: a fixed three-tape, three-state binary adder
  processes equally padded little-endian operands. The finite control stores
  carry; the exact transition count equals the output length, at most the
  input width plus one. Both entire inputs are preserved, and blank output
  initialization yields the exact sum with globally blank tails. Padding and
  output initialization are explicit preconditions.
- `Machine/BinarySub.lean`: a fixed three-tape, two-state subtractor
  takes exactly one transition per padded input bit. It preserves both
  complete source tapes and retains the final borrow in finite control.
  The modular subtraction identity, exact underflow criterion, ordinary
  nonnegative subtraction, and globally blank-tail output are proved.
- `Machine/BinaryPad.lean`: a one-state, two-tape scan physically pads two
  little-endian operands to their maximum width with high zero bits. It
  preserves both numeric values and halts in exactly that maximum width,
  with complete padded word tapes and both heads at the common end. Rewinding
  to the start for arithmetic is a separate charged operation.
- `Machine/BinaryArithmetic.lean`: a fixed three-tape, seven-state adder
  accepts unequal-width raw words, physically pads and rewinds both operands,
  then runs binary addition. Both composition joins and all head movement are
  charged: at most three times the maximum input width plus five transitions.
  The output is the exact sum with globally blank tails, and the padded
  sources retain their numeric values. Empty operands are included.
- `Machine/Execution.lean`: run composition, locality of writes, unit head
  motion, and an actual one-tape scanning program with exactly `n` transitions
  through `n` nonblank cells. The program preserves the tape and halts at the
  first blank. This is a stream primitive, not a multiplier.
- `Machine/WordTape.lean` and `Machine/Copy.lean`: finite-alphabet segment
  placement and appending, plus concrete two-tape copy and move programs with
  exactly one transition per symbol. The delimiter, complete source and
  destination tapes, and cells outside both segments are tracked in the time
  contract. Copying onto a blank tape gives the exact global blank-tail output
  representation. These routines are ingredients for record-stream processing;
  complete radix sorting is not yet implemented.
- `Machine/Partition.lean`: a concrete three-tape, three-state stable partition
  of delimiter-separated records by their leading key bit. The outputs are
  proved to be the encoded original-order filtered lists; the source is
  unchanged, and the exact runtime is the encoded input length. The contract
  retains complete tape contents, and blank outputs give globally blank tails.
  `TapeRadixSort` supplies the complete subsequent-key controller.

- `Machine/RadixSort.lean` and `Machine/PartitionSort.lean`: executable stable
  least-significant-bit sorting, with permutation, numeric sortedness, exact
  equal-key subsequence preservation, and a key-width-times-volume identity.
  The concrete partition's two outputs concatenate to precisely one such pass,
  with their total volume equal to its actual transition count. Full tape
  sorting is supplied separately by `TapeRadixSort`; the list traversal volume
  is not itself claimed as the machine runtime.

- `Machine/PartitionMarked.lean`: a five-symbol version of the literal
  partition retains a left sentinel on each tape. A proved nondecreasing-head
  invariant supplies the alphabet simulation's footprint. Exact complete-tape
  contracts and a distance-plus-one rewind theorem support stream composition.
- `Machine/Concatenate.lean`: a three-tape, two-state program copies two
  blank-terminated source words consecutively to a destination, preserving both
  sources. Exact runtime is their combined length plus one phase-switch step;
  the complete output and untouched background are specified. Source positioning
  is a precondition; this routine does not perform its callers' rewinds.
- `Machine/Reinsert.lean`: a three-tape, four-state program retains unflagged
  records and replaces flagged records in order from a second stream. It
  preserves both sources, halts after exactly the combined encoded input
  lengths, and proves complete output correctness when replacement count equals
  the number of flags. Selected-and-repaired records give pointwise flagged
  repair. Computing those replacements and sorting them into destination order
  still require separate machine proofs.

- `Machine/PartitionPass.lean`: a fixed four-tape, nine-state, five-symbol
  leading-bit stable pass, composing partition, both bucket resets, and
  concatenation. Its exact runtime is three times encoded input length plus
  eight, including every head movement and phase join. Complete output is
  the list radix sort's stable pass. The precondition supplies left sentinels
  and empty work/output tapes; setup, repeated key selection, and full sorting
  remain open.

- `Machine/KeySelectData.lean` and `Machine/KeySelect.lean`: one fixed
  three-tape, four-state machine scans a supplied unary key index, physically
  selects that bit from each record, rewinds, and emits a leading flag followed
  by all original bits. Source and selector are preserved. Exact runtime is
  input volume plus `recordCount * (2*index + 2)`, at most three times input
  volume for valid positions. Output is proved to match the partition format;
  repeated-pass control, flag removal, and buffer reuse remain to be composed.

- `Machine/DropFlag.lean`: a fixed two-tape, two-state routine removes the
  leading flag of arbitrary records in exactly their flagged encoded length.
  Optional source erasure restores a completely empty marked buffer while
  preserving its sentinel; output, untouched cells, endpoint heads, and halting
  are proved. Selection followed by flag removal restores the original records.

- `Machine/KeyPartition.lean`: one fixed six-tape, fifteen-state program
  composes physical key selection, a flagged-stream rewind, and the complete
  partition pass. Output encodes the stable pass of the original records at
  any valid key index; original input and selector survive. Exact runtime
  includes every join and is at most eleven input volumes plus twelve.
  Output still carries flags; repeated-pass buffer reuse remains separate.

- `Machine/KeyPass.lean`: a fixed seven-tape, twenty-one-state stable pass
  returns raw records after key selection, partition, and destructive flag
  removal. It resets the emptied sorted-flag buffer and tracks all other
  tape contents and heads. Exact runtime is bounded by seventeen raw volumes
  plus nineteen. Remaining old input/flag/bucket buffers need cleanup for reuse.

- `Machine/Erase.lean` and `Machine/KeyPassReuse.lean`: backwards cleanup
  preserves the sentinel and restores a marked blank stream in its length plus
  two transitions. A fixed seven-tape, thirty-six-state pass clears every old
  buffer and physically moves the sorted raw output back to the original input
  slot. All heads return to zero, every work tape is empty, and the selector
  survives; total time is at most twenty-six raw volumes plus forty-one.
  The repeated-pass selector controller remains separate.

- `Machine/UnarySelector.lean` and `Machine/TapeRadixSort.lean`: one fixed
  eight-tape, forty-state program performs the entire stable least-significant-
  bit radix sort, physically advancing and rewinding its unary selector and
  testing the width cursor. All work buffers return empty. Exact execution
  yields the list-level sort, with time at most `74 * width * rawVolume`;
  empty streams halt immediately. Initial marked buffers and unary width are
  explicit preconditions; their preparation is not charged by this theorem.

- `Machine/RadixDigits.lean`: Fixed-radix digit alphabet, decoder and least-significant-first word value, with exact encoding/decoding and word-width bounds.
- `Machine/RadixAdd.lean`: Literal three-tape, two-state fixed-radix modular addition. Exactly one transition per padded digit, actual halting, exact output remainder and final carry, with arbitrary tape backgrounds and complete source preservation.
- `Machine/RadixSub.lean`: Literal three-tape, two-state fixed-radix subtraction. Exactly one transition per padded digit; canonical modular difference, final borrow and underflow, actual halting and complete source preservation.

- `Machine/RadixUnary.lean`: Generic literal two-tape finite-table digit transducer. Exact-width execution and halting, arbitrary finite control, full source preservation and output-local writes; the finite table is fixed independently of word length.
- `Machine/RadixDivisionData.lean`: Bounded-carry prime-radix division by a fixed positive denominator below the radix. The d-state local congruence telescopes to exact integer and word-modulus division identities.
- `Machine/RadixDivide.lean`: Literal two-tape fixed-denominator modular division using RadixUnary, with exactly d carry states and one transition per digit. Arithmetic, exact runtime, halting and complete source preservation are proved.
- `Machine/RadixScaleData.lean`: Fixed-natural-coefficient scaling with coefficient+1 bounded carry states. Exact carry identity and word-width modular multiplication hold for every input word.
- `Machine/RadixScale.lean`: Literal two-tape fixed-coefficient modular scaling using RadixUnary. Exactly one transition per digit, output remainder and final carry, actual halting and source preservation on arbitrary tape backgrounds.

- `Machine/RadixRationalData.lean`: Arbitrary signed rational-numerator scaling in prime radix with a fixed finite signed-carry interval. The exact local congruence, interval invariant and full-word integer identity are proved; no state bound depends on width.
- `Machine/RadixRational.lean`: Literal two-tape rational-coefficient multiplication, including negative coefficients, with one transition per digit. The exact finite carry table implements the actual Swap.Modular.ratMod coefficient at every word modulus; exact runtime, halting and complete source preservation are proved.

- `Machine/CountdownData.lean`: Fixed-width binary decrement, exact borrow trace, zero detection and potential telescoping. All successful decrement/return/payload calls and terminal underflow cost at most five times the initial count plus twice the clock width plus two.
- `Machine/CountedCopy.lean`: Literal three-tape, five-state raw block transfer controlled by a binary count. Copies exactly the supplied count, even across blank payload symbols, preserves the source and destination background, and genuinely halts within the proved countdown bound. Clock preparation/reset and payload-head repositioning remain explicit caller operations.

- `Machine/CountedCopyReuse.lean`: Literal four-tape, sixteen-state reusable raw block transfer. Copies the immutable binary descriptor into a work clock, performs counted transfer, erases the clock, and returns both control heads. Exact runtime includes all joins and resets and is at most five times payload length plus seven times descriptor width plus sixteen. Descriptor construction and payload-head positioning remain explicit caller work.

- `Machine/BlockNegationData.lean`: Coordinate negation preserves block zero and reverses the remaining block order while retaining each internal payload. Exact payload indices, involution, width and volume are proved; reversing the raw tail and reversing each fixed-width pop realizes the same data recipe. Literal nested block scheduling remains separate.
- `Machine/ScalingControl.lean`: Fixed-multiplier residue control selects the unique source stream from Q modulo c and one finite output-residue state. Its transition, source reconstruction, clipped ceiling endpoints and exact piece sizes are proved, independently of word width. These are finite-control semantics; literal split/merge execution remains open.
- `Machine/BlockRotationData.lean`: Controlled cyclic block-shift semantics: split at Q-a, rejoin suffix first, preserve exact internal payload indices and total volume. Uniform-width flattening matches a literal payload cut at (Q-a)*B; per-fiber offsets preserve the entire payload permutation. These are list semantics, not a tape runtime.
- `Machine/ScalingPieces.lean`: Positive unit scaling split into quotient pieces, with unique divisibility-selected merge streams, exact source reconstruction and strictly increasing order inside each piece. The complete piece streams partition the output addresses, including multipliers above the modulus. No tape runtime is asserted.

- `Machine/Reflection.lean`: Reversing any fixed selection of tape head directions produces a literal finite transition table with exact step, run, halt and Hoare transport. Word reflection reverses its list representation; this is a simulation theorem, not a free tape reversal.
- `Machine/CountedReverse.lean`: Literal binary-counted backwards source read with forwards output and an unchanged forwards clock. Produces the exact reversed raw word, including blank payload symbols, preserving the source and destination background; the same linear countdown bound includes every real transition. The reusable variant also charges clock preparation, erasure and control-head resets. Initial source-head positioning and descriptor construction remain preconditions.

- `Machine/Placement.lean`: Generic whole-bank placement of a fixed-tape program. Active projection and replacement preserve the complete complementary tapes and heads; exact runs, real halts and Hoare contracts lift without extra transitions. Sequential exact contracts charge their connecting transition.
- `Machine/CountedSeek.lean`: Literal three-tape, sixteen-state forward and backward positioning by a binary descriptor. Proven projection of the reusable copying machine discards its irrelevant destination; every payload cell and the immutable descriptor survive, the work clock is restored, and all preparation/cleanup costs fit five times the count plus seven times descriptor width plus sixteen.

## Compact

Compact packed controls, repair, and density bounds.

- `Compact/Ideal.lean` and `Compact/ExactRepair.lean`: a packed ideal toggle
  permutation, preservation of the actual guard predicate, and executable
  destination repair connected to both concrete packed programs. Correctness
  holds for every address, including saturated temporary digits and failed
  guards. These prove address semantics. Tape partition and reinsertion
  primitives are proved separately; computing record keys, full sorting, and
  assembling the complete repair pipeline remain open.
- `Compact/Permutations.lean`: modular rotations as actual permutations,
  restoration of an arbitrary back field by swap/load/swap, and invertibility
  of both packed programs on every address, including bad addresses. The
  permutations are proved to agree with the integer implementations.
- `Compact/RepairBounds.lean`: the uniform rational exceptional-density bound
  under the stated dyadic cutoff, and the inequality reducing the written
  repair-cost expression to three logical volumes. The sorting implementation
  still needs a proof.
- `Compact/Counting.lean` and `Compact/Density.lean`: exact good- and bad-address
  counts for both concrete repair predicates, using a restricted radix
  bijection. These establish the common exceptional fraction bound capped by
  one, and its uniform bound `5 / (128*p^3)` under the dyadic cutoff. The density
  is derived from actual address cardinalities rather than assumed. Extracting,
  sorting, and reinserting the counted records on tapes remains open.
- `Compact/Layout.lean`: reversible whole-row splitting, preservation and
  completeness of every suffix, exact role volumes, padding to a multiple
  within twice the original volume, and ceiling-based reservation capacities.
- `Compact/Radix.lean`: bounded radix packing and decoding, injectivity, signed
  packed additions without carries, and preservation of lower/upper spectators.
- `Compact/PackedControl.lean`: executable modular arithmetic implementations
  of the earlier- and later-source gadgets, proved correct for arbitrarily many
  guarded digits. Offsets decode the current packed fields. The target parities
  are toggled and dirty temporary fields restored exactly. Embedding these
  segments in the complete physical slot, compiling the operations to tapes,
  and bounding their tape costs remain open.
- `Compact/DirtyControl.lean`: the four-update identity, restoration of an
  arbitrary dirty integer temporary, parity and guard invariance, the
  later-source identity, and guarded intermediate ranges. These are universal
  integer statements, used by the guarded packed modular refinement above.
- `Compact/Repair.lean`: for any two permutations agreeing outside an invariant
  exceptional set, the actual map preserves that set and destination repair
  gives exactly the ideal map. `ExactRepair.lean` now instantiates this result
  with both verified packed programs. Implementing repair within the tape cost
  remains necessary.

## Networks

Bit and complex networks.

- `Networks/Scalar.lean`: the eight-step arbitrary-scratch cancellation
  schedule, three-stage signed exchange, bit and complex triple-intersection
  coefficients, the resulting complex bank identity at any finite ground size,
  and the common-frame linear-gate identity. Sparse network realization,
  residual bases, endpoint corrections, and tape compilation remain open.

- `Networks/Circuit.lean`: executable finite linear register updates and matrix
  blocks, the full eight-row dirty-scratch schedule, its reversed inverse, and
  exact instruction counts. Arbitrary scratch and spectator registers are
  restored. A register update may read many terms: these instruction counts
  are neither sparse wire counts nor tape runtimes.
- `Networks/CircuitTriples.lean`: explicit copy, injection, gather, and scatter
  matrices for the complex motif, with neighboring-pair coefficient identities
  and the resulting executable shear over rational scalars. Finite wire
  enumerations and injective three-element labels parameterize the construction;
  concrete cardinalities, residual rank savings, Gaussian-dyadic values, and
  tape compilation remain open.

- `Networks/CircuitRouting.lean`: semantics-preserving register renaming and
  the three executable dirty-scratch stages implementing signed bank exchange.
  The middle stage uses the reversed inverse schedule with bank roles exchanged;
  all scratch and spectators are restored. Exact instruction counts and the
  neighboring-pair rational motif instance are proved. Tape movement, sparse
  wire counts, and residual spaces remain separate obligations.

- `Networks/CircuitBits.lean`: explicit binary motif matrices over `ZMod 2`,
  with intersection-one side pairs and coordinate-only central sums. Actual
  matrix coefficients reconstruct the source, proving executable dirty-scratch
  shear and true bank exchange with full scratch restoration. Elementary
  instruction counts are proved; grouped-gate topology and tape costs are not.

- `Networks/Labels.lean`: the degree-one rational and binary bilinear label
  spaces, their nondegeneracy, triple-indicator pairing formulas, orthogonality
  of neighboring triples, and nondegeneracy of each triple line. The rational
  form is nondegenerate whenever the ground size differs from nine. These
  label fields differ from the circuit scalar rings; tensor-cube labels,
  nested gate labels, and total residual-rank savings remain open.

- `Networks/NeighborCounts.lean`: an explicit intersection/outside splitting
  equivalence proves the generic fixed-size-subset intersection census. It
  yields exact triple-bank, bit-neighbor, complex-neighbor, and ordered-pair
  cardinalities, including 161700 triples, 13968 bit neighbors per triple,
  and 147731 complex neighbors at ground size 100. Enumeration transport
  connects these counts to the finite-index circuit side-wire predicates.
- `Networks/Wires.lean`: named roles for both data banks and every stage's
  separate invocation scratch, with exact cardinalities. The ground-size-100
  counts match both manuscript wire totals. Compiling the global gate schedule
  on these roles and attaching nested labels remain open; this is a layout
  cardinality proof, not yet the complete rank-saving network theorem.

- `Networks/TensorLabels.lean`: tensor products of finite nondegenerate
  bilinear forms are proved nondegenerate using their Kronecker matrices.
  The actual tensor-cube label spaces have dimension `h^3`; pure triple
  tensors have rational self-pairing eight or binary self-pairing one.
  Their terminal lines and orthogonal complements give nondegenerate direct
  decompositions with dimensions one and `h^3 - 1`. Intermediate gate labels
  and the complete residual budget still need construction.
- `Networks/FramedCircuit.lean`: explicit edge-frame instructions and finite
  circuit compilation prove the full common-frame identity, including all
  scratch and spectator wires. At every address the logical circuit is the
  existing executable scalar circuit. Intermediate frames cancel exactly;
  approximate frame implementations, grouped motif topology, and tape costs
  remain separate obligations.

- `Networks/ProjectionRank.lean`: actual orthogonal projectors on finite
  nondegenerate labels, their commutation along nested labels, and the exact
  range of their difference as the larger label intersected with the smaller
  orthogonal complement. This residual is nondegenerate, and the projector
  difference has rank equal to the label-dimension difference. Complementary
  projections also verify the routed endpoint identity with the required negative
  source projection, whose rank is exactly the source-label dimension. The network
  must still construct its comparable gate labels and sum these edge ranks.

- `Networks/GlobalCircuit.lean` and `Networks/GlobalCircuitBits.lean`: the
  full three-coordinate scalar schedule runs on the actual named wire layout,
  with separate arbitrary scratch for every invocation in every stage. Finite
  gate embedding and complete invocation enumeration prove global signed
  exchange over rational values and true exchange over binary values, with all
  scratch restored and exact elementary instruction counts. The dense row
  lists prove scalar semantics; grouped sparse incidence topology, Gaussian-
  dyadic scalar extension, and labeled rank/tape bounds remain separate.

- `Networks/ShearFrame.lean`: exact address-shear permutations and linear
  frames on arrays, with independent address and value rings. Composition
  adds matrices, edge changes subtract matrices, and the routed complementary
  projector endpoints give the full identity-matrix shear. Finite-radix
  encoding, denominator reduction, and rank-dependent tape execution remain
  open.

- `Networks/BinaryOrthonormal.lean`: every finite-dimensional symmetric,
  nondegenerate, nonalternating form over the binary field has an orthonormal
  basis indexed by its dimension. Explicit absorption of a hyperbolic plane
  into a unit line supports dimension induction. Concrete residual spaces
  still need their nonalternation witnesses.

- `Networks/GroupedCircuit.lean`: sparse simultaneous groups with read/write
  separation refine to elementary circuits, with exact nonzero wire supports.
  The eight motif rows use source-owned copy groups, target-owned injections,
  and single central groups; their bit and rational dirty-shear semantics and
  group count are proved. Framed compilation aligns each group once. Full
  grouped exchange topology and the labeled rank budget remain separate.

- `Networks/GroupedRouting.lean`: the inverse grouped motif and local
  three-stage exchange refine the existing bit swap and rational signed
  exchange, preserving dirty scratch. Renaming transports sparse supports
  exactly; the grouped gate count and threefold incidence count are proved.
  The global grouped embedding and labeled rank sum remain separate.

- `Networks/NeighborResidual.lean`: orthogonal anisotropic pairs span a
  nondegenerate plane, and their complement is the side residual with dimension
  two less than the ambient space. For neighboring rational and binary triples
  this gives the actual degree-one residual. Binary coordinate vectors outside
  supports prove norm-one witnesses for triple, pair, square-tensor, and
  cube-tensor complements; triple and neighbor complements have orthonormal
  bases. The full nested tensor gate labels remain to be assembled.

- `Networks/GlobalGrouped.lean`: actual grouped three-coordinate schedules
  on the existing global wire layout, with distinct scratch per invocation.
  Injective placement transports sparse supports exactly; the middle reversed
  inverse retains physical side orientation. The complete bit swap and rational
  signed exchange refine the scalar circuits, with exact grouped and incidence
  counts. Nested labels and total rank bounds remain separate.

- `Networks/BinaryPhase.lean`: exact rank-one decomposition of nested
  projection differences, indexed by the residual dimension. Actual Hamming
  weight modulo four is additive on orthogonal vectors, giving a diagonal
  edge factorization into one phase per orthonormal residual direction; unit
  directions have quarter-turn phases. Walsh conjugation, binary tensor
  coordinate identification, and tape execution remain separate.

- `Networks/TensorSubspace.lean`: actual embedded tensor subspaces, with
  monotonicity, distribution over sums, multiplicative dimensions, restricted
  bilinear pairing, and proved preservation of nondegeneracy and orthogonality.
  These support the nested labels of the network schedule.

- `Networks/TensorCoordinates.lean`: the actual binary tensor cube has an
  explicit coordinate tensor basis with identity Gram matrix, giving a linear
  isometry onto exactly `h^3` binary coordinates. This connects tensor labels
  to the concrete dot-product and Hamming-weight phase formulas.

- `Networks/LabelTransport.lean`: linear isometries transport actual label
  subspaces, nondegeneracy, orthogonal residuals, dimensions, and projection
  operators. Thus the coordinate bridge preserves the mathematical edge
  operators as well as their ranks. No tape coordinate-conversion cost is claimed.

- `Networks/BinaryWalsh.lean`: an explicit finite Walsh transform with
  checked orthogonality and inverse normalization conjugates the diagonal
  phase factors to actual address translations. Increasing and decreasing
  edges run exactly one forward/inverse manuscript kernel per residual
  dimension, given the proved local geometric premises. Multi-column lifting,
  Gaussian-dyadic closure, and tape execution remain separate.

- `Networks/MotifLabels.lean`: the actual eight-row local tensor-label table,
  with all labels nondegenerate and all data/neighbor-side paths increasing.
  The central return is the unique decrease and removes exactly the past line
  tensored with the current space. Tensoring by the future line preserves
  dimensions and comparability, including scratch source/sink edges. Global
  attachment and interstage coordinate identification remain separate.

- `Networks/RankTrace.lean`: finite wire-label update histories record the
  actual source/target subspaces. For comparable nondegenerate labels, the
  true projection-rank sum plus source dimensions equals sink dimensions
  plus twice the total dimension loss. Concrete schedule attachment and
  enumeration of decreasing edges must still establish the network budget.

- `Networks/GroupedFrames.lean`: the full common-frame compiler preserves
  actual multi-output group boundaries, tracks each wire’s last label, and
  appends all sink edges. Its exact array identity uses the original scalar
  grouped program; its complete label history feeds the checked projection-rank
  balance. The rational negative-source sign change has its actual rank proved
  in `ProjectionRank.lean`. Global loss enumeration remains separate.

- `Networks/StageLabels.lean`: actual tensor associator/unit isometries
  embed all three local motif geometries into the common tensor cube. X/Y
  output labels equal the next-stage input labels, and terminal labels are
  exactly the tensor line/zero and full space/orthogonal line complement.
  Attaching these subspaces to the global physical group history remains separate.

- `Networks/MotifSupport.lean`: actual sparse support lemmas identify each
  side wire with its unique copy/injection owner. Both concrete motifs have
  nonzero injection coefficients precisely at the owning target; central
  incidence tests and invariance under coefficient negation are also proved.

- `Networks/BinaryColumns.lean`: concrete slice operators on arrays indexed
  by multiple binary columns. Distinct-column operations commute, and the
  finite product regroups each forward/reverse edge into exactly one
  all-column factor per residual direction. The factor count is the actual
  dimension difference. Residual witnesses and arithmetic closure are supplied
  by separate modules; attachment to physical edges and tape implementation remain.

- `Networks/MotifResiduals.lean`: exact orthogonal residual formulas for the
  local data, side, and central label comparisons. Residuals tensor with the
  future line, and the final scratch residual is exactly the full earlier
  space tensored with the future-line complement.

- `Networks/BinaryMotifResiduals.lean`: all thirteen listed local comparisons
  have zero residual or an actual norm-one vector, including the future
  factor and scratch sink. Concrete witnesses discharge the earlier and
  future premises at each of the three stages for ground size above six.
  Isometries transport these witnesses. Matching every physical sparse-history
  edge to these comparisons remains part of global attachment.

- `Networks/GaussianDyadic.lean`: exact Gaussian-integer numerators on a common
  binary scale, closed under addition, subtraction, multiplication and halving.
  Actual binary translation kernels consume at most one binary place each;
  all-column factors consume at most the column count. Both directions of a
  nested projection edge have precision bounded by the actual residual
  dimension times the column count, with the zero-or-unit premise explicit.

- `Networks/GaussianCircuit.lean`: every actual rational motif coefficient
  is Gaussian-dyadic with at most one binary denominator place. Simultaneous
  grouped scalar updates preserve this arithmetic domain, increasing precision
  once per group by the maximum coefficient precision. These are exact
  arithmetic bounds; tape implementations and numerator-size bounds remain.

- `Networks/GaussianPrecision.lean`: explicit integer numerator bounds for
  the actual binary kernels, all-column factors, and forward/reverse projection
  edges. One kernel increases the binary scale by one and multiplies the
  numerator bound by at most four; a list across columns gives the corresponding
  exponential bound in residual dimension times column count. Exact tape
  arithmetic costs remain separate.

- `Networks/LabeledMotif.lean`: literal labeled forward, inverse, and opposite
  grouped motifs erase to the actual scalar schedules. Every physical wire
  history is derived from sparse incidence. Edge comparability, nondegenerate
  labels, and total loss bounded by central-wire count times current dimension
  are proved, including sink alignment and skipped intermediate labels.

- `Networks/SignedProjection.lean`: the first rational edge from a negative
  source projection to any containing label has rank equal to that containing
  label's dimension. The correction over ordinary edge rank is exactly the
  source dimension, even when sparse support skips an initial repeated label.

- `Networks/GlobalLabels.lean` and `Networks/GlobalLabelsNondegenerate.lean`:
  actual tensor labels attached to every physically embedded invocation of
  the three-stage schedule. Erasing labels returns precisely `GlobalGrouped`;
  source/sink and interstage identities refer to the same physical addresses.
  Every attached label is nondegenerate after future lift and transport.

- `Networks/GlobalLabelsResiduals.lean`: explicit binary norm-one witnesses
  cover the three extra comparisons created by missing sparse incidences,
  including their actual future-line lifts. Thus skipped intermediate labels
  do not require an assumed nonalternation property.

- `Networks/GlobalRank.lean`: actual local histories, losses, and comparable
  edges transport through tensor-stage maps and physical embeddings. Each
  real invocation loses at most the central-wire count times current dimension,
  also when prior sparse histories leave labels below the canonical input.
  Wires outside the invocation remain unchanged.

- `Networks/GlobalRankStages.lean`: disjoint physical invocation induction
  assembles the complete three-stage loss bound and comparable label edges.
  Sparse predecessors may leave weaker inputs; the invariant handles them.
  Actual terminal alignment adds no loss. No stage-loss premise is assumed.

- `Networks/ProjectionTrace.lean`: nondegeneracy propagates through actual
  sequential label updates. The sum of genuine projector-difference ranks
  equals dimension variation and telescopes with exactly twice the trace loss.

- `Networks/GlobalProjectionRank.lean`: all labels in the actual physical
  trace are nondegenerate; its projector ranks balance the actual terminal
  dimensions. The full loss theorem gives a global rank upper bound without
  supplying an assumed rank or loss budget.

- `Networks/ComplexRank25.lean`: instantiates the actual rational-scalar
  complex circuit at ground size twenty-five, its binary labels, sparse
  injection support, neighbor orthogonality, and complete terminal list.
  Its actual projection-rank sum is at most 916333630984500000 and meets the
  selected complex branching exponent. Binary edge-factor coverage is supplied
  by `GlobalBinaryResiduals` and `ComplexPhaseBudget`; tape costs remain open.

- `Networks/GlobalBinaryResiduals.lean`: complete norm-one-or-zero residual
  coverage for the actual binary-labeled global trace. Certified growth
  survives sparse skipped incidences and weaker stage inputs; disjoint
  invocation induction handles every stage and terminal edge. No global
  residual-unit premise replaces this concrete coverage proof.

- `Networks/BinaryRankFactors.lean`: genuine projector ranks count exact
  all-column binary vector factors in either edge direction. Isometric
  coordinate transport preserves the rank and the coordinate-label operator.
  One fixed kernel list works for every column count. Ordered trace lists
  retain each edge identity and the aggregate rank count; scalar-kernel or
  tape costs and physical instruction placement are separate.

- `Networks/ComplexPhaseBudget.lean`: the actual h=25 complex-network edge
  list has one finite family of binary kernel directions valid for every
  column count. Every edge operator is factored and total vector-factor count
  equals its actual rank sum, hence meets the concrete budget and exponent.
  Whole framed execution is supplied by `ComplexFramedExecution`; tape
  compilation remains open.

- `Networks/BinaryColumnFrame.lean`: actual invertible columnwise frames
  have the proved forward and inverse operators for every column count.
  Rational scalar restriction preserves the complex-array functions and
  identifies their exact frame changes with the rank-factor edge operators.

- `Networks/GroupedModuleFrames.lean`: the same grouped compiler acts on
  any module over its scalar ring. Whole-run identities and exact ordered
  instruction-edge extraction preserve the physical label history. Scalar
  circuit equalities, including signed routing, lift by proved coefficient
  rows to arbitrary module values without a freeness assumption.

- `Networks/FramedFactorExecution.lean`: replaces each actual frame-change
  instruction by its certified linear factors on the original physical wire.
  Reversed list execution matches operator product order; whole state runs
  agree and every scalar gate retains its position relative to the others.
  Exact factor count and total length include the fixed scalar gate list.
  These are finite linear-operation instructions, not tape transitions.

- `Networks/ComplexFramedExecution.lean`: instantiates the complete physical
  h=25 rational-scalar network on complex arrays. A fixed family of binary
  directions works at every column count; its placed vector factors execute
  exactly the signed bank exchange conjugated by the actual endpoint frames.
  Total array-instruction length is the rank total plus the fixed scalar-row
  count, and executed vector-factor count meets the budget and exponent.
  Scratch has its prescribed output frame; `ComplexEndpoints` simplifies the
  endpoint corrections to the desired transform. Tape compilation remains open.

- `Networks/TensorTerminalWeight.lean`: tensor coordinates of the actual
  terminal vector are the Cartesian-product indicator of its triple labels,
  so its binary Hamming weight is exactly twenty-seven.

- `Networks/ComplexEndpoints.lean`: explicit input/output character corrections,
  the terminal phase, and signed bank rerouting turn the actual h=25 physical
  network into the full product of forward coordinate kernels on every input,
  including dirty scratch. The lowered instruction run has the same transform
  and a uniform internal vector-factor budget. Correction costs, scalar-kernel
  expansion and literal tape execution are separate obligations.

- `Networks/NetworkBudget.lean`: sums dimensions of actual physical source
  and sink subspaces, including the empty-data case. At complex ground size
  twenty-five, their totals and the actual role count match the numerical
  parameter certificate. Given the full trace balance and global loss bound,
  the exact rank budget meets the selected complex branching exponent;
  those trace premises are not assumed globally.

- `Networks/SharedPointLabels.lean`: every source span generated by triples
  sharing one point is nondegenerate for the rational form. Its quadratic form
  is exactly the sum of coordinate squares away from that point; the shared
  linear relation proves positive definiteness. Support inclusion gives nested
  spans. These supply frame lemmas for the optimized bit graph; its circuit,
  sharing counts, and frame transfer are separate.

- `Networks/SharedPointMap.lean`: an exact bijection between excluded pairs
  and triples sharing one point proves that the three partial outputs equal
  the original bit-side matrix. Their actual source spans are nondegenerate
  and orthogonal to the target line. Optimized DAG construction is separate.

- `Networks/SharedPointKey.lean`: the upstream common-vertex/vertex-union
  key determines the exact triple support whenever at least two common
  vertices remain. Any sharing between distinct common-point copies lies
  in this branch, so the compressed key cannot merge unequal sums.

- `Networks/SharedPointIntern.lean`: executable compressed-key lookup among
  addition nodes and conditional interning preserve DAG validity and exact
  values over any commutative additive monoid. One-common-point nodes are
  freshly allocated; global sharing counts remain separate.

- `Networks/DisjointPruning.lean`: an executable backwards ancestor pass
  computes the least parent-closed set containing requested outputs. The
  instrumented run skips inactive additions and preserves every output of
  a valid DAG, with an exact marked-addition count. It retains index
  placeholders; compact physical role allocation and tape costs are open.

- `Networks/DisjointCircuit.lean`: executable addition DAGs carry checked
  disjoint input supports. Structural validation proves actual evaluation is
  the support sum; equal-support interning preserves values and validity.
  The list implementation is reference semantics, without tape-cost claims.

- `Networks/DisjointBuilder.lean`: executable zero-eliding, support-interning
  addition and list totals preserve validity, old references, and values.
  Pairwise-disjoint totals construct the exact support union with at most
  one fewer new nodes than operands, including empty and singleton cases.

- `Networks/DisjointBalanced.lean`: the upstream balanced total with literal
  floor-half splitting and left-before-right DAG construction. Zero elision,
  support interning, exact sums and preservation are verified with at most
  one fewer new nodes than operands. Construction order matches the source.

- `Networks/DisjointExclusion.lean`: executable prefix/suffix sharing builds
  all leave-one-out sums. Each output has exactly the support and value of
  the original list with that position removed; all old references survive.
  The constructed DAG adds at most three nodes per input. This variant does
  not certify the upstream allocation order or optimized certificate count.

- `Networks/DisjointPaired.lean`: a shared DAG batch builder using balanced totals computes the
  weighted paired-exclusion base-case queries: total, all single omissions,
  and all pair omissions. Ordered output values and supports, old-reference
  preservation and a sum-of-query-lengths node bound are proved. Recursive
  coarse-graph assembly and exact optimized counts remain separate.

- `Networks/PairedPartition.lean`: actual weighted-graph source supports
  partition into coarse vertex weights, crossing edges and remaining-vertex
  strips. Single, same-pair and cross-pair exclusions reconstruct by disjoint
  unions; finite-sum identities match the script's addition grouping.
  These justify recursive builder additions, without assuming partitions.

- `Networks/PairGrouping.lean`: literal consecutive-pair slicing has exact
  ceiling-half length, covers the original list, and gives nonempty disjoint
  groups of size at most two for distinct inputs. The coarse recursive call
  strictly decreases after the size-four base case.

- `Networks/PairedReconstruct.lean`: the script's actual three smart additions
  reconstruct a cross-pair exclusion from concrete far, strip and cross
  supports; one smart addition reconstructs a single exclusion. Valid DAG
  extension, exact output supports/values, preservation and three/one new-node
  bounds are proved. `PairedBlockCorrect` supplies complete recursive semantics;
  optimized sharing counts remain open.

- `Networks/SupportInterpretation.lean`: expanding weighted source atoms
  into original input supports preserves disjoint partitions and finite sums,
  including empty weights required by initial graph vertices.

- `Networks/PairedCircuit.lean`: full executable upstream paired-exclusion
  recursion, with the literal balanced-total, prefix/suffix, coarse graph,
  strip, and reconstruction order. Termination follows from actual pair
  grouping. `PairedBlockCorrect` proves its complete recursive semantics;
  optimized counts remain separate.

- `Networks/PairedVectorCorrect.lean`: the literal prefix-first, suffix-second
  vector builder preserves the DAG and produces the exact total and each
  omission over arbitrary commutative additive monoids. It adds at most
  three nodes per operand and preserves prior values.

- `Networks/PairedGraphSpec.lean`: ordered graph/table invariants and a
  semantic contract for recursive results, including exact query supports
  and preserved references. The literal small-block branch satisfies the
  complete contract; state-threaded balanced query loops are verified.

- `Networks/PairedCoarseSupport.lean`: actual paired groups classify fine
  sources into disjoint coarse vertex/edge cells that cover the graph.
  Excluding coarse indices excludes exactly their fine vertices, with
  domain validity and looplessness proved from the actual ordered keys.

- `Networks/PairedCoarseCorrect.lean`: both literal coarse construction
  passes establish the full recursive input invariant, with valid disjoint
  DAG references and exact interpreted source-cell supports. Canonical
  lookups, crossing queries, internal weights and persistence are proved.

- `Networks/PairedQuerySupport.lean`: actual table-filter queries equal
  interpreted fine sources avoiding the removed vertices. The source
  domain is loopless and contained in its vertex set; crossing queries and
  the weighted reconstruction partitions have their required disjointness.

- `Networks/PairedCoarseQuery.lean`: actual coarse table queries contract
  to fine-source exclusions. A correct recursive call supplies exactly the
  fine total, outside and far references needed for reconstruction, with
  the original graph invariant preserved at its returned DAG.

- `Networks/PairedStripCorrect.lean`: literal carry, balanced edge totals,
  prefix/suffix omissions and the entire strip loop are valid DAG extensions.
  Exact total and keyed omission supports are anchored in original operands;
  executable strip lookup retains those semantics after later extensions.

- `Networks/PairedStripSupport.lean`: the original graph invariant supplies
  every strip operand's validity and disjointness. Actual full and omitted
  strip queries expand to precisely the source strips used by reconstruction,
  with the remaining vertex weight retained and the selected group excluded.

- `Networks/PairedCircuitCorrect.lean`: literal single-output and nested
  cross-pair loops preserve the shared DAG and produce exact keyed support
  tables. The left partial sum is allocated once and shared through the
  inner loop, retaining the upstream constructor order.

- `Networks/PairedReconstructionSupport.lean`: the actual fine graph and
  contracted coarse outputs discharge all local reconstruction requirements.
  Executable strip lookups, single exclusions, reused within-group outputs
  and cross-pair loops give exactly the original graph's query supports.

- `Networks/PairedReconstructionKeys.lean`: literal group-member enumeration
  returns the original vertices, and internal pairs followed by cross pairs
  are a permutation of all original pairs. These list identities require no
  sortedness assumption and account for the actual output table order.

- `Networks/PairedBlockCorrect.lean`: full correctness of the literal weighted
  paired-exclusion recursion by strong induction, with no assumed recursive
  result or checker acceptance. Every total, single and pair output has its
  exact support and weighted value; the DAG remains valid and every prior
  reference retains its value. Optimized node counts and tape costs are open.

- `Networks/PairedInitialGraph.lean`: concrete singleton pair inputs in literal
  enumeration order, indexed edge references and zero vertex weights establish
  the full input invariant. The resulting circuit has exact surviving-pair
  output sums for all ordered vertex lists; the actual 49-vertex local circuit
  is unconditionally correct with exactly 1,176 inputs and outputs. Active
  addition, global sharing and physical role counts remain separate.

- `Networks/DisjointUnique.lean`: exact lookup absence, interning allocation
  branches and support uniqueness through smart addition and balanced totals.
  Valid DAG supports are nonempty; nonzero disjoint additions contain at least
  two sources, and equal supports identify valid references in a unique DAG.

- `Networks/PairedUnique.lean`: every literal paired constructor and the full
  recursive block preserve support uniqueness. Together with validity, this
  proves unique nonempty supports for the concrete 49-vertex local circuit.

- `Networks/DuplicateBudget.lean`: deleting one endpoint of each disjoint
  equal-support match preserves represented supports and saves a node. A
  nontrivial triple sum has at most two common vertices. Concrete domain and
  witness counts are required to instantiate the optimized numerical bound.

- `Networks/SharedPointMatching.lean`: in actual common-point copy families,
  a genuine ordered equal-support pair has exactly its two owners as common
  vertices. Per-copy uniqueness forces distinct discarded endpoints and
  excludes left/right overlap, discharging those counting prerequisites.

- `Networks/MaskDAG.lean`: executable bitmask DAG certificate checkers prove
  actual disjoint-support validity and evaluation semantics. A static balanced
  bank permits independent indexed chunks, checking its own annotations and
  all backward references; acceptance uses ordinary kernel reduction.

- `Networks/MaskSignature.lean`: checked small-mask core/union annotations
  equal the intersection and union of actual source endpoint sets. Inputs
  use their source endpoints; additions intersect cores and union vertices.
  Chunk composition and bank semantics avoid rescanning dense source masks.

- `Networks/MaskUnique.lean`: a checked strictly increasing list of masks
  with bounded, bank-verified node identifiers proves identifier uniqueness
  and coverage, then bank injectivity and unique actual DAG supports.

- `Networks/PairMask.lean`: canonical pair indexing and incident/exclusion
  bitmasks encode exactly the original pairs avoiding specified vertices.
  Decoded masks and weighted sums agree with actual canonical pair queries;
  the 49-vertex specialization supplies the certificate output interface.

- `Networks/DAGAllocator.lean`: literal active-node consumer order and role
  allocation, sharing the first input pivot with the first output, retiring
  other inputs and allocating remaining outputs fresh. The local transition
  produces a valid reversible fanout layout from its live-slot invariant.

- `Networks/DAGAllocatorCount.lean`: actual backward marking gives every
  active node a consumer. Counting real ports proves the executable allocator
  uses exactly active additions plus requested outputs, including repetitions.

- `Networks/DAGAllocatorFrontier.lean`: each real allocation preserves unique
  bounded live slots and consumer keys, with exact creation and retirement.
  This is the invariant used by the complete compiler scan.

- `Networks/DAGConsumers.lean`: actual consumer keys are unique, every active
  addition reads earlier producers, and inactive nodes have no scheduled ports.
  These facts discharge the compiler's scheduling requirements from the DAG.

- `Networks/DAGAllocatorRun.lean`: whole-loop frontier propagation produces
  valid layouts for actual emitted gates. Their scalar instruction lists have
  an executable reverse on arbitrary dirty registers, with no assumed layout
  or externally supplied allocator result.

- `Networks/DAGCompileCorrect.lean`: the complete actual compiler has valid
  shared-pivot gates, all intermediate slots within its role count, distinct
  bounded requested-output slots, and no pending gate-input ports. DAG-value
  transfer is proved in DAGValueTransfer; support-frame nesting remains open.

- `Networks/DAGAllocatorBudget.lean`: pruning cannot increase the number of
  additions, so the actual compiler's roles are bounded by all certificate
  additions plus requested outputs, without requiring a liveness certificate.

- `Networks/DAGValueTransfer.lean`: the actual emitted scalar program computes
  every requested DAG support sum when its distinct physical source slots are
  loaded from input labels and all other roles start zero. Proved by induction
  over the allocator, including pending values, future source initialization,
  source provenance and distinctness; repeated semantic input labels work.
- `Networks/DAGInstructionCount.lean`: exact scalar instruction accounting
  for the actual compiler: instructions plus source slots equal twice active
  additions plus requested outputs. This gives bounds from total additions
  or actual allocated roles, including repeated output requests.
- `Networks/Paired49Execution.lean`: the checked local witness's actual
  emitted program computes all 1,176 pair-exclusion sums over the binary field
  with at most 10,989 scalar roles and 20,802 XOR updates. It has an executable reverse on
  arbitrary states; tape execution and support-frame nesting are still open.

- `Networks/Paired49Certificate.lean`: unconditional finite witness for all
  1,176 canonical pair-exclusion sums on 49 vertices, over every commutative
  additive monoid; exactly 9,813 additions, unique supports, and exact endpoint
  signatures. Its actual pruned allocator uses at most 10,989 scalar roles,
  with distinct bounded output slots. Equality with the literal recursive
  builder and tape costs are not claimed.

- `Networks/ReversibleFanout.lean`: literal binary gate lists gather a sum
  into a pivot and fan it out. Full dirty-state semantics, reverse-list
  inversion, spectator preservation, exact instruction counts and support
  are proved. The singleton identity correctly has empty instruction support.

- `Networks/SharedPointLift.lean`: injective local pair-to-triple lifting under
  the actual omitted-point embedding; exact common/covered vertex formulas,
  preservation of support cardinality and cross-copy equality from verified
  endpoint signatures. Includes the canonical 49-vertex pair payload.
- `Networks/SharedPointFamily.lean`: the actual fifty-copy family formed from
  certified local addition nodes has exactly 490,650 members before sharing.
  Nontrivial supports, common points and per-copy uniqueness discharge the
  matching theorem's structural hypotheses; the concrete duplicate count
  is checked in Certificates/Shared50, with global construction in SharedPointReplay.

- `Networks/DAGReplay.lean`: executable topological import into an existing
  DAG under injective source renaming, interning by exact support. Validity,
  original-node reference alignment, evaluation, support uniqueness and
  addition provenance are proved through the actual scan.
- `Networks/DAGReplayBudget.lean`: for support-unique DAGs the addition count
  equals the cardinality of actual addition supports; replayed additions are
  bounded by the union of old and renamed source supports.
- `Networks/SharedPointOutputMap.lean`: canonical pair inputs cover every
  triple containing a fixed common point, and each lifted local exclusion
  support is exactly the triples intersecting its target in that common point.
- `Networks/SharedPointReplay.lean`: actual fifty-copy global DAG with exact
  58,800 output keys and values, valid references, unique supports and every
  addition support in the checked local family. The support-image bound of
  450,394 implies at most 509,194 compiled roles and 959,588 XOR updates;
  the premise is discharged in Shared50Certificate.

- `Networks/SharedPointExecution.lean`: actual compiled binary scalar program
  computes every common-point partial sum for every target triple containing
  that point. Output coverage, distinct bounded physical output slots and an
  executable inverse on arbitrary states are proved; numerical global bounds
  are discharged by Shared50Certificate and Shared50Finite.

- `Networks/SharedPointOutputIndex.lean`: direct arithmetic index for each
  common-point/pair output, proved to select its actual output record and
  compiled partial sum; no output-list search is needed.
- `Networks/BoundedCircuit.lean`: converts every bounded scalar instruction
  to an actual finite register type, preserving forward/reverse execution
  under restriction and preserving instruction count.
- `Networks/DAGFiniteCompile.lean`: the actual allocator bounds every scalar
  target/source; its finite-register program has exactly the same execution,
  output values and length, with a proved inverse on arbitrary finite states.
- `Networks/SharedPointWitnessCheck.lean`: compact duplicate checker with
  proved omitted-point bit insertion, exact core/union signature semantics,
  genuine cross-copy equality and sorted-row uniqueness/cardinality.
- `Networks/Shared50Certificate.lean`: the global certificate discharges every
  finite-count premise: actual additions at most 450,394, compiled roles at
  most 509,194, and at most 959,588 scalar XOR instructions in the same program
  that computes all common-point partial sums.
- `Networks/Shared50Finite.lean`: concrete program on `Fin 509194` with the
  certified instruction bound, exact partial sums at explicit distinct output
  registers, and executable reverse on arbitrary finite register states.
  Global rank-frame assembly and literal tape costs remain open.

- `Networks/DAGFramedExecution.lean`: actual interleaved frame alignments and
  unchanged scalar instructions telescope to initial decoding, literal module
  execution and final trace encoding on arbitrary stored module states.
  Erasing only frame changes recovers the compiler's exact scalar program.
- `Networks/FanoutFrames.lean`: literal fanout alignment and scalar execution
  in a common frame, including identity pivots; support-derived increasing
  labels, nondegenerate endpoints and exact projection-difference ranks.
- `Networks/DAGSupportTrace.lean`: support events erase to the actual compiler
  gates; source initialization and allocator invariants prove every event
  ready, output supports exact, and the forward label trace increasing with
  zero dimension loss. Common-point nodes give nondegenerate edge endpoints.
- `Networks/SharedPointOutputLabels.lean`: lifted exclusion supports have
  exactly the partial-output span, nondegenerate and orthogonal to the target.
- `Networks/Shared50Frames.lean`: the actual shared fifty-copy DAG satisfies
  all forward support-trace premises; exact output labels hold at arithmetic
  output slots. Inverse/complement labels and global rank assembly remain open.

- `Networks/DirtyLinearCircuit.lean`: actual embedded compute/read/uncompute/
  inject schedule restores arbitrary scratch; its shear is the actual linear
  computation on the injected input. Additivity is proved from instructions.
- `Networks/Shared50Dirty.lean`: actual finite source loading and three-output
  readout recover the intersection-one neighbor map; the shared circuit's
  concrete dirty wrapper restores every scratch register. Dense matrix
  wrappers establish semantics, without sparse operation or tape-cost bounds.
- `Networks/Shared50Invocation.lean`: literal twelve-block optimized schedule
  combines the actual shared circuit with the fifty central sums. It performs
  the full identity shear and restores arbitrary side and central scratch,
  retaining spectators. Global stage reuse and frame/rank costs remain open.

- `Networks/DAGComplementTrace.lean`: reverse each actual label assignment
  and complement both endpoints, retaining repeated incidences. Exact endpoint
  restoration, increasing reverse edges, zero loss and nondegenerate complements
  are proved; scalar event reversal equals the compiler's reversed program.
- `Networks/DAGComplementExecution.lean`: physical complementary inverse
  execution retains gate boundaries and identity pivots. Its exact label trace
  is the proved reversed-complement trace, its scalar erasure is the literal
  reverse program, and its frame identity holds on arbitrary module states.
- `Networks/Shared50Exchange.lean`: explicit inverse of the optimized twelve
  blocks, opposite data orientation, and three-invocation local bank exchange,
  all restoring arbitrary side/central scratch and spectators. Inverse matrix
  blocks retain their internal row order; full global placement is separate.

- `Networks/TripleNeighborPermutation.lean`: double counting proves Hall's
  condition for positive regular relations; the exact triple-neighbor degree
  supplies a fixed bijection at h=50 pairing every triple with a neighbor.
  This uses classical finite choice, not the upstream paired-point generator.
- `Networks/Shared50ReuseLabels.lean`: actual stage-one and stage-three tensor
  boundary labels at the selected reuse pairs are nested and nondegenerate.
  The join has zero downward loss and its actual projector rank saves exactly
  125,000 against separate terminal edges. The reused scalar schedule is proved
  in Shared50GlobalCircuit; its complete rank trace remains separate.

- `Networks/DAGSourceRoles.lean`: each actual source entry has a certified
  finite role and actual input-node label, with no fallback value. Repeated
  semantic labels retain their separate physical source locations.
- `Networks/Shared50InitialLabels.lean`: every actual source role starts at
  its source triple's indicator line; nonsource roles start at bottom. The
  complementary reverse ends at the source line's orthogonal complement.
- `Networks/Shared50OutputRoles.lean`: equal partial-output slots identify
  both target and common point; physical slots have their exact arithmetic
  output index, final partial-output span and target-line orthogonality.
- `Networks/Shared50ComplementFrames.lean`: the actual fifty-copy circuit
  has increasing nondegenerate complementary inverse edges, zero reverse loss,
  exact endpoints and the target-line inclusion at every original output.
- `Networks/Shared50StageFrames.lean`: lifts actual forward/complementary
  inverse traces into the stage geometry and future tensor line. Exact edges,
  endpoints, nesting, nondegeneracy, zero loss and physical source/output
  attachments are proved; whole-invocation and global assembly remain separate.
- `Networks/Shared50FiniteTrace.lean`: every actual declared label incidence,
  including identity pivots, fits the certified 509,194-register bank. Finite
  restriction preserves the complete ordered edge list and exact endpoints
  under any stage label lift, without filtering any update.

- `Networks/SparseCircuit.lean`: actual one-source XOR lists between disjoint
  banks, with exact accumulation semantics, instruction count and incidences.
- `Networks/Shared50SparseIO.lean`: copies only actual allocated source slots
  and reads each target's three physical partial outputs. Proves arbitrary-state
  equivalence to the dense matrices, unique source roles, exact gate incidences,
  nonsource preservation and source/readout counts; no zero terms are emitted.
- `Networks/Shared50SparseCentral.lean`: literal gather/scatter incidences are
  precisely each triple's three coordinates. Both lists have 3n XORs and exact
  central-matrix semantics on arbitrary scratch with spectators preserved.
- `Networks/Shared50SparseInvocation.lean`: actual sparse twelve-block program,
  inverse blocks, opposite orientation and three-invocation exchange, restoring
  arbitrary scratch. Exact counts give at most 5,209,540 scalar instructions per
  invocation and 15,628,620 per local exchange at h=50. These are not tape costs.

- `Networks/Shared50GlobalBudget.lean`: explicit padded world with two
  auxiliary banks and 406,321,422,080,000 roles; embeds all certified local
  roles, defines actual rational terminal labels, and proves their total
  dimensions. The existing three-bank world has a different count. Corrected
  rank and branching corollaries explicitly require actual trace balance and
  loss bounds; this file does not prove the reused schedule's rank estimate.

- `Networks/Shared50GlobalCircuit.lean`: actual three-coordinate sparse
  program on the optimized two-bank world. The outer stages share matching
  side and center slots via the neighbor permutation; each stage's placements
  are injective and the middle bank is separate. Every invocation, full stage
  and fixed global program swaps/shears as specified, restoring arbitrary dirty
  scratch. Exact list accounting gives at most 3 × 19,600² × 5,209,540 scalar
  instructions. Projector-rank history and tape costs remain separate.

- `Networks/FramedEmbedding.lean`: injective placement preserves actual
  frame/scalar instructions, scalar erasure and complete module execution.
  Full-register frame identities include exact preservation of all spectators.
- `Networks/BoundedFramedCircuit.lean`: checked restriction of physical
  frame-edge and scalar instructions to a finite bank, preserving module
  execution, scalar erasure and full decode/execute/encode identities.
- `Networks/Shared50FiniteFramed.lean`: actual finite forward and complementary
  inverse physical schedules on 509,194 registers. Every declared incidence,
  including scalar-empty pivots, has a proved bound; scalar erasure is exactly
  the certified finite program or its reverse. Identities hold on arbitrary
  module contents with no initialized-scratch premise.
- `Networks/Shared50FiniteReverseTrace.lean`: complementary reverse updates
  introduce no new roles; finite restriction after any stage-label lift retains
  the exact endpoints and complete ordered edge list without filtering.

- `Networks/Shared50LabeledInvocation.lean`: concrete forward sparse-block
  boundary profiles and unique physical readout owners. Every source/readout
  attachment and all profile nondegeneracy facts are proved, including reused
  scratch entering at the stage-common label.
- `Networks/Shared50InvocationRank.lean`: complete finite forward label
  history includes boundary alignments and every actual middle DAG incidence.
  Exact endpoints, nested nondegenerate edges and loss exactly 2,500 are proved,
  for bottom or common auxiliary input. Physical linkage is proved in Shared50InvocationPhysicalEdges.
- `Networks/Shared50OppositeLabels.lean`: concrete opposite-inverse profiles
  use actual complemented final spans for injection and complemented initial
  source lines for draining; common-frame attachments and nondegeneracy proved.
- `Networks/Shared50OppositeRank.lean`: complete opposite history, including
  the actual finite complementary inverse trace. Common-input endpoints,
  nested nondegenerate edges and exact loss 2,500 are proved; physical linkage
  is proved in Shared50FramedOpposite; global rank assembly remains separate.

- `Networks/FramedBlocks.lean`: Whole-bank frame alignment and scalar-block lifting with exact execution and erasure laws.
- `Networks/FramedEdgeTrace.lean`: Extracts every ordered physical frame change, preserving identity edges and repetitions; extraction commutes with finite restriction and injective placement.
- `Networks/Shared50BlockFrames.lean`: Every actual forward sparse block uses a common frame at its concrete invocation boundary profile.
- `Networks/Shared50FramedInvocation.lean`: Complete physical forward wrapper around the actual finite shared DAG. Exact sparse scalar erasure and frame identity on arbitrary module contents, including dirty scratch.
- `Networks/Shared50PhysicalEdges.lean`: Actual finite forward and complementary inverse middle frame changes equal the ordered support-label traces.
- `Networks/Shared50InvocationPhysicalEdges.lean`: Every frame change of the complete physical forward wrapper equals the corresponding edge of its proved local rank history.
- `Networks/Shared50OppositeBlockFrames.lean`: Common-frame proofs for every actual opposite-inverse sparse block at its concrete boundary profile.
- `Networks/Shared50FramedOpposite.lean`: Complete physical opposite wrapper with literal complementary inverse middle, exact sparse scalar erasure, arbitrary-module frame identity and exact equality to its local rank edges.

- `Networks/Shared50InvocationProjectionRank.lean`: Genuine rational projector-difference matrices certify every actual forward/opposite physical frame change in order. Their actual range ranks telescope with the proved local loss of 2,500, without assumed edge costs.
- `Networks/Shared50GlobalTrace.lean`: Concrete source, stage and sink profiles on the actual reused two-bank world. All four boundary attachments have exact endpoints, nondegenerate increasing edges and zero loss; the reused stage-one/stage-three join uses the actual scratch key.

- `Networks/Shared50GlobalTracePlacement.lean`: Places the actual three local histories on the two-bank physical world, preserving exact local endpoints, edge order, loss 2,500 and nesting; different same-stage placements are disjoint.
- `Networks/Shared50GlobalTraceNondegenerate.lean`: Transports nondegeneracy of every actual forward/opposite local edge through the three tensor coordinate isometries into the common rational cube.
- `Networks/Shared50GlobalTraceStages.lean`: Complete chronological reused-world trace: four boundaries and all three actual invocation stages. Proves exact source/sink endpoints, nested nondegenerate edges and total loss 2,881,200,000,000, with no global trace hypotheses.
- `Networks/Shared50GlobalProjectionRank.lean`: Genuine projector-difference operators for the complete optimized global trace. Their actual range ranks satisfy exact balance, and adding the source correction gives exactly 50,790,175,992,864,000,000 and the strict chosen branching inequality. Signed physical realization is proved in Shared50GlobalShear.

- `Networks/Shared50GlobalFramed.lean`: Literal three-stage physical execution on the actual reused two-bank world. Exact scalar erasure, arbitrary-module frame identity and equality of every ordered physical frame change with the complete global rank trace.
- `Networks/Shared50SignedBoundary.lean`: Actual negative-source first-boundary shear matrices and physical instructions in exact wire order. Their genuine range-rank sum equals the ordinary boundary rank plus the exact source dimension total.
- `Networks/Shared50ShearEndpoints.lean`: Exact global scalar and arbitrary-module routing, plus the actual sink-minus-negative-source projector identity on both data banks and all scratch. Every routed array receives the same full address shear.
- `Networks/Shared50GlobalShear.lean`: Complete signed physical optimized network on arbitrary binary arrays over rational address pairs. Exact scalar erasure and uniform full address shear after data exchange, including dirty scratch; every physical edge has its actual matrix certificate, whose total range rank is exactly the improved budget and satisfies the strict branching inequality. Finite-radix realization and tape costs remain separate.

- `Networks/Shared50OperatorPairs.lean`: Retains both rational operator endpoints of every actual signed physical frame edge. Their ordered differences are exactly the already-counted operator list, and their shear frames are exactly the physical frame pairs.
- `Networks/Shared50ModularOperators.lean`: Chooses a 125,000-coordinate basis for the actual tensor ambient, proves matrix rank equals operator range rank, and applies the existing modular-shear construction to the concrete ordered operators with exact total interchange count.
- `Networks/ModularFrameSchedule.lean`: One good prime simultaneously protects every ordered frame endpoint, difference factorization and extra endpoint matrix. At every prime-power modulus, the actual reduced-frame differences have ordered shear programs with exact rational-rank interchange totals; reduction is through the coprime-denominator subring.
- `Networks/ModularProgramShape.lean`: Each modular edge program reduces one fixed rational instruction list. Operation order and pivots are independent of width, with exactly three times the rank plus four field operations per edge. These counts are not tape steps.
- `Networks/Shared50ModularSchedule.lean`: Instantiates the shared-prime construction with the exact signed physical matrix pairs and all source/sink matrices. One prime works at every radix exponent, the routed endpoint difference remains the identity, and the ordered edge programs have exactly the improved interchange budget. Full modular physical execution is proved in Shared50ModularExecution.

- `Networks/Shared50SignedFramed.lean`: Generic signed first-boundary physical wrapper for any module and initial frame profile. Exact scalar erasure, stored-state routing and ordered physical pairs; the rational wrapper is a definitional specialization.
- `Networks/Shared50ModularExecution.lean`: Full physical optimized network on finite prime-power address arrays, for every exponent at one fixed odd prime. Exact routed full shear on arbitrary data and dirty scratch arrays, exact scalar erasure, and ordered per-edge field programs realizing the actual physical array movements with exactly the improved interchange budget. Tape execution and runtime remain open.
- `Networks/Shared50ModularControl.lean`: Canonical edge-control lists use one chosen prime and fixed rational factorizations, with no new program choices per width. Exact interchange and total field-operation counts, fixed rational instruction shape, admissible endpoints and lower-triangular transform matrices are proved.

- `Networks/Shared50FiniteInterchange.lean`: complete finite address-chunk interchange using the actual optimized modular network between literal pre/post field programs. Every routed array, including arbitrary scratch, exchanges its two coordinate groups; all physical edges have ordered field-program certificates, exactly the improved recursive interchange count, and a fixed rational instruction shape across widths. Pre/post add no recursive interchanges. Tape execution and runtime remain separate.

- `Networks/Shared50CoefficientMachines.lean`: Every transform coefficient in the actual fixed rational interchange schedule has denominator below its chosen prime, derived from actual factorization membership including inverse factors and the negative-identity boundary. Each coefficient therefore has a literal two-tape arithmetic kernel with exact width runtime, halting, source preservation and output equal to the actual reduced matrix entry times the input. Matrix sweeps and payload permutations remain separate.

### Networks/Certificates/Paired49

Generated data are untrusted; all acceptance proofs use Lean kernel reduction.
The four generators in `scripts/generate_paired49_*.py` reproduce the witness
from the reference paired-exclusion implementation.

- `Data.lean`, `Chunk000.lean` through `Chunk085.lean`, `Checked.lean`:
  10,989 support masks with checked input masks, backward references, disjoint
  addition operands and exact support unions; DAG validity and 9,813 additions.
- `Incidents.lean`, `Outputs.lean`: checked endpoint-incidence masks, the full
  canonical output list, output bounds, and exact pair-exclusion semantics.
- `Unique.lean`: a sorted mask certificate checks coverage and injectivity of
  the actual bank, proving all node supports are distinct.
- `SignaturesData.lean`, `SignaturesChunk000.lean` through
  `SignaturesChunk085.lean`, `Signatures.lean`: exact common/covered endpoint
  sets for every support; 4,389 additions have empty common-endpoint masks and
  5,424 have nonempty ones. These are local counts, not the global sharing count.

### Networks/Certificates/Shared50

- `Data.lean`, `Chunk000.lean` through `Chunk314.lean`, `Checked.lean`:
  40,256 duplicate rows, each kernel-checked for increasing common points,
  actual addition indices, matching lifted endpoint signatures, and strict
  numeric ordering. Finset conversion preserves the full distinct-row count.
- `Kinds.lean`: the addition-index range is checked against every actual local
  certificate row, rather than assumed from the generator's numbering.
- `Semantics.lean`, `Sound.lean`: the numeric checker describes the actual
  common-point support family; all listed pairs are genuine duplicate
  witnesses, yielding at most 450,394 distinct addition supports. The generator
  `scripts/generate_shared50_witnesses.py` supplies only untrusted finite data.

## NLogN

The `O(n log n)` FFT multiplier subroutine and the analytic tools for resampling.

- `NLogN/DFT.lean`: the discrete Fourier transform over an integral domain
  with a primitive root of unity, its linearity, the cyclic convolution
  theorem, orthogonality, double-transform inversion up to the factor `N`, and
  injectivity. This is the algebra behind every FFT multiplier, including the
  `O(n log n)` subroutine; no fast algorithm or rounding analysis is here.
- `NLogN/FFT.lean`: the radix-2 Cooley-Tukey transform as an executable
  recursion on `Fin (2^n)`, proved equal to the naive transform for any `ω`
  with `ω^(2^n) = 1`, with an exact count of `n * 2^(n+1)` ring multiplications
  and additions, i.e. `2 N log₂ N`. Twiddle powers are taken as given and the
  count is of ring operations, not tape steps.
- `NLogN/Recurrence.lean`: the Harvey-van der Hoeven master recurrence in the
  abstract. A normalized cost satisfying `T(n) ≤ ρ T(n') + C` with `ρ < 1` and
  `n' < n` is uniformly bounded, so a multiplication cost satisfying the
  corresponding `n log n`-scaled recurrence is `O(n log n)`; also the geometric
  tail bound. Nothing here constructs an algorithm or establishes the
  recurrence for an actual cost.
- `NLogN/Kronecker.lean`: the reduction of integer multiplication to digit
  convolution. Acyclic convolution of digit lists evaluates to the product,
  with a coefficient bound; a cyclic convolution of sufficient length equals
  the zero-padded acyclic one; bit strings chunk into base `2^k` digits with
  each chunk below `2^k`, connected to the machine's `binaryValue`. Carry
  propagation of the convolved digits back to bits is not yet implemented.
- `NLogN/FixedPoint.lean`: the radix-2 transform over `ℂ` with an arbitrary
  per-step error of size at most `ε` deviates from the exact transform by at
  most `(2^n - 1) ε`, the exact transform grows by at most `2^n`, a complex
  value within `1/2` of an integer rounds to it exactly, and the product error
  bound. The forward, pointwise, inverse error budget is not yet assembled.
- `NLogN/Carry.lean`: carry propagation from unnormalized convolution digits
  to proper base-`B` digits preserving the value, fixed-width truncation, and
  packing of base `2^k` digits into a most-significant-first bit string of
  exactly `k * L` bits whose `Machine.binaryValue` is the digit value. This is
  the output side of `Machine.outputCorrect`, at the list level only.
- `NLogN/Multidim.lean`: convolution transports along any additive group
  isomorphism, so by the Chinese remainder map a cyclic convolution of coprime
  composite length is a two-dimensional one; the two-dimensional transform
  factors into row and column transforms and satisfies the convolution
  theorem. Higher dimensions follow by iterating; the `d`-fold form is not
  stated.
- `NLogN/ErrorBudget.lean`: the total error of the perturbed forward,
  pointwise, inverse pipeline against the exact one, an explicit envelope
  `5 * 4^n * A * ε`, and the precision statement: `2n + 4 + log₂ A` fixed-point
  bits make the rounded perturbed pipeline return the exact integer vector
  whenever the exact pipeline is integral.
- `NLogN/Pipeline.lean`: the complex FFT multiplier as a function on
  `Fin (2^n)`: inversion of the naive transform, the convolution theorem on
  `Fin`, and the proof that forward transform, pointwise product, inverse
  transform, division by `2^n`, and rounding return exactly the product of two
  digit lists. Exact arithmetic over `ℂ`; the fixed-point version is covered by
  the error budget, and nothing is compiled to tapes.
- `NLogN/Gaussian.lean`: summability of Gaussians over the integers, an
  explicit geometric tail bound, the periodized Gaussian with its periodicity
  and explicit uniform upper and lower bounds, and the Poisson summation
  identity for Gaussians re-exported from mathlib. These are the analytic
  inputs to Gaussian resampling; the resampling map itself is not yet defined.
- `NLogN/MultidimD.lean`: the `d`-dimensional transform on a product of
  cyclic groups, its convolution theorem, orthogonality, inversion up to the
  product of the lengths, and the splitting of the first coordinate into a
  one-dimensional transform of lower-dimensional transforms.
- `NLogN/Primes.lean`: from Bertrand's postulate, a strictly increasing chain
  of distinct odd primes above any seed with explicit growth, pairwise
  coprimality, and bounds on their product. This is the prime-selection step
  without the short-interval prime theorems the paper cites.
- `NLogN/Multiplier.lean`: the assembled fixed-point FFT multiplier on bit
  strings. With chunk size `k`, transform length `2^m`, and `2m + 4 + k` bits
  of precision, the rounded perturbed pipeline followed by carry propagation
  returns the exact `2n`-bit product for every pair of `n`-bit inputs; the
  parameter choice `m = ⌈log₂ 2L⌉` fits, and the count is `6 m 2^m + 2^m`
  fixed-point complex operations. Chunking, rounding, carries, twiddles, and
  tape steps are not counted.
- `NLogN/Neumann.lean`: the linear-algebra skeleton of the resampling
  inversion. A map `1 + E` with `‖E‖ < 1` has an inverse of norm at most
  `1/(1 - ‖E‖)`; given the resampling identity and a normalized square
  subsystem, the source transform factors as `B ∘ (target transform) ∘ A`
  with explicit norm bounds, and after scaling as `2^γ B F A` with
  `‖A‖, ‖B‖ ≤ 1`; diagonal and coordinate-selection maps have the expected
  operator norms. The analytic hypotheses are not yet discharged.
- `NLogN/Bluestein.lean`: Bluestein's chirp identity for even lengths, in one
  and `d` dimensions: the transform is a chirp multiplication, a cyclic
  convolution with the chirp, and another chirp multiplication, so a
  power-of-two transform reduces to a convolution.
- `NLogN/Approx.lean`: the fixed-point approximation framework. Rounding
  toward zero at `p` bits with its norm bounds, the scaled error of vector and
  map approximations as predicates, error propagation through a map of norm
  at most one, through compositions, through bilinear maps, through rounded
  products, and through slice-wise application in a tensor factor.
- `NLogN/Synthetic.lean`: principal roots of unity, transform inversion over
  an arbitrary commutative ring from the principal-root property alone, the
  synthetic ring `ℂ[y]/(y^r + 1)` with `y^(2r/t)` a principal `t`-th root for
  every power of two `t ∣ 2r`, and the exact synthetic FFT and its inverse.
  The coefficient norm bound on products in the synthetic ring is not here.
- `NLogN/CRTMulti.lean`: the `d`-fold Agarwal-Cooley transport. Through the
  Chinese remainder isomorphism, a cyclic convolution whose length is a
  product of pairwise coprime moduli is the `d`-dimensional convolution, the
  `d`-dimensional transform is injective over a domain, and the convolution
  is recovered from the pointwise product of transforms; strictly increasing
  primes are pairwise coprime.
- `NLogN/MainRecurrence.lean`: Corollary 5.5 and the final induction of the
  paper, stated abstractly: a cost satisfying the recursive inequality
  `M(n) ≤ 12 T/r · M(3rp) + A n log n` with the parameter facts
  `T p ≤ 48 n`, `3rp < n`, and `log(3rp) ≤ (1/d + 1/(2d²)) log n` has
  normalized cost contracting by `1728/d · (1 + 1/(2d)) ≤ 0.9998` at
  `d = 1729`, hence `M(n) = O(n log n)`. The recursive inequality itself is
  a hypothesis here.
- `NLogN/Resampling.lean`: the Gaussian resampling identity, Theorem 4.2 of
  the paper, for all positive lengths `s`, `t` and every `α > 0`: the
  Gaussian-weighted resampling maps `S` and `T` intertwine the length-`s` and
  length-`t` transforms up to the two index permutations. Proved from shifted
  Poisson summation, derived from mathlib's Jacobi theta functional equation.
  Norm bounds on the resampling maps and the inversion of `T` are not here.
- `NLogN/MainReduction.lean`: steps one and three of the paper's recursive
  step. An `n`-bit product is the length-`S` cyclic convolution of its
  `b`-bit digit vectors, with product digits below `2^(3b)`; the scaled
  convolution `w = (u ∗ v)/S` of the `2^(-b)`-scaled digit vectors is
  recovered exactly by rounding `2^(2b) S w'` from any approximation within
  `1/(2 · 2^(2b) S)`, and the rounded list evaluates to the product.
- `NLogN/NormFFT.lean`: the normalized radix-2 transform with abstract
  isometric twiddles over any normed space, its norm bound, linearity, and
  the fixed-point error bound of `n ε` after `n` levels; the complex instance
  equals `2^(-n)` times the plain FFT and packages as an approximation of the
  normalized transform with scaled error `n = log₂ N`, the paper's Lemma 3.2
  over `ℂ`. The synthetic-ring instance is not yet connected.
- `NLogN/FixedOps.lean`: the elementary fixed-point operations. Fixed-point
  numbers at `p` bits are closed under sums and integer scaling and are fixed
  by rounding; a rounded half-sum or half-difference adds at most one unit of
  scaled error, integer scaling multiplies the error, and rounded products
  add two units; the negacyclic product of coefficient vectors satisfies
  `‖ab‖ ≤ r ‖a‖ ‖b‖`, and multiplication by a power of `y` is a signed shift
  of norm one. Bit costs and the bridge to the synthetic ring quotient are
  not here.
- `NLogN/MainParams.lean`: the paper's Section 5.1 parameter selection as
  natural-number definitions: chunk size `b = ⌈log₂ n⌉`, precision `6b`,
  `α`, `γ = 2dα²`, the power-of-two transform size `T` in `[4n/b, 8n/b)`, the
  root size `r` with `T ≤ r^d < 2^d T`, and the factorization of `T` into
  `d` powers of two bounded by `r`; with the inequalities `α² < p`,
  `γ < b − 13`, `T < n < 2^p`, `2^(2d) ≤ T`, and the product comparison
  behind `S > T/2`. The short-interval prime selection is not here.
- `NLogN/ResamplingNorm.lean`: Lemma 4.5 of the paper in its sharp form: the
  periodized Gaussian is at most `1 + √(π/a)` by comparison with the Gaussian
  integral, so the resampling map `S` has sup-norm at most `1 + 1/α`,
  uniformly in the lengths.
- `NLogN/TensorApprox.lean`: the two-factor case of the paper's tensor
  lemma: slice-wise application along either factor preserves approximation
  error and unit norm, the composed tensor approximation has the sum of the
  errors, and the normalized two-dimensional transform is exactly the tensor
  of the two normalized one-dimensional transforms. The `d`-fold version is
  not written.
- `NLogN/BluesteinApprox.lean`: the error bookkeeping of the paper's
  Theorem 3.1 in one and `d` dimensions: with an approximate chirp of scaled
  error `εa`, an approximate normalized convolution of scaled error `εM`, and
  rounded pointwise products, the Bluestein pipeline approximates the
  normalized transform with scaled error at most `εM + 3 εa + 4`. The
  normalized convolution is bounded and bilinear on unit balls.
- `NLogN/Section5Approx.lean`: the error bookkeeping of the paper's
  Propositions 5.2 and 5.3: a three-fold composition of unit-norm maps has
  the sum of the errors, scaling by a natural number scales the error, so a
  transform factored as `2^γ B F A` is approximated with error
  `2^γ (εB + εF + εA)`; and the forward, rounded pointwise, inverse
  convolution has error `εI + 2 εF + 2`, scaled by the length.
- `NLogN/ResamplingInverse.lean`: Section 4.2 of the paper. The row
  selection `C`, the square subsystem `T′ = C T` with its explicit series,
  the diagonal normalization `D` with `1 ≤ d_ℓ ≤ e^(πα²/4)`, the identity
  `N = T′ D = 1 + E`, and Lemma 4.6: under `α²θ ≥ 1` every entry of `E u`
  is at most `2.01 e^(−πα²θ/2) ≤ 1/2` on the unit ball. The operator-norm
  packaging and the assembly `D N⁻¹ C` are not here.
- `NLogN/TensorApproxD.lean`: the paper's tensor lemma with `d` factors:
  applying approximations coordinate by coordinate preserves unit balls, has
  operator norm at most one, and accumulates the sum of the errors; and the
  normalized `d`-dimensional transform is exactly the tensor of the
  normalized one-dimensional transforms.
- `NLogN/SynthFFT.lean`: the synthetic transform in coefficient form.
  Multiplication by `y^e` in `ℂ[y]/(y^r + 1)` is a signed cyclic shift of
  norm one with the semigroup law and period `2r`; the normalized radix-2
  recursion with shift twiddles computes the synthetic transform exactly,
  is a contraction, and has fixed-point error at most `n ε` after `n`
  levels, the paper's Lemma 3.2 for the synthetic ring.
- `NLogN/ResamplingCLM.lean`: the normalized transform, the two index
  permutations, and the resampling maps `S` and `T` as continuous linear
  operators with `‖F‖, ‖P‖ ≤ 1` and `‖S‖ ≤ 1 + 1/α`; `P_s` is invertible
  for coprime lengths with contractive inverse; the resampling identity as an
  operator equation; and fixed-point approximability of any vector to two
  scaled units.
- `NLogN/NeumannApprox.lean`: the paper's Lemma 4.12. The truncated Neumann
  series of `(1 + E)⁻¹` with `‖E‖ ≤ 1/2` is within `2 · 2^(−K)` of the
  inverse; Horner evaluation with an approximate `E` and per-step rounding
  has scaled error `2(εE + ρ)` uniformly in the number of steps, so `p` steps
  approximate the inverse with scaled error `2(εE + ρ) + 1`.
- `NLogN/ResamplingApprox.lean`: the paper's Lemma 4.9. Restricting the
  resampling series of `S` to the `2m + 1` terms nearest the row centre
  loses at most `(2/α)` times a Gaussian tail, which is below `3/(α 2^p)`
  once `m² ≥ p α²` and `α² ≤ p`; summing per-term fixed-point approximations
  of scaled error `c` gives total scaled error `c (2m + 1) + 3`. The
  per-term evaluation cost is not modeled.
- `NLogN/ResamplingAssembly.lean`: Proposition 4.7(i) of the paper. The row
  selection, diagonal normalization, and off-diagonal part are operators
  with `C T D = 1 + E` and `‖E‖ ≤ 1/2`; any left inverse of `1 + E` has
  norm at most two; and for `s < t` coprime, `α ≥ 1`, and `α²θ ≥ 1`, the
  length-`s` transform factors as `2^(2⌈α²⌉ + 2) · B ∘ F_t ∘ A` with explicit
  `A = S/2`, `B = P_s⁻¹ D J C P_t / 2^(γ−1)`, and `‖A‖, ‖B‖ ≤ 1`.
- `NLogN/SynthConv.lean`: the synthetic ring in coefficient form is an
  associative, commutative, unital algebra on which powers of `y` act by
  shifts; the synthetic transform of a cyclic convolution of ring-valued
  vectors is `t` times the pointwise negacyclic product of the transforms,
  for any `t ∣ 2r`; and for `t` a power of two the inverse transform
  recovers the input up to `1/t`, by the half-period cancellation.
- `NLogN/OffDiagApprox.lean`: the paper's Lemmas 4.11 and 4.8. Restricting
  the off-diagonal series `E` to the `2m` terms with `0 < |h| ≤ m` loses at
  most a geometric tail, below `3/2^p` once `9m ≥ p`; summing per-term
  fixed-point approximations of scaled error `c` gives total `2mc + 3`; and
  a rounded diagonal entry in `[0, 1]` times a unit-ball value has scaled
  error at most four.
- `NLogN/SynthEmbed.lean`: Section 3.2 of the paper. Twisting the last
  coordinate by the `2r`-th roots of unity turns complex cyclic convolution
  of length `r` into the negacyclic product, the twist is an isometry with an
  inverse, and a cyclic convolution on `G × Fin r` for any finite group `G`
  is the `R`-valued convolution on `G` of the twisted slices, which covers
  the `d`-dimensional case.
- `NLogN/SynthConvApprox.lean`: the paper's Proposition 3.4 in one
  dimension over the synthetic ring: the normalized convolution equals
  `t r` times the inverse transform of the `1/r`-scaled pointwise products of
  the forward transforms; the inverse transform is the forward one at the
  negated index; and the pipeline computed with per-level error oracles and
  rounded products has scaled error at most `4n + 2` for `n ≤ 2^p`.
- `NLogN/ResamplingMulti.lean`: Theorem 4.1 of the paper. Rectangular
  tensor products of operators on sup-normed coordinate spaces are defined
  through matrix entries, compose and scale factorwise, and are contractions
  when the factors are; the normalized `d`-dimensional transform is the
  tensor of the one-dimensional ones; hence for coordinatewise coprime
  `s_i < t_i`, `α ≥ 1`, and `α²θ_i ≥ 1`, `F_s = 2^(dγ) · B ∘ F_t ∘ A` with
  `‖A‖, ‖B‖ ≤ 1`.
- `NLogN/SynthMultiD.lean`: the `d`-dimensional synthetic transform over
  the coefficient-form synthetic ring: coordinate splitting into a
  one-dimensional transform of lower-dimensional ones, the convolution
  theorem for any lengths dividing `2r`, orthogonality and inversion up to
  `1/∏ N_i` for power-of-two lengths, and contraction bounds for both
  directions.
- `NLogN/MainStep.lean`: Proposition 5.4 at the vector level. The
  normalized `d`-dimensional transform and its index-negated form are
  contractions with `F(a ∗ b) = S · Fa · Fb` and `F⁻ F = id/S`; the scaled
  digit convolution of the recursive step lives on the Chinese-remainder
  grid; and given approximations of the transform and its inverse with
  scaled errors `εF`, `εI`, the rounded output is the exact product whenever
  `2^(2b) S² (εI + 2εF + 2) < 2^(p−1)`. Discharging that precision condition
  from the parameter choices is not here.
- `NLogN/TensorApproxV.lean`: the `d`-fold tensor lemma for arrays with
  values in any normed space, indexed by `Fin`, in square and rectangular
  form: coordinatewise approximations preserve balls, have norm at most one,
  and accumulate the sum of the errors. The rectangular composition law is
  not proved here.
- `NLogN/ResamplingNumeric.lean`: Proposition 4.7(ii) of the paper. The
  numerical `Ã` from truncated Gaussian sums and the numerical `B̃` from the
  permutations, rounded diagonal, Horner-evaluated Neumann inverse with a
  truncated off-diagonal part, and row selection are approximations of
  `A` and `B` with explicit scaled errors, both below `p²` for the paper's
  per-term error seven. The per-term Gaussian evaluations and the clamping of
  the off-diagonal approximation into the unit ball are hypotheses.
- `NLogN/PrecisionCheck.lean`: the paper's parameter choices satisfy the
  recursive step's side conditions: with `b = ⌈log₂ n⌉`, `p = 6b`, `S ≤ T`,
  and transform errors at most `2^(γ+5) T log₂ T`, the precision condition
  `2^(2b) S² (εI + 2εF + 2) < 2^(p−1)` holds because `γ + 14 < b`; and the
  digit counts fit in the cyclic length whenever `T < 2S`.
- `NLogN/PowerOfTwoExact.lean`: the exact algebra of Theorem 3.1. The
  normalized synthetic convolution in `d` dimensions is `T′ r` times the
  inverse synthetic transform of the `1/r`-scaled pointwise products of the
  forward transforms; a normalized complex convolution on `G × Fin r` is the
  untwisted synthetic one; and for two power-of-two coordinates the complex
  transform is a chirp multiplication, a synthetic transform pipeline, and
  another chirp multiplication. More than two coordinates is not written.
- `NLogN/NegacyclicKronecker.lean`: the paper's Lemma 2.5 in exact
  arithmetic. The integer negacyclic product is the fold of the polynomial
  product; a signed product splits into four nonnegative ones; and for
  nonnegative inputs below `M` every coefficient of the polynomial product is
  a base-`r M² + 1` digit of one integer product of two packed numbers below
  `B^r`, so the negacyclic product is read off from a single multiplication
  of integers of about `3rp` bits. This is where the recursion enters.
- `NLogN/CostModel.lean`: an operation-count model for Section 3. The
  synthetic FFT recursion costs `2 r t log₂ t` word operations, the
  `d`-dimensional transform `2 r T′ log₂ T′`, and the convolution pipeline
  `4 T′ M(3rp)` delegated integer products plus `O(r T′ p log T′)` word
  operations; with the Section 5 parameters three pipelines cost at most
  `(12 T/r) M(3rp) + 2880 n log₂ n`, the shape of the main recursion. Tape
  steps, data rearrangement, and weight computation are not modeled.
- `NLogN/ResamplingMultiNumeric.lean`: the numerical half of Theorem 4.1.
  The rectangular coordinatewise tensor on Chinese-remainder grids preserves
  balls, accumulates the sum of the errors, and agrees with the matrix-defined
  tensor; hence the tensors of the one-dimensional numerical maps approximate
  `A` and `B` with scaled errors `d εA` and `d εB`, alongside the exact
  factorization.
- `NLogN/SynthConvApproxD.lean`: Propositions 3.3 and 3.4 of the paper in
  `d` dimensions. The `d`-dimensional synthetic transform is the tensor of
  the one-dimensional ones, so its coordinatewise numerical version has
  scaled error `∑ log₂ t_i`; the inverse is the forward transform at the
  negated index; and the convolution pipeline with rounded `1/r`-scaled
  products has scaled error exactly `3 log₂ T′ + 2` before the final scaling
  by `T′ r`. Unit-ball preservation of each one-dimensional FFT is a
  hypothesis.
- `NLogN/Clamp.lean`: the radial clamp of a complex number to the unit
  disk, applied coordinatewise, is nonexpansive against every point of the
  ball, so any approximation of a contraction can be clamped into the unit
  ball at no cost in scaled error; with a radius-`R` version. This supplies
  the unit-ball side conditions the composition lemmas require.
- `NLogN/PowerOfTwoNumeric.lean`: Theorem 3.1 of the paper for two
  power-of-two coordinates `t × r`: the numerical transform built from an
  approximate chirp, the rounded pre-multiplication, the twisted synthetic
  convolution pipeline, the untwist, and the rounded post-multiplication
  approximates the normalized transform with scaled error
  `t (4 log₂ t + 2εa + 4) + εa + 2`, at most `4 t log₂ t + 8 t + 4` for a
  chirp within two units. No unit-ball side conditions are needed.
- `NLogN/PowerOfTwoExactD.lean`: the exact chain of Theorem 3.1 for any
  number of coordinates: splitting off the last coordinate through an
  additive isomorphism, the normalized complex transform is a chirp
  multiplication, the untwisted `d`-dimensional synthetic pipeline over the
  ring of dimension `t_{d+1}`, and another chirp multiplication.
- `NLogN/MainTransform.lean`: Proposition 5.2 of the paper and its use in
  the recursive step. The scaled composition of the numerical resampling
  tensors with a numerical power-of-two transform approximates the
  prime-grid transform with error `2^γ (d εB + εFt + d εA)`, which the
  parameter choices bound by `2^(γ+4) T log₂ T` using `d p² ≤ 4 T log₂ T`;
  the index-negated version approximates the inverse; radial shrinking keeps
  outputs in the unit ball at the cost of a factor two; and the recursive
  step returns the exact product with only the power-of-two transform, the
  per-coordinate resampling maps, and the prime-choice condition as
  hypotheses.
- `NLogN/ExplicitNumeric.lean`: the numerical maps with every side
  condition discharged: per-term Gaussian weights rounded to `p` bits and
  multiplied with rounding, the off-diagonal part clamped into the unit
  ball, the Neumann inverse and `B̃` built from them, the synthetic FFTs
  clamped, and the `d`-dimensional synthetic pipeline restated with the
  clamped transforms; the multidimensional resampling tensors then
  approximate `A` and `B` with explicit errors below `d p²` and no
  hypotheses beyond the parameter ranges and the inverse identities.
- `NLogN/PowerOfTwoNumericD.lean`: Theorem 3.1 of the paper for any number
  of power-of-two coordinates: with numerical synthetic transforms of
  elementwise scaled error `S` and an approximate chirp within `εa`, the
  Bluestein pipeline approximates the normalized transform with scaled error
  `T′ (3S + 2εa + 4) + εa + 2`, at most `3 T′ S + 8 T′ + 4` for a chirp
  within two units. The synthetic transforms are abstracted by their error
  and ball properties, which the `d`-dimensional synthetic file supplies.
- `NLogN/ContractPrep.lean`: the recursive step with the resampling side
  fully explicit: at window `m = p` the parameter ranges hold, the clamped
  per-coordinate numerical maps approximate `A_i` and `B_i` with errors
  below `p²`, and the recursive step returns the exact product given only
  the prime choice, the size conditions, and a numerical power-of-two
  transform with error at most `8 T log₂ T`; plus the arithmetic showing
  the power-of-two transform's error shape meets that bound.
- `NLogN/PowerOfTwoContract.lean`: the explicit numerical power-of-two
  transform as the recursive step's input. For a grid of lengths `2^(e_i)`
  with last length `2^g`, the clamped Bluestein pipeline with clamped
  synthetic FFTs and a rounded chirp approximates the normalized transform
  with scaled error `2^S (3S + 8) + 4`, `S = ∑ e_i`, which is at most
  `8 T log₂ T`, and keeps the unit ball. The transforms of the resampling
  and Bluestein files are identified.
- `NLogN/RecurrenceParams.lean`: the parameter facts the final recurrence
  needs at `d = 1729`: `T p ≤ 48 n`, `2 ≤ 3rp < n`, and
  `log(3rp) ≤ (1/d + 1/(2d²)) log n`, the last through a real sixth root of
  the chunk size; hence any cost satisfying the recursive inequality with
  these parameters is `O(n log n)`.
- `NLogN/Contract.lean`: the headline correctness contract of the
  subroutine's recursive step in the vector model. For `n ≥ 2^(d^12)` there
  is a power-of-two grid of total size `T` bounded by `r`, and for every
  choice of moduli `s_i < t_i` pairwise coprime with `∏ s_i ∈ (T/2, T]` and
  `α²(t_i/s_i − 1) ≥ 1`, the fully explicit numerical algorithm, with
  per-level rounding oracles within `2^(−p)`, outputs exactly the product of
  the two `n`-bit inputs. The existence of such moduli, the paper's
  short-interval prime lemma, is the one remaining mathematical hypothesis;
  bit costs and tape compilation are separate.
- `NLogN/CostBound.lean`: the operation-count model closes the recursion.
  With the paper's grid, three convolution pipelines cost exactly
  `12 T/r` delegated products of size `3rp` plus `O(n log n)` word
  operations, so any cost function bounded by three pipelines plus a linear
  overhead for `n ≥ 2^(1729^12)`, and polynomially below, is `O(n log n)`.
- `NLogN/PrimeSelection.lean`: the paper's Lemma 5.1 and the moduli
  selection, downstream of one isolated hypothesis: Rosser and Schoenfeld's
  bound `y − y/(2 log y) < ϑ(y) < y + y/(2 log y)` for `y ≥ 563`, stated as
  a definition and never assumed globally. From it, every window
  `((1−2η)x, (1−η)x]` holds at least `ηx/(2 log x)` primes, a power-of-two
  grid of lengths at least `2^(d^9)` admits distinct primes in its windows,
  those moduli satisfy every condition of the recursive-step contract, and
  the explicit recursive step is exact with the moduli supplied. The
  Chebyshev bound itself is not in mathlib and remains the one external
  number-theoretic input.
- `NLogN/OffDiagApproxSqrt.lean`: the paper's Lemma 4.11 window. Under
  `α²θ ≥ 1` the off-diagonal terms decay like `e^(−2π(|h| − 1/2)²)`, so
  truncating to `|h| ≤ m` with `9 m² ≥ p` loses at most `3/2^p`; the clamped
  off-diagonal part, the Neumann inverse, and `B̃` keep their error bounds at
  the window `⌊√p⌋ + 1`, still below `p²`. This window is what makes the
  resampling maps cost `O(T p^(3/2+δ))`.
- `NLogN/ContractSqrt.lean`: the recursive-step contract with the paper's
  window sizes, `(⌊√p⌋ + 1) α` for the resampling sums and `⌊√p⌋ + 1` for
  the off-diagonal part, so that the numerical maps match the ones the cost
  model counts; the errors stay below `p²` and the contract's hypotheses are
  unchanged.
- `NLogN/ResamplingOps.lean`: operation counts for the resampling maps in
  the word model, mirroring the explicit numerics: with the paper's windows
  and `α² + 1` Neumann iterations the resampling part of a step costs
  `270 d T α (√p + 1)` per-term operations, which is `O(n log n)` whenever a
  weight evaluation plus a product costs quasilinearly in `p`; the `m = p`
  windows are shown quadratic and hence not enough. One full step then costs
  `(12 T/r) M(3rp) + O(n log n)`, and the recurrence closes to `O(n log n)`
  for any cost bounded by a full step plus linear overhead.

## Swap

Faster interchange of address chunks (§4).

- `Swap/Recurrence.lean`: the arithmetic of the chunk-interchange recurrence.
  A normalized cost satisfying `F (k+1) ≤ a F k + C` with `a ≤ m^τ` is bounded
  by an explicit constant times `(m^k)^τ`, with no case split on the ratio.
  The base-`m` digit pieces of a general width `n ≥ m^k` cost
  `O(n^τ)` in total, with the digit expansion `n = Σ (n / m^j % m) m^j`
  proved. Row padding to a multiple of `W^k ≤ R` stays below `2R`; the
  row-range digit count `⌈k log W / (2 log q)⌉` gives `q^(2ρ) ≥ W^k` and is
  eventually below the width; the least radix-`q` width covering `[2^u]` is
  at most `u` and inflates the range by less than `q`. The lower triangular
  factorization, the rational matrix shear, and the interchange procedure
  itself are separate obligations.
- `Swap/Shear.lean`: the algebra of the rational matrix shear. Field
  programs on two groups `H`, `D` consist of later-field updates `D_j ← D_j +
  H_i`, `D_j ← H_i - D_j`, interchanges of `H_i` with `D_j`, and within-group
  matrix transformations. One interchange and two later-field updates realize
  `H_i ← H_i + D_j`; a pivot list adds `Π D` to `H` for the matrix `Π` with a
  one at each listed position; with `E₁ E₁' = 1` and `E₂' E₂ = 1` the program
  transform `D` by `E₂`, `H` by `E₁'`, pivot, `H` by `E₁`, `D` by `E₂'`
  computes `H ← H + E₁ Π E₂ D` with exactly as many interchanges as pivots.
  A lower triangular transformation equals the strictly descending sequence of
  its coordinate updates, each reading only the original values, and each row
  reads only its own and earlier coordinates. Identities over any commutative
  ring; the modulus choice, the factorization, and tape costs are separate.
- `Swap/LowerTriangular.lean`: Lemma 4.1. Every matrix over a field, square or
  rectangular, is `E₁ Π E₂` with `E₁`, `E₂` lower triangular with explicit
  lower triangular two-sided inverses and `Π` the pivot matrix of a list with
  distinct rows and distinct columns. The elimination keeps finite active row
  and column sets: the topmost nonzero active row and its rightmost nonzero
  entry give the pivot, a square-zero lower triangular column operation clears
  the pivot row, a square-zero lower triangular row operation clears the pivot
  column, the pivot is scaled to one and subtracted, and strong induction on
  the number of active indices finishes. Factors act as the identity outside
  the active sets, which makes the pivot commute with the residual factors.
  The identification of the pivot count with the rank is in `PivotRank`.
- `Swap/PivotRank.lean`: the pivot count of a factorization is the rank. A
  pivot matrix `Π` with distinct rows and distinct columns has entries given
  by list membership, `Πᵀ Π` is the diagonal indicator `D` of its columns, and
  `Π D = Π`, so `rank Π = rank D` equals the number of pivots over any field;
  the invertible triangular factors do not change the rank. Lemma 4.1 is thus
  complete: every matrix over a field factors with exactly `rank A` pivots.
- `Swap/Modular.lean`: Lemma 4.2, the specialization to `ℤ/q^bℤ`. Rationals
  with denominator prime to `m` form a subring of `ℚ`, and `num · den⁻¹` is a
  ring homomorphism from it to `ZMod m`, proved through the integer identities
  behind fraction addition and multiplication and cancellation of coprime
  denominators. Entrywise reduction of admissible matrices preserves products,
  the identity, inverse pairs, lower triangularity, and pivot matrices, so a
  rational factorization reduces to one over `ZMod m` with the same pivots.
  For a finite collection of rational matrices there is an odd prime `q`
  beyond every denominator of the chosen factorizations, and modulo every
  `q^b` each matrix `A` has a shear program computing `H ← H + A D` with
  exactly `rank A` interchanges, all other operations being lower triangular
  transformations and later-field updates. The `O(V)` tape cost of those
  operations is a separate obligation.
- `Swap/Interchange.lean`: the mathematics of Proposition 4.3. The three
  steps `D ← D - H`, `H ← H + D`, `D ← H - D` interchange the two chunks. The
  field programs of `Shear` realize the address permutation `Φ_M` of
  `ShearFrame` for the reduced matrix, so modulo every power of a suitable
  prime every matrix of a finite collection, and every edge of a labeled
  schedule, has a program with exactly its rank in interchanges, the schedule
  total being the sum of the edge ranks. Under the finite shear contract
  `M_out (ρ w) - M_in w = I` and a logical circuit routing role `w` to `ρ w`,
  the framed circuit's physical output at `ρ w` is the full shear of the input
  at `w`, for every wire including scratch roles. The recursion
  `time (k+1) V ≤ s · time k (V / W) + C V` with `s / W ≤ m^τ` gives
  `time k V ≤ K (m^k)^τ V` with an explicit constant. The role-stream split,
  the depth-first fixed-tape schedule, and descriptor processing are tape
  obligations.
- `Swap/ArbitraryWidth.lean`: the cost assembly of Lemma 4.4. For binary
  chunks of width `u`, the radix width `e` is at least one and at most `u`,
  the row-range digit count `ρ` gives a row field of range at least `W^k`, and
  the remaining width is split into base-`m` pieces. With per-volume overhead
  `A (ρ + log (2e) + 1)` for the high-digit moves, padding, descriptors, and
  cleanup, and the power-width calls on less than twice the volume, the total
  per unit volume is at most `K u^τ` for every `u ≥ 1`, with `K` explicit and
  independent of `u`; the logarithms are absorbed uniformly, not only
  eventually. The field-order bookkeeping of the construction is a tape
  obligation.
- `NLogN/ModuliConstruction.lean`: an elementary replacement for the paper's
  Lemma 5.1. The moduli need only be odd and pairwise coprime, so each is a
  product of powers of two coordinate-specific odd primes whose exponents are
  found by pigeonhole in log scale; this lands in every window once the
  lengths exceed a double exponential in `d`. Hence the explicit recursive
  step is exact with no number-theoretic hypothesis at all, for
  `n ≥ 2^(2^(1000 d³))`, a threshold larger than the paper's but still a
  constant.
- `NLogN/ContractFinal.lean`: the headline theorem in its final form: for
  `n ≥ 2^(2^(1000 d³))` and any `n`-bit inputs, the explicit numerical
  recursive step with the paper's window sizes and elementarily constructed
  moduli computes the exact product, given only per-level rounding oracles
  within `2^(−p)`; instantiated at `d = 1729`.
- `NLogN/SmallMultiplierCost.lean`: the plain FFT multiplier with chunk size
  `⌈log₂ q⌉`, zero rounding error, and schoolbook word arithmetic multiplies
  two `q`-bit integers exactly within `10^6 · q · (log₂ q)²` bit operations;
  this fixed quasilinear bound serves the small products inside the weight
  evaluations of the main algorithm.
- `NLogN/ExpEval.lean`: the paper's Lemma 2.13 at the model level. The
  Taylor series with about `8 p / log₂ p` terms is within `2^(−p)` on
  `|x| ≤ 1`; `e^(−z)` reduces to a power of `e^(−1)` times a Taylor sum with
  error `3(⌊z⌋ + 1) · 2/K!`; and the binary-splitting recurrence with
  superadditive multiplication cost evaluates such a series in
  `O(M(80p) log p)` operations, the `O(p^(1+δ))` shape. The exact product tree
  and the `p`-bit approximation of `π` times a rational are not written.
- `NLogN/JointRecurrence.lean`: the cost recurrence closed with no
  hypothesis about the main cost on the resampling side: with the delegated
  `3rp`-bit products costed by the cost being bounded and the `p`-bit
  products inside the weights by an a priori quasilinear multiplier, any cost
  bounded by one full step plus linear overhead above `2^(2^624)` and
  polylogarithmically below is `O(n log n)`. The explicit constants need the
  larger threshold.
- `NLogN/ExpCostBound.lean`: the concrete weight-evaluation cost: with the
  plain multiplier's monotone superadditive envelope `10^6 q (log₂ q + 1)²`
  as the multiplication cost, one Gaussian weight to `q` bits costs at most
  `2 · 10^11 · q (log₂ q + 1)³` operations, which supplies the joint
  recurrence's quartic-log hypothesis, and the envelope itself is cubic-log.
- `NLogN/CostFinal.lean`: the final cost theorem of the subroutine in the
  operation-count model: any cost that, above `2^(2^624)`, is bounded by one
  full recursive step (three convolution pipelines with the delegated
  `3rp`-bit products at the recursive cost, plus the resampling maps with the
  paper's windows, the plain-multiplier envelope for the small products, and
  the binary-splitting exponential cost for the weights) plus a linear
  overhead, and polylogarithmically below, is `O(n log n)`. The grids and
  moduli are parameters; the correctness theorem supplies them above its own
  larger threshold.
- `NLogN/Capstone.lean`: the capstone of the subroutine. Above
  `2^(2^(1000 · 1729³))` the grids and moduli are chosen once as functions
  of `n`; with that choice the explicit recursive step with the paper's
  windows computes the exact product of any two `n`-bit inputs, and any
  cost bounded by one full step on the same grids and moduli with concrete
  small-product and weight-evaluation costs, plus linear overhead, is
  `O(n log n)`. Tape steps are not modeled.

## Top-level

Parameters and asymptotics.

- `Asymptotics.lean`: logarithmic powers are little-o of every strictly larger
  real power, specialized to all seven assembly margins; a finite-depth,
  volume-normalized recurrence bound with explicit leaf and overhead costs.
- `Parameters.lean`: every stated rational parameter slack, all seven assembly
  margins, their attained minimum and strict absorption gap, the two dyadic
  comparisons, the complex motif counts, and the strict complex branching-ratio
  bound. The logarithm enclosure is proved from a finite exponential-series
  lower bound inside Lean. These do not establish the motif's circuit interface
  or the costs of an implementation.
- `Shared50Parameters.lean`: exact h=50 two-bank counts, positive deficit,
  finite exponential-series logarithm enclosure and strict branching inequality
  for the selected tau. Converting the numerical budget into an actual circuit
  bound still requires its proved rank balance and loss estimate.
