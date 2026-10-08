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
- `Machine/Branch.lean`: a finite-state conditional testing only scanned
  symbols. One transition enters the selected branch with every tape and head
  preserved, and the branch's halt halts the whole machine. The contract
  charges the larger branch bound plus one.
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
- `Machine/BinaryCompare.lean`: a fixed three-tape, four-state comparator for
  LSF binary words of unequal widths, reading a missing high bit as zero and
  keeping the order so far in control. It writes one bit, whether the first
  operand is strictly smaller, at the output head and preserves both operands
  with each head parked on its own blank end; cost the larger width plus one,
  with the exact value correspondence proved.
- `Machine/BinaryAccumulate.lean`: a fixed two-tape, three-state in-place
  adder: the addend is scanned together with the accumulator, a missing high
  bit on either tape read as zero, each column sum written back over the
  accumulator and a final carry extending it by one cell. The addend is
  preserved and its head parks on the addend's blank end, so a plain rewind
  returns it; the exact sum word, its value and width bounds, and the cost of
  the larger width plus one are proved.
- `Machine/ExactFrame.lean`: exact-bank forms of the extend and reindex rules
  for any alphabet, a halting empty program for conditional branches, the
  rewind to a word's origin from an arbitrary position over an arbitrary
  background, and two one-tape moves, step left and prepend a zero bit.
- `Machine/BinaryMultiply.lean`: a fixed three-tape, seventeen-state
  multiplier by Horner's rule. The multiplier is read from its most
  significant bit down; each bit doubles the accumulator by writing a zero one
  cell left of its origin and, when set, adds the multiplicand in place and
  rewinds both heads, so the accumulator's origin moves left one cell per bit
  and no word is copied. Both operands are preserved, the accumulator holds
  the exact product with a proved width bound, and the cost is at most
  `m(5w + 2m + 18)` for a `w`-bit multiplicand and `m`-bit multiplier.
- `Machine/BinaryDecrease.lean`: a fixed two-tape, two-state in-place
  subtractor: the subtrahend is scanned together with the minuend, a missing
  high bit read as zero, each column difference written back over the minuend
  with the borrow in control, halting on the common blank. The subtrahend is
  preserved with its head parked on its end; the modular difference word, its
  exact value without underflow and the cost of the common width are proved.
- `Machine/PrependRead.lean`: a two-tape, four-state move that reads the bit
  under the first head, optionally steps that head left, and writes the bit
  or its negation one cell left of the second head, in two transitions.
- `Machine/BinaryDivide.lean`: a fixed five-tape, thirty-three-state
  restoring long divider. Each dividend bit, from the most significant down,
  is prepended to the remainder, the remainder is compared with the divisor,
  the divisor is subtracted in place when it fits, the quotient bit is
  prepended to the quotient word and the one-cell comparison flag is erased;
  remainder and quotient origins move left one cell per bit. Dividend and
  divisor are preserved, the remainder and quotient words have the exact
  values, and the cost is at most `m(4m + 6k + 27)` for an `m`-bit dividend
  and `k`-bit divisor.
- `Machine/WordMoves.lean`: scan to a blank-terminated word's end, copy a
  word onto another tape, erase a word backwards onto a blank background
  returning to its origin, and copy a fixed number of cells with blanks read
  as zero bits, the last unrolled with a state count linear in the count.
  Each has an exact contract and transition count.
- `Machine/ColumnTransducer.lean`: a generic three-tape column transducer on
  equally padded words, a finite control reading one bit from each operand and
  writing one output bit, halting on the common blank in exactly the common
  width with both operands preserved. Modular addition (sum modulo two to the
  width) and bitwise exclusive or are proved instances.
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
- `Machine/StripPrefix.lean`: a fixed three-tape, four-state routine removes
  a unary-counted key prefix from every raw record: it rewinds the width tape
  from wherever the sorter left it, then per record advances over the prefix
  in lockstep with the width tape, rewinds it, and copies the remainder. Source
  and width tapes are retained; exact runtime is the input volume plus the
  width plus two per record, plus the initial rewind.
- `Machine/ReturnOrigin.lean`: a one-tape, three-state routine returns a head
  from the end of a blank-backed nonblank word to its origin in the word
  length plus two transitions, retaining the tape.
- `Machine/RepairStage.lean`: one fixed eleven-tape machine sequences the
  radix sorter, the prefix stripper, the head return, and the alphabet-widened
  reinserter. Keyed records (key bits then the flagged record) are sorted by
  key, stripped, and reinserted into the flagged full stream; the exact-run
  contract lists every tape and head, and the cost is at most `74k + 4`
  extracted volumes plus one full-stream volume plus `k + 7`. Radix sorting
  commutes with key-preserving record maps.
- `Machine/FlagCopy.lean`: a four-tape, six-state routine rewrites one
  record's flag from a key tape and, when the flag is set, moves the key's
  destination bits to the extracted stream and copies the record behind them
  in the raw keyed format, erasing the key tape back to its marked blank
  state. Exact cost: the record length, plus twice the key width plus three
  when flagged.
- `Machine/MarkedReturn.lean`: a one-tape, three-state routine returns a head
  from the end of a word to its origin over either a blank or a marked
  background in the word length plus two transitions.
- `Machine/LoopChain.lean`: a while loop whose iterations form a chain of
  exact-tape contracts runs from the first bank to the last within the sum of
  the iteration bounds plus two control transitions each.
- `Machine/RepairScan.lean`: the flagging and extraction scan of the
  exceptional-address repair on the fourteen-slot repair bank. A binary rank
  counter drives a loop whose body runs a key routine (a program parameter
  with a per-rank contract: read the counter, write the flag and destination
  bits), the flag copier, and the counter increment; two head returns and the
  sort-strip-reinsert stage follow. The complete machine has an exact-run
  contract, and its cost is the key cost plus ten per record, three stream
  volumes, `74k + 5` extracted volumes, `2k + 3` per extracted record, and
  `k + 14`.
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

- `Machine/CountedRotate.lean`: Literal six-tape, sixty-four-state raw cyclic rotation: seek past a prefix, copy the suffix, seek backwards over the total block, and copy the prefix. The source and three immutable descriptors are preserved and the clock is restored. Exact single-fiber controlled-shift semantics follow from block payload indexing; all seeks, clock setup/cleanup and joins cost at most fifteen times volume plus descriptor-width terms. Descriptor synthesis and multi-fiber scheduling remain open.

- `Machine/CountedLoop.lean`: A fixed finite-state binary-counted body loop with a dedicated final clock tape. Actual Hoare chains with varying body costs execute in their summed costs plus at most six times the iteration count, twice the clock width and two. All decrement scans, returns, body joins and terminal underflow are charged; the clock finishes all ones. Preparation and cleanup remain explicit.

- `Machine/GrowingCounterData.lean`: Growing-width binary increment from the empty zero word, exact value increment, canonical highest-one invariant and logarithmic width. A bit-weight potential bounds all increment-and-return costs by four times the increment count plus twice initial width.
- `Machine/GrowingCounter.lean`: Literal growing binary increment writes a new high bit at the end blank and returns to its sentinel. Exact execution and halting, canonical growth from an empty marked tape and amortized costs including cycle joins are proved; no counter width is prepared in advance.
- `Machine/BinaryLength.lean`: Literal two-tape, six-state scanner constructs a canonical binary source-length descriptor from an empty marked counter. The source is preserved, its first blank causes true halt, and all growth, movement and joins cost at most eight transitions per source symbol. Internal blank payloads are excluded by the source contract.
- `Machine/BinaryLengthInit.lean`: Initializes the counter sentinel from a genuinely blank second tape, then measures the source. Exact execution costs at most eight times source length plus two; canonical output and logarithmic width are proved. The literal standard multiplication input is covered, including its separator symbol.

- `Machine/CountedRotateAdvance.lean`: Literal cyclic block rotation followed by a charged suffix seek, so both payload heads reach the next block. Source and descriptors survive, the reusable clock is empty, and all routines and joins cost at most fifteen times block length plus descriptor-width terms.
- `Machine/WordSegments.lean`: Exact local tape-word indexing and matching-segment replacement. A middle word of a placed concatenation is already present at its length-offset origin; these representation identities justify local stream views without asserting free tape operations.
- `Machine/FiberShift.lean`: A fixed seven-tape, eighty-five-state counted controller rotates successive uniform raw fibers by a common prepared cut. Source and prior output are preserved, both data heads advance the entire volume, and inner controls reset. Canonical prepared descriptors and nonempty fibers give actual runtime at most 177 times payload volume plus four; outer count preparation/cleanup and varying offsets remain separate.

- `Machine/CountedLoopReuse.lean`: Generic fixed counted body loop with an immutable count descriptor. Physically prepares the mutable clock, runs the counted body chain, erases the clock and resets both control heads, preserving the descriptor. All body costs plus six times the count, seven times descriptor width and sixteen bound the actual execution. Public metadata cleanup also erases any padded binary word and resets its head while preserving an immutable companion descriptor, charging both scans.
- `Machine/FiberShiftReuse.lean`: Fixed eight-tape, ninety-six-state common-offset fiber shifts with full inner and outer clock cleanup. Source and four immutable descriptors survive; both data heads advance the full volume. Canonical prepared descriptors and nonempty fibers give actual runtime at most 182 times payload volume plus twenty-three.
- `Machine/FiberShiftAddress.lean`: Instantiates the reusable fiber machine as actual forward target-coordinate translation modulo Q on arbitrarily many Q-by-B fibers, preserving every intra-block payload position. The same linear-volume execution restores all clocks; the common offset and derived binary descriptors remain explicit prepared inputs.

- `Machine/BlockReverseAdvance.lean`: Literal four-tape, fifty-two-state reversal of a raw block with both payload heads finishing at the next block. Two counted seeks, a backwards read-copy, two single-cell moves and all four joins cost at most fifteen times length plus twenty-one times descriptor width plus fifty-four, including empty blocks.
- `Machine/BlockReverseStream.lean`: Fixed five-tape, fifty-seven-state counted repetition reverses each uniform block while preserving block order, source and prior output. Both heads advance the full volume and inner controls reset; canonical descriptors and positive width give actual runtime at most 119 times volume plus four. The outer count remains consumed.
- `Machine/BlockNegation.lean`: Complete literal seven-tape, 141-state single-fiber coordinate negation. Copies block zero, reverses the raw tail onto scratch, physically rewinds scratch and reverses each popped block to restore internal payload order. All moves and three joins cost at most 200 times volume plus 128 for positive width and canonical descriptors. Full source and descriptor preservation are proved; dirty scratch and consumed outer count are explicitly tracked.

- `Machine/Dispatch.lean`: Literal dispatch among a fixed finite family of programs using only scanned symbols. One stationary tape-preserving transition selects the branch, and exact execution, true halt and Hoare contracts add exactly one step to the selected body cost.
- `Machine/ScalingMergeData.lean`: Sequential FIFO semantics for positive unit scaling. Prefix selection counts equal the inverse source offset within each contiguous piece; selected streams never underflow, all pieces are completely consumed and recursive head-pop merging gives the exact inverse-scaled payload. Pure semantics only; no tape runtime is asserted.

- `Machine/CountedErase.lean`: Delimiter-free scratch erasure using a literal one-cell body and reusable counted loop. Preserves all cells outside the interval and restores an initially blank scratch segment, with immutable descriptor and empty clock restored. Actual cost is at most seven times length plus seven times descriptor width plus sixteen, or fourteen times length plus twenty-three for canonical descriptors.
- `Machine/OneHot.lean`: Fixed finite residue encoding on control tapes under their current heads. Decoding reads scanned symbols only, and one literal stationary transition increments the residue modulo the fixed bank size, preserves every head and background cell and truly halts. Exact execution and Hoare contracts charge one step.

- `Machine/ScratchReset.lean`: Fully reusable raw scratch cleanup: physically rewind from the segment end, erase the exact interval, and rewind to its origin. Initially blank scratch is restored including its head, while surrounding cells and immutable length descriptor survive. All three routines and joins cost at most seventeen times length plus twenty-one times descriptor width plus fifty, or thirty-eight times length plus seventy-one with a canonical descriptor.
- `Machine/BlockReverseStreamReuse.lean`: Fixed six-tape, sixty-eight-state blockwise reversal with immutable block-count and block-width descriptors. Both inner and outer mutable clocks are prepared and cleared, control heads reset, and payload heads advance the full volume. Canonical descriptors and positive block width give actual runtime at most 124 times payload volume plus twenty-three.

- `Machine/ScalingSplit.lean`: Literal fixed-coefficient partition into contiguous source pieces on separate tapes. A fixed sequence of reusable counted copies preserves the source and all piece-length descriptors, with exact output words and final heads, including empty pieces. Cost is five times volume plus seven times the sum of descriptor widths plus seventeen times the fixed piece count, or twelve times volume plus twenty-four times piece count for canonical descriptors.
- `Machine/ScalingMerge.lean`: Literal fixed-coefficient FIFO merge via scanned-symbol dispatch, counted block copies and one-hot residue updates. Actual repeated execution writes the exact inverse-scaled payload, preserves source tapes, descriptors and modulus control, and clears both clocks. Prepared canonical descriptors and positive block width give at most fifty-one times volume plus twenty-three steps. Source heads initially at piece starts and residue banks are explicit prerequisites.
- `Machine/ScalingPieceBridge.lean`: Exact representation bridge from flat literal split pieces to contiguous block streams consumed by the merge. Proves arbitrary uniform-block interval slicing and preserves every intra-block cell, including zero-width blocks and empty pieces. This is a representation equality, not a free tape move.

- `Machine/BlockNegationReuse.lean`: Complete eight-tape, 202-state reusable coordinate negation: copy block zero, reverse the raw tail, physically rewind, reverse individual blocks with reusable controls, then erase and rewind scratch. Source/descriptors survive; both clocks and the entire initially blank scratch interval with its original head are restored. Canonical prepared descriptors and positive width give actual cost at most 210 times volume plus 219.

- `Machine/ScalingSplitRewind.lean`: Literal fixed-coefficient buffer rewinds after splitting. Each buffer physically returns to its original head using its preserved piece-length descriptor, with no data changes and full clock cleanup. The combined split-and-rewind machine writes exact contiguous pieces at merge-ready heads; canonical descriptors give actual cost at most twenty-four times volume plus forty-eight times fixed piece count plus one.

- `Machine/OneHotCount.lean`: Actual fixed-modulus residue construction from an immutable binary count. Writes zero into arbitrary control cells and performs counted literal residue advances; heads and background cells survive and the mutable clock resets. Twenty fixed states, cost seven times count plus seven times descriptor width plus eighteen, or fourteen times count plus twenty-five for canonical descriptors.
- `Machine/ScalingControlInit.lean`: Initializes both scaling residue banks from arbitrary control-cell contents: modulus becomes Q modulo fixed c, current becomes zero. One real initialization transition and reusable counted advances preserve descriptor, clock, all heads and background cells. The complete cost is linear in Q and fits the positive-width payload-volume budget.

- `Machine/NegationStream.lean`: Fixed ten-tape, 218-state repeated coordinate negation on uniform fibers. Exact payload is the flattened map of fiber negation; both payload heads advance full volume, and shared scratch with its head plus every descriptor and work clock are restored. Canonical prepared descriptors and positive fiber dimensions give actual runtime at most 442 times payload volume plus twenty-three.

- `Machine/ScalingExecution.lean`: Complete literal positive-unit scaling through fixed-coefficient split, physical buffer rewinds and FIFO merge. A static placement shares actual buffers; source and descriptors survive and destination block c*y modulo Q is original block y. Tape count ten plus four times fixed coefficient and state count forty-eight times coefficient plus twenty-one are independent of Q and B. Prepared canonical descriptors and residue banks give cost at most seventy-five times volume plus forty-eight times coefficient plus twenty-five.
- `Machine/ScalingBuffersReset.lean`: Literal fixed-family scratch cleanup after scaling. Each buffer is physically rewound, erased and rewound again; initially blank intervals and original heads are restored with source and control tapes preserved. Canonical piece descriptors give cost at most thirty-eight times total volume plus seventy-two times fixed piece count.

- `Machine/ScalingScatter.lean`: Literal inverse-scaling routing from a single sequential source to finitely many piece buffers, selected by actual residue control and dispatch. Buffers acquire contiguous pieces of y mapped to input at c*y modulo Q, preserving every payload block. Both clocks reset and prepared descriptors survive; canonical descriptors and positive dimensions give at most fifty-one times volume plus twenty-three steps. Physical buffer concatenation remains separate.

- `Machine/ScalingExecutionReuse.lean`: Complete reusable positive-unit scaling with actual residue-control initialization, split, physical rewinds, merge, and temporary-buffer erasure/reset. Arbitrary initial residue cells are accepted; source, canonical immutable descriptors, complete scratch backgrounds and scratch heads are preserved. Fixed ten plus four-c tapes and ninety-eight-c plus forty-two states; actual runtime at most 127 times volume plus 120 times fixed coefficient plus fifty-two. Binary descriptors remain prepared inputs.

- `Machine/ScalingConcatenate.lean`: Literal concatenation of a fixed family of raw piece buffers into one destination. Each source starts at its segment end, is physically rewound and copied, and ends at its original end position; source contents, descriptors and clock survive. Exact output is the flattened family in index order; canonical descriptors give cost at most twenty-four times total volume plus forty-eight times fixed piece count.
- `Machine/ScalingPartitionData.lean`: Contiguous quotient pieces concatenate to the complete block list, both for natural-index and Fin-indexed physical buffer families. This pure representation bridge identifies inverse-scatter concatenation with input blocks indexed by c*y modulo Q, preserving every intra-block payload cell.

- `Machine/ScalingStream.lean`: Literal repeated positive-unit scaling on uniform fibers with real control reinitialization and shared restored scratch. Exact per-fiber payload permutation, unchanged source, advanced payload heads, preserved descriptors and fully reset inner/outer clocks. Fixed twelve plus four-c tapes and ninety-eight-c plus fifty-eight states; canonical prepared descriptors give actual bound (192 plus 120 times c) times total payload volume plus twenty-three.

- `Machine/ScalingDescriptorData.lean`: Growing binary descriptor family for exact contiguous scaling-piece lengths. Selector prefix counts identify each value and final piece length; descriptors remain canonical. A telescoping family carry potential bounds all actual increment/return transitions by four times payload volume, avoiding a binary-width charge per increment.
- `Machine/ScalingDescriptors.lean`: Literal piece-length descriptor synthesis from canonical Q/B descriptors and genuinely blank derived-descriptor/work tapes. Initializes sentinels and residue controls, dispatches B counted growing increments to the selected piece for Q iterations, and restores mutable clocks. All output descriptors are exact and canonical; actual cost at most seventy times Q*B plus fifty-one for positive B. No piece-length descriptor oracle is assumed.

- `Machine/ScalingInverseExecution.lean`: Complete reusable inverse positive-unit scaling: initializes residue banks, scatters blocks to pieces, physically rewinds/concatenates them, then erases and resets all buffers. Output block y is original input block c*y modulo Q; entire source, scratch backgrounds/heads and immutable descriptors survive, all clocks reset. Fixed ten plus four-c tapes and ninety-eight-c plus forty-one states; prepared canonical descriptors give actual runtime at most 127 times volume plus 120 times fixed coefficient plus fifty-one.

- `Machine/CountedSpanSeek.lean`: Whole-fiber forward/backward positioning from separate block-width and block-count descriptors. A fixed five-tape, thirty-two-state reusable loop performs every physical move and restores both clocks/descriptors without a product-length descriptor. Canonical descriptors and positive width give rewind cost at most forty-eight times fiber volume plus twenty-three.
- `Machine/CountedSpanReset.lean`: Complete intermediate-fiber cleanup from separate width/count descriptors. Physically rewinds, erases all blocks using reusable counted loops, and rewinds again; initially blank scratch contents and original head are restored, with all other cells and both descriptors preserved. Fixed five tapes and ninety-eight states, canonical cost at most 146 times fiber volume plus seventy-one.

- `Machine/ScalingInverseStream.lean`: Actual repeated inverse-unit scaling over uniform fibers with fixed control and shared restored scratch. Every fiber initializes residue cells, scatters, physically concatenates and cleans buffers; the outer loop also restores its clock. Exact inverse payload, unchanged source and advanced data heads; canonical supplied descriptors give runtime at most (191 plus 120 times fixed coefficient) times total volume plus twenty-three.

- `Machine/ScalingAffineBridge.lean`: Exact semantic link from literal positive/inverse scaling and block negation to ordered-affine target-coordinate updates. Proves signed numerator/denominator list composition and instantiates every actual Shared50 rational scale at all prime-power widths using proved unit recipes. Preserves intra-block payload orientation; contains no uncharged tape operation or new runtime claim.

- `Machine/ScalingPreparedExecution.lean`: Complete literal one-fiber positive-unit scaling with piece descriptors generated from blank work tapes. Static placement shares the generated descriptors and Q/B controls with the reusable scaling machine, initializes remaining sentinels physically, and preserves source plus restored scratch buffers. Only canonical Q/B descriptors are supplied; generated descriptors and explicit work-marker states remain in the final bank. Fixed eleven plus four-c tapes and 117-c plus eighty-five states; actual runtime at most 197 times volume plus 120 times fixed coefficient plus 106.

- `Machine/ScalingPreparedStream.lean`: Once-only piece-descriptor synthesis from blank work followed by actual repeated positive-unit scaling. Complete initial/final banks retain generated descriptors and explicit spare/sentinel state while source and restored temporary buffers survive. Only canonical Q/B/family-count descriptors are supplied. Fixed thirteen plus four-c tapes and 117-c plus 103 states; cost is (192+120*c)*volume+70*Q*B+79, or (262+120*c)*volume+79 for a nonempty family.

- `Machine/SignedScalingExecution.lean`: Unsigned rational scaling core, despite the broader module name: literal positive numerator scaling, physical shared-intermediate rewind, denominator inverse scaling, and complete intermediate erase/reset. Exact numerator/denominator payload semantics with source, coefficient scratch and shared intermediate restored. Fixed twenty-five plus four times the sum of coefficients tapes; cost448*volume+120*(numerator+denominator)+200. Canonical per-coefficient descriptors remain prepared, and optional sign negation is not part of unsignedProgram.

- `Machine/SignedScalingSign.lean`: Complete literal signed rational scaling with a compile-time sign choice. Positive coefficients use the unsigned numerator/denominator core; negative coefficients additionally perform real intermediate rewind, block-preserving coordinate negation and full scratch cleanup. Exact signedBlocks payload and all source/scratch/control guarantees proved. Bound is448*volume+120*(a+d)+200 for positive and852*volume+120*(a+d)+516 for negative. Canonical coefficient descriptors remain prepared; canonical tail length/count descriptors are required only in the negative branch.
- `Machine/BinaryOneInit.lean`: Literal two-transition construction of a constant-one binary descriptor from a genuinely blank tape. Writes its sentinel and one digit, leaves the head on that digit and truly halts; exact value and canonicality proved. Supports the Q-minus-one descriptor bootstrap needed by negation.

- `Machine/BinarySubReuse.lean`: Literal immutable-input binary subtraction with unequal operand widths. Reads blank operand cells as zero, writes a sentinel and padded exact Q-a output from blank work, and physically resets all three heads. Fixed three tapes and thirteen states; cost four times maximum input width plus fourteen. Output width is exactly that maximum; canonicality is deliberately not asserted.
- `Machine/TranslationProduct.lean`: Literal product-length descriptor synthesis via nested counted growing increments, with input counts on immutable tapes and a fixed selected output slot. A telescoping carry proof pays total work linearly in N*B. Output is canonical when grown from empty even if the supplied N count has padding; no input-size-dependent controller or free arithmetic is used.
- `Machine/TranslationDescriptors.lean`: Complete literal shift-length synthesis from canonical Q,a,B descriptors with a≤Q and positive B. Initializes markers, physically subtracts Q-a, then constructs canonical (Q-a)*B, a*B and Q*B descriptors by actual nested loops, preserving all inputs. Fixed ten tapes and 120 states; bound163*Q*B+92. Generated metadata is explicit at the endpoint; reuse cleanup remains separate.

- `Machine/ActualAffineScaling.lean`: Instantiates the fixed signed-scaling machine for every actual Shared50 scalar coefficient. The program depends on the rational coefficient, never on radix exponent or payload width; the chosen-prime unit recipe discharges numerator/denominator legality. Exact symbol transport matches OrderedAffine target scaling at every prime-power width, with bound (1368+120*(absolute numerator+denominator))*payload volume. Canonical descriptor and blank scratch hypotheses remain explicit.

- `Machine/TranslationDescriptorsReuse.lean`: Reusable shift-length synthesis and literal metadata cleanup. From marked empty output counters, subtraction and three products create canonical split lengths while preserving Q,a,B; fixed118-state execution costs163*Q*B+90. A fixed19-state cleanup erases all three generated counters and the padded subtraction word, resets every metadata head, and physically removes the scratch sentinel, restoring the exact next-iteration bank. Cleanup costs at most8*Q*B+30 under the supplied canonical dimension assumptions.

- `Machine/TranslationPreparedExecution.lean`: Complete literal single-fiber translation from canonical Q,a,B descriptors, with a≤Q and positive dimensions. Starts derived-work tapes blank, constructs all split lengths, and physically rotates the payload through fixed shared placement. Source is preserved, both payload heads advance Q*B, and output block y+a modulo Q retains the exact source block y, including a=0 and a=Q. Fixed twelve tapes and200states; bound199*Q*B+212. Derived metadata is retained explicitly; iteration cleanup is separate.

- `Machine/NegationDescriptors.lean`: Literal canonical tail metadata construction from supplied Q/B descriptors only. Writes its own constant one on blank tape, synthesizes (Q-1)*B and the padded difference, and uses counted multiplication by one to produce a canonical Q-1 descriptor. Preserves Q/B and leaves explicit generated metadata/control banks. Fixed eleven tapes and160states; bound216*Q*B+121 for positive Q/B.

- `Machine/FamilyPlacement.lean`: Static pairing and framing of independent tape-bank placements, with exact active/extra bank laws and charged sequential execution. Placement wires finite transition tables without assuming physical transfers.

- `Machine/SignedScalingPrepared.lean`: Constructs both numerator and denominator piece-descriptor families from canonical Q/B before executing signed rational scaling. Exact signedBlocks output and full-bank contracts; bound (1612+120*(a+d))*Q*B. Fixed 40+4*(a+d) tapes. Negative-tail descriptors and the fixed split-clock sentinel remain explicit input requirements; generated coefficient metadata is retained. Public allPrepareProgram/allPrepare_hoare expose the once-only coefficient setup independently of execution.

- `Machine/TranslationExecutionReuse.lean`: Literal split-length synthesis, rotation and complete derived-metadata cleanup in one reusable twelve-tape machine. Exact modular forward shift, immutable source and Q/a/B, and both payload heads advanced Q*B. Recurring 217-state bound 207*Q*B+241; initial 219-state program starts writable metadata blank and costs 207*Q*B+243. Changing the supplied offset between calls still requires physical preparation.

- `Machine/TranslationStream.lean`: Repeated common-offset translation with literal descriptor recomputation and cleanup on each fiber. One fixed fourteen-tape, 235-state machine initializes all writable metadata from blank, preserves the source and supplied canonical Q/a/B/n, and proves the exact full final bank, including zero fibers. Runtime at most 461 times physical payload volume plus 25 for positive Q/B. Varying-offset preparation and prefix scheduling remain separate.

- `Machine/TranslationPreparedFamily.lean`: Varying-offset translation composed with one supplied fixed physical preparation program and an actual counted loop. Exact full-bank contracts preserve payloads during preparation and preserve arbitrary preparation workspace during translation. Costs the sum of actual preparation bounds plus 462 times payload volume plus 23; fixed 14+s tapes and m+233 states. Explicitly conditional on preparation Hoare contracts, with recurring marked initial workspaces. Concrete offset arithmetic and spectator scheduling remain to be instantiated.

- `Machine/SignedScalingDimensions.lean`: Complete signed rational scaling from canonical Q/B numeric inputs, synthesizing both coefficient-piece families and negative-tail descriptors by literal machines. Exact signedBlocks destination, full-bank endpoint, restored negation scratch and explicit retained metadata. Bound (1950+120*(a+d))*Q*B; fixed 49+4*(a+d) tapes. Scratch blankness and inherited fixed sentinel layouts remain explicit; it does not claim a blank-workspace bootstrap or full stream scheduler. Public bootstrapProgram/bootstrap_hoare expose charged negative-tail setup independently of execution.

- `Machine/RadixToBinaryData.lean`: Pure radix countdown and canonical binary output semantics with borrow/carry amortization. Zero-digit potential bounds total modeled conversion work by 10*value+2*width+2, hence 12*q^width+2 for q at least two; binary output has exactly the source value. This is the data/cost lemma, not yet the literal conversion-machine correctness theorem.

- `Machine/ActualAffineScalingDimensions.lean`: Specializes dimension-based signed scaling to every rational coefficient occurring in the actual Shared50 schedules. Membership proves coefficient positivity/unit legality at every prime-power width. One fixed program per coefficient, exact full-bank and ordered-affine output contracts, restored negation scratch, and bound (1950+120*(abs numerator+denominator))*q^b*B. No derived numeric descriptors supplied; inherited fixed sentinels and scratch layouts remain explicit. This proves one fiber, not the full network scheduler.

- `Machine/BinaryReplace.lean`: Seven-state two-tape binary descriptor replacement: erases the old word, copies a physically supplied replacement and restores both heads, preserving the source exactly. Full-bank bound 2*oldWidth+2*newWidth+8 includes removal of stale longer suffixes.

- `Machine/TranslationOffsetReplace.lean`: Places literal descriptor replacement on the translation offset tape and a physical scheduler-output tape, preserving arbitrary additional workspace. Composes an actual scheduler contract with replacement and varying-offset counted translation; charges the sum of scheduler runtimes and replacement scans plus 462*volume+23. The concrete scheduler and its complete tape/time contract remain required.

- `Machine/RadixToBinary.lean`: Literal radix-to-canonical-binary converter for fixed q at least two, using three tapes, eighteen states and a q+4-symbol alphabet. Physically initializes markers, copies and rewinds source, runs amortized radix countdown with binary growth, erases work and removes the temporary source marker. Exact full-bank output, original source/head preserved, scratch blank/head restored. Bound 10*value+6*width+14, hence 16*q^width+14 and 30 times nonempty fiber volume. Handles empty words, zero and leading radix zeroes; alphabet-lifted connection to translation is separate.

- `Machine/SignedScalingStream.lean`: Actual counted iteration of the signed rational scaling machine across consecutive equal-volume fibers. Exact boundary invariant tracks advanced source/destination heads, updated physical residue cells, preserved descriptor banks and restored shared scratch. Bound (1381+120*(a+d))*totalVolume+23; fixed 40+4*(a+d) tapes. Coefficient and negative-tail descriptors are prepared inputs, with explicit marked controls; once-only dimension-based setup composition is separate.

- `Machine/OffsetPreparationCost.lean`: Every fixed polynomial in radix width is little-o of q^width for q at least two. A proved polynomial preparation bound therefore gives O(q^width), and O(q^width*B) for any varying positive suffix length B. Analytic absorption only; physical preparation correctness and its polynomial bound remain premises.

- `Machine/SignedScalingDimensionsStream.lean`: One-time literal tail/coefficient descriptor synthesis followed by counted signed scaling across all fibers. Canonical Q/B/n numeric inputs only, exact full-bank endpoints with metadata and synthesis spares retained. Cost (1381+120*(a+d))*volume+356*Q*B+249, or (1737+120*(a+d))*volume+249 for nonempty families. Explicit inherited/outer sentinels and scratch requirements remain; fixed 51+4*(a+d) tapes.

- `Machine/ActualAffineScalingStream.lean`: Specializes dimension-based streams to each actual Shared50 scalar, proving exact output symbols at every concrete fiber offset and ordered-affine action for explicitly represented address fibers. Program depends only on coefficient; one-time setup charged, full-bank endpoint proved, nonempty linear constant 1737+120*(abs numerator+denominator). Arbitrary whole-field layout identification and full network scheduling remain separate.

- `Machine/MarkedWordCleanup.lean`: Literal marker installation, nonblank-word erasure, rewind and marker removal over arbitrary finite alphabets. One tape, six states; exact fully blank/head-zero endpoint in 2*width+6. Requires a nonblank word at cell one on otherwise blank tape.

- `Machine/BinaryDescriptorReset.lean`: Physically clears a binary descriptor including its sentinel and restores a genuinely blank output tape for reuse. Exact endpoint and charged scan bound; supports the recurring rational-to-binary pipeline.

- `Machine/RadixRationalBinary.lean`: Fixed-rational radix arithmetic followed by actual canonical binary conversion and complete radix scratch cleanup. Four tapes over q+4 symbols; marked source preserved with head one, both scratch tapes blank with heads zero. Bound 10*resultValue+10*width+27, at most47 times positive fiber volume. Modular interpretation assumes denominator less than prime q.

- `Machine/RadixRationalBinaryReuse.lean`: Recurring rational-to-binary computation erases the previous binary descriptor before recomputing. Exact marked-source preservation and blank scratch; bound 2*oldWidth+10*resultValue+10*width+32, at most54 times fiber volume for a canonical prior offset below the modulus.

- `Machine/RationalOffsetPrepare.lean`: Concrete five-tape recurring fixed-rational scalar offset computation, conversion, scratch cleanup and physical destination descriptor replacement. Both output copies are canonical and equal; marked radix source is preserved. At most67 times positive fiber volume for canonical prior descriptors below the modulus. Rational semantics require denominator below prime q; prefix scheduling and fixed linear combinations remain separate.

- `Machine/RadixCounterData.lean`: Fixed-width radix increment with exact modular value, increasing enumeration and wraparound to zero. Maximal-digit potential proves cycle cost at most6*n+2*width and at most8*q^width for a complete traversal.

- `Machine/RadixCounter.lean`: Literal three-state radix incrementer restores the digit head after carries and overflow. Four-state cyclic controller exposes exact finite-prefix runs with arbitrary payload frames preserved; complete traversal enumerates all radix values and returns the exact bank in at most8*q^width steps. The cyclic controller does not halt; counter initialization and mixed-field scheduling remain separate.

- `Machine/RationalTranslationExecution.lean`: Concrete sixteen-tape rational-controlled single-fiber translation: physical rational arithmetic, binary conversion, descriptor replacement, rotation and cleanup share the actual offset tape. Exact recurring full bank, source preserved, both payload heads advanced, marked radix control untouched. Cost274*Q*B+242, hence516*Q*B for positive B. Only active binary/payload tapes are alphabet-lifted; foreign radix cells are preserved as frames. Rational interpretation requires denominator below prime radix; multi-control combinations and prefix scheduling remain separate.

- `Machine/CountedLoopAlphabet.lean`: Binary-counted iteration of an arbitrary-alphabet body, with exact physical countdown/head-reset semantics and actual body transitions preserved. Core exact-bank cost is sum of body bounds plus6*n+2*countWidth+2; binary cleanup is supplied by the reusable wrapper.

- `Machine/CountedLoopReuseAlphabet.lean`: Reusable counted loop over arbitrary body alphabets, encoding only its two binary control tapes and framing all body symbols literally. Exact whole-bank endpoints, immutable descriptor and restored clock; sum of body costs plus6*n+7*countWidth+16 includes preparation and cleanup. Adds two tapes and sixteen states; uses the exposed CountedLoopReuse.prepare_exact contract.

- `Machine/PrefixCounterData.lean`: Multi-field radix carry semantics, exact flattened-prefix modular enumeration, width preservation and wraparound. Sum of maximal-digit potentials gives cost at most(4*c+2)*n+2*sum(widths), avoiding a spectator-width multiplier on each iteration.

- `Machine/PrefixCounter.lean`: Concrete fixed-field-count carry scheduler over separate radix tapes with physical head restoration. 3*c+1-state incrementer and 3*c+2-state cyclic controller; exact joint address enumeration and preserved arbitrary frames. Full finite traversal restores every field and payload bank within(4*c+4)*q^sum(widths). Fields have radix-power sizes q^b_i with arbitrary widths, including long spectators; arbitrary non-power ranges and initialization are not covered. Cyclic finite-prefix execution does not assert halting.

- `Machine/RationalTranslationStream.lean`: Concrete varying-offset family for one cyclic radix control: rational offset computation, translation, physical control increment and arbitrary-alphabet counted iteration. Exact recurring full-bank endpoints, cyclic control semantics and output length; bound534*physicalVolume+23 on eighteen tapes. Starts with explicit marked metadata, canonical Q/B/n and prior offset, and a marked radix control word. No derived descriptors or per-fiber preparation oracle; mixed-prefix scheduling and full field-layout identification remain separate.

- `Machine/FamilyPlacementAlphabet.lean`: Alphabet-polymorphic pairing, framing and charged sequential composition of tape banks. Uses static placement equivalences while preserving every symbol of arbitrary-alphabet frames; no physical transfer is assumed.

- `Machine/RadixAddReusable.lean`: Literal equal-width radix addition from blank-backed operands and blank output, all heads at zero. Writes/removes markers, preserves both operands and restores every head; three tapes/six states, cost2*width+5. Modular sum semantics and width preservation proved. Eighteen-state consume variant erases both temporary operands, leaving only the sum, in6*width+19. Supports reusable arithmetic for multi-control offsets.

- `Machine/RationalTranslationAffineBridge.lean`: Exact physical symbol transport for the concrete cyclic rational-controlled translation stream. Connects destination offsets to OrderedAffine.shift on explicitly represented address fibers; realizes_hoare combines exact bank and transported-symbol claims with the linear runtime. Actual Shared50 coefficients discharge the denominator bound. Requires the represented control coordinates to match the physical cyclic counter; arbitrary multidimensional layout construction remains separate.

- `Machine/RadixZeroFill.lean`: Physical zero-radix-field construction from a supplied binary width descriptor. Writes markers and placeholders by actual counted iteration, recodes backward to radix zero, and returns the field head. Three tapes, twenty-three states; bound8*n+7*descriptorWidth+21, or15*n+28 for canonical widths. Field/work tapes start blank; dimension descriptor is preserved and control scratch returns to its explicit reusable marked state.

- `Machine/PrefixCounterInit.lean`: Fixed-field-count physical initialization from canonical binary width descriptors, with all output and clock tapes initially blank. Sequential radix zero-fill constructs every field; exact full-bank endpoint and injective field projection identify the zero PrefixCounter bank. Cost15*sum(widths)+29*fieldCount; 3*fieldCount+1 tapes and23*fieldCount+1 states, including the empty family via an untouched spare. Width descriptors and explicit reusable clocks are retained; whole translation-bank assembly remains separate.

- `Machine/RadixLinearCombination.lean`: Fixed expression/list compiler executes rational leaves and modular addition nodes, physically erasing temporary operands and restoring source/scratch heads. Exact radix output equals the rational modular sum when denominators are below prime q. Coefficient-list bound(34*termCount+7)*q^b with3*termCount+2 tapes. Every leaf, including the zero seed, has a supplied marked source copy; repeated logical controls are not copied or refreshed for free. Binary endpoint and scheduler-source linkage remain separate.

- `Machine/RadixLinearCombinationBinary.lean`: Fixed rational-expression arithmetic followed by one canonical binary conversion and physical erasure of the final radix result. Exact output descriptor/head, both converter work tapes blank/head zero, and original leaf-source workspace preserved. Coefficient-list bound(34*termCount+47)*q^b with3*termCount+4 tapes; binary value is the exact modular rational sum for denominators below prime q. Supplied per-leaf copies remain explicit; source duplication/refresh and recurring binary-output replacement are separate.

- `Machine/RationalPrefixTranslationExecution.lean`: Concrete rational-controlled fiber translation followed by physical multi-field prefix increment. Selected field zero supplies the offset; a fixed nonempty duplicate-free carry order may place it anywhere, with independent spectator widths. Exact full-bank endpoint preserves spectator tapes during translation and charges actual carry/rewind transitions:516*Q*B+1+prefixStepCost. Fixed16+c tapes for c+1 prefix fields. Prepared marked inputs and equal target/selected-control radix width explicit; repeated-family and layout assembly separate.

- `Machine/RationalPrefixTranslationStream.lean`: Actual counted translation across mixed-width prefix fields, with selected field zero supplying rational offsets and a fixed nonempty duplicate-free carry order. Exact evolving bank and modular offset semantics; cost(530+4*orderLength)*volume+2*initialTotalWidth+23. Full finRange traversal restores all prefix fields and costs(536+4*c)*volume+23 on18+c tapes for c+1 fields. Spectator widths incur no per-fiber full scan. Recurring marked initial bank remains explicit; initialization and whole-array layout assembly are separate.

- `Machine/PrefixAddressData.lean`: Whole-prefix radix address semantics: flattening fastest-first field words equals reversed lexicographic field order; full-order width sum and selected-field extraction proved. Zero-start PrefixCounter enumeration yields the actual prefix rank and selected control via division/modulo, allowing arbitrary spectator widths without a supplied address-family assumption.

- `Machine/FiberLayoutData.lean`: Constructs prefix/target/suffix fibers directly from a flat Fin(P*(Q*B)) array and proves flattening returns exactly its original List.ofFn. Per-prefix rotations transport each target entry while preserving every suffix symbol and total volume. scheduled_entry connects selected-counter extraction to these concrete flat-array addresses. Pure layout/address lemmas; physical runtime integration remains separate.

- `Machine/MarkedRadixRefresh.lean`: Physical replacement of a stale marked radix word from a shared source tape. Erases the old copy, copies actual source digits and restores both heads to one, preserving the source cell-for-cell and removing stale longer suffixes. Two tapes, seven states; exact whole-bank bound2*oldWidth+2*sourceWidth+8. Wiring this primitive across all expression leaves and scheduler controls is separate.

- `Machine/SharedPlacementAlphabet.lean`: Alphabet-polymorphic placement sharing one physical tape between an active program and a retained bank. Exact complete-tape/head replacement and framed Hoare contracts use static finite wiring, without a physical copy assumption.

- `Machine/RadixLinearCombinationRefresh.lean`: Concrete refresh of every expression leaf from one shared physical control bank. Fin-bounded references determine fixed tape placements; recursive erase/copy programs preserve the shared bank and synchronize all stale leaf copies, including repeated references. Exact complete-bank theorem and runtime+1 at most leafCount*(4*width+9) when source/stale widths are bounded. Actual binary arithmetic composition and recurring output reset remain separate.

- `Machine/FlatControlledShift.lean`: Complete physical controlled shift on a flat Fin(P*(Q*B)) array, with fibers constructed from the input itself. Actual prefix enumeration supplies the selected rational control; exact source List.ofFn and every destination symbol proved, preserving prefix and suffix coordinates. Full-bank Hoare theorem costs(536+4*c)*volume+23. Requires canonical B/Q/P descriptors and a prepared marked zero prefix/work bank; no assumed address family or offset oracle. Target and selected control share radix width, spectator widths arbitrary, denominator below prime radix. Physical initialization handoff remains separate.

- `Machine/RadixLinearCombinationShared.lean`: One physical program refreshes stale expression leaves from a shared bounded control bank, computes the rational expression, converts to canonical binary and restores arithmetic/converter scratch. Exact shared-control preservation and output descriptor; finite-bank wrapper needs no unbounded extra source tapes. Cost(13*leafCount+expressionConstant+40)*q^b for common new width b and stale widths at most b. Leaf sentinels/head-one remain prepared inputs and binary output starts blank; first-use bootstrap and recurring output reset separate.

- `Machine/RadixLinearCombinationBootstrap.lean`: First-use canonical offset computation from genuinely blank expression/converter scratch. Actual finite marker installation precedes shared-source refresh, arithmetic and binary conversion; shared marked controls are preserved and final state is the exact shared-computation output. Bound(15*leafCount+expressionConstant+40)*q^b, with a finite control-bank wrapper. Source control words remain supplied; recurring binary-output reset and translation-bank composition are separate.

- `Machine/PrefixCounterInitPlacement.lean`: Explicit static permutation hands physically initialized prefix-field tapes to a consumer while retaining all width descriptors, clocks and spare tapes as frames. initialize_then composes real initialization with a proved consumer execution and charges their join; no field copying is assumed.

- `Machine/RationalPrefixTranslationInit.lean`: Composes actual blank-prefix initialization with FlatControlledShift on the same physical tapes. Exact active-stream output and transported flat-array symbols; bound(551+4*c)*volume+29*(c+1)+24 includes prefix setup. Canonical width/B/Q/P descriptors remain supplied; prefix outputs/clocks start blank. Fixed marked translation metadata is still explicit input, so this is not yet an entirely blank-workspace bootstrap.

- `Machine/FlatAffineScaling.lean`: Concrete flat-array theorem for every actual Shared50 rational scalar. Identifies the physical source with the supplied array and proves every output symbol keeps its prefix/suffix while the target is multiplied modulo Q. Exact full-bank execution includes descriptor synthesis and bound (1737+120*(abs numerator+denominator))*volume+249. Canonical dimension descriptors and inherited sentinel/scratch conditions remain explicit; composition of successive operations is separate.

- `Machine/MarkedBinaryCleanup.lean`: Four-state physical erasure of an encoded binary descriptor and its sentinel, returning a wholly blank tape/head zero without a supplied length descriptor; exact runtime bound 2*bits.length+4.

- `Machine/RadixLinearCombinationReuse.lean`: Recurring shared-bank expression evaluation physically erases the old binary output and refreshes all stale leaf copies. Exact finite-control-bank contract and bound (13*leaves+expressionConstant+47)*q^b. Physical advancement of the shared controls remains the caller scheduler responsibility.

- `Machine/MultiControlTranslationExecution.lean`: Actual shared-source expression evaluation composes with fiber translation using the same physical binary offset tape through static placement. Exact recurring full-bank state, preserved controls, payload/head contracts and modular expression semantics; bound (13*leaves+expressionConstant+496)*Q*B. No fresh copies or supplied computed offset; canonical dimensions, initial metadata and control advancement remain explicit, and prefix-stream scheduling is separate.

- `Machine/RationalPrefixTranslationBootstrap.lean`: Full flat-array controlled shift from blank writable prefix and translation metadata tapes. One actual transition installs eight markers and moves the spare head, then physical prefix initialization and stream execution run. Exact complete output bank inherits the transported-symbol theorem; bound (551+4*c)*volume+29*(c+1)+26. Only canonical width/B/Q/P descriptors and payload remain supplied; dimension construction and successive-operation composition are separate.

- `Machine/CountedVolumeLoop.lean`: Three actual nested counted loops over separate canonical B/Q/P descriptors; restores all clocks and preserves arbitrary body symbols. Exact per-cell iteration contract and explicit runtime; one-step body costs at most 109*volume. No total-volume descriptor is assumed.

- `Machine/FlatArrayNormalize.lean`: Eight-tape, 150-state three-pass payload transfer: physically rewind both heads, copy old output into common input while erasing it, then rewind both again. Exact full-bank contract restores output scratch and both origins, reuses B/Q/P descriptors, and charges 327*volume+2. Placement into concrete operation banks is separate.

- `Machine/FlatControlledShiftNormalize.lean`: Composes full concrete controlled shift with physical payload normalization on the same tape bank. Actual B/Q/P descriptors and clocks are reused by static placement; exact final offset/prefix metadata is retained, both payload heads return to origin, output scratch is restored and shifted symbols are on common input tape10. Bound (863+4*c)*volume+26 includes every pass. Prepared shift input remains explicit; blank-workspace wrapper and full schedule assembly are separate.

- `Machine/FlatControlledShiftReady.lean`: Composes physical blank-workspace marker setup, prefix initialization, concrete controlled shift and payload normalization. Exact full bank retains initializer and operation metadata; transformed symbols return to common input with output scratch/head origins restored. Bound (878+4*c)*volume+29*(c+1)+29 includes every stage. Canonical width/B/Q/P descriptors remain supplied; full fixed affine schedule and dimension construction remain separate.

- `Machine/MultiControlTranslationBootstrap.lean`: First-use physical shared-source expression evaluation and translation starts all writable arithmetic/translation scratch blank at head zero. Explicit spare-head setup, leaf marking, canonical offset computation, translation metadata initialization and rotation are charged; the exact output matches the recurring MultiControlTranslationExecution bank. Bound (15*leaves+expressionConstant+493)*Q*B. Only physical marked radix controls, canonical B/Q descriptors and payload remain supplied; full prefix scheduling is separate.

- `Machine/FlatControlledShiftArray.lean`: Canonical finite-array representation of the physically normalized controlled-shift output. Proves the common input tape is exactly the new List.ofFn array on the original background, eliminating the nested old-word overlay. Supports subsequent operations with a different prefix/target/suffix split without an uncharged tape conversion.

- `Machine/StaticMarkerInit.lean`: Two-state machine installs a fixed coefficient-dependent marker/head template in one actual transition. Exact raw-to-target full-bank proof, origin-zero input heads, off-origin data preservation and append lemmas. The template is part of fixed finite control, not input dimensions.

- `Machine/FlatAffineScalingBootstrap.lean`: Actual rational scaling from blank generated storage, residue banks, intermediate payloads and sign scratch, with all heads initially zero. Physically installs coefficient-dependent sentinels and runs descriptor/residue synthesis and whole-array scaling; exact source and scaled destination symbols, bound nonemptyConstant*volume+251. Only canonical B/Q/P words in fixed input slots and payload remain supplied; dimension-word construction and common-input normalization are separate.

- `Machine/MultiControlPrefixTranslationExecution.lean`: Physically evaluates shared-control expression, translates a fiber and advances the actual common prefix fields; old leaf copies and binary result remain explicitly stale until next evaluation. Exact full-bank postcondition and per-fiber linear work plus actual carry cost. No per-fiber refreshed-bank premise.

- `Machine/MultiControlPrefixTranslationStream.lean`: Real counted stream of multi-control translations with physical carry scheduling and exact current/stale-field invariant. Complete equal-width c-field cycle costs (13*leaves+expressionConstant+512+4*c)*volume+23 and restores shared controls; exact output tape and modular-expression offsets. Initial recurring metadata/old arithmetic state and canonical B/Q/count descriptors are explicit; blank bootstrap is separate.

- `Machine/InjectivePlacement.lean`: Extends fixed injective physical tape slots to a complete static placement, with exact active-slot/bank lemmas. Existing placement Hoare rules preserve every complementary tape and head literally; no runtime relabeling or tape movement is introduced.

- `Machine/FlatAffineScalingNormalize.lean`: Attaches physical three-pass payload normalization to the actual scaling output using existing B/Q/P descriptors and clocks. Exact original source/destination slots, retained complementary metadata, restored scratch and heads, and scaled symbols on common input. Full bound (2064+120*(abs numerator+denominator))*volume+252. Prepared scaling input remains explicit; blank-workspace wrapper and schedule composition separate.

- `Machine/MultiControlPrefixTranslationBootstrap.lean`: Complete equal-width multi-control prefix stream from wholly blank writable arithmetic, translation and outer-clock workspace. Physically creates metadata markers/spare position and evaluates the shared expression before running the counter-driven stream; exact full-bank output and bound (28*leaves+2*expressionConstant+552+4*c)*volume+26. Actual marked initial radix controls and canonical B/Q/count descriptors remain supplied; field initialization is separate.

- `Machine/FlatAffineScalingReady.lean`: Complete actual rational scaling from blank generated workspace through physical normalization. Exact retained bank and transported symbols on original source; destination scratch and both heads restored. Bound (2064+120*(abs numerator+denominator))*volume+254 includes marker creation, descriptor synthesis, scaling and every normalization pass. Canonical dimension words and initially blank destination interval remain explicit inputs.

- `Machine/FlatAffineScalingArray.lean`: Canonical finite array produced by initialized normalized scaling. Exact coordinate multiplication, List.ofFn representation and original-source tape equality over the original background; eliminates the old input overlay so later target-coordinate splits use the same physical word.

- `Machine/FlatCoordinateLayout.lean`: One common row-major coordinate/index bijection for all targets, including modulus one and arbitrary trailing record width. Exact target-specific volume split, identical serialized source word, physical earlier-control extraction and scale/shift destination equations for OrderedAffine.execute. Concrete fiber transport bridges eliminate abstract address-family assumptions; actual machine specialization and shared-tape schedule composition remain separate.

- `Machine/MultiControlPrefixTranslationInit.lean`: Physically generates every shared radix control field from blank storage using canonical width descriptors, then runs blank-workspace initialization and the complete multi-control prefix stream. Exact active output and preserved initializer frame; no supplied marked controls, stale copies, results or work sentinels. All initialization is absorbed into (28*leaves+2*expressionConstant+594+33*c)*volume. Canonical width/B/Q/count descriptors remain supplied; concrete flat-array adapter is separate.

- `Machine/FlatMultiControlTranslation.lean`: Complete physical flat-array translation by a fixed rational expression over actual prefix coordinates. Proves generated counter field j is the jth radix slice of the physical prefix, computed offset equals modular expression evaluation, source fibers serialize exactly to the input array, and every suffix symbol reaches its correct output address. Full initialized machine costs (28*leaves+2*expressionConstant+594+33*c)*volume. Only canonical dimension descriptors and flat payload remain supplied; normalized output/schedule assembly separate.

- `Machine/FlatCoordinateScaling.lean`: Instantiates the common-coordinate layout with actual initialized normalized network scaling. Exact returned canonical array transports every coordinate/record according to OrderedAffine.execute scale; original source tape equals that array. Actual ready-machine Hoare contract includes all setup/movement and bound (2064+120*(abs numerator+denominator))*commonVolume+254; canonical dimension descriptors remain supplied.

- `Machine/FlatCoordinateShift.lean`: Actual initialized normalized controlled shift on the common row-major coordinate layout. Constructs the counter order so the selected control is after exactly the less-significant prefix fields; proves the physical offset equation and exact OrderedAffine shift transport of every symbol. Ready-machine Hoare theorem returns the canonical common-volume array on its original source, with all initialization/normalization costs; canonical dimension words remain supplied.

- `Machine/SharedPayload.lean`: Static injection shares a stage source/destination with two permanent payload tapes, retaining all private metadata and leaving private payload slots blank/head-zero. Exact active/frame identities and placed-stage Hoare rule; no runtime copies, head resets or relabeling operations.

- `Machine/SharedPayloadPair.lean`: Literal composition of two stages on the same permanent payload pair and separate stripped metadata banks. Proved exact whole-bank handoff when first output pair equals second input pair; costs both proved runtimes plus one sequence step. Concrete scaling/shift compatibility and full fixed schedule instantiation are separate.

- `Machine/FlatControlledShiftPayload.lean`: Exact payload-pair interface for the initialized normalized controlled-shift machine. Proves distinct actual source/destination slots and identifies input as the encoded original array and output as the encoded canonical shifted array on the same heads, with destination scratch restored. Supplies concrete tape compatibility for shared-payload stage assembly.

- `Machine/RadixPowerWord.lean`: Fixed 29-state physical machine reads binary b, constructs an unmarked radix word of b zeros followed by one (value q^b), clears its clock and preserves the exponent tape. All high-digit writes, scans and marker removal charged; runtime 10*b+7*inputWidth+27.

- `Machine/RadixPowerDescriptor.lean`: Fixed four-tape, 53-state machine computes canonical binary q^b from one canonical binary b descriptor, for fixed q>=2 including b=0. Physical radix construction, conversion and cleanup compose with exact full-bank output, preserved exponent and blank scratch. Bound99*q^b; no precomputed power or arithmetic oracle. Assembly of all affine dimension descriptors remains separate.

- `Machine/FlatAffineScalingPayload.lean`: Lifts the actual initialized normalized scaler to the common radix alphabet with the same runtime. Proves distinct physical source/output slots, exact canonical encoded input/output payload pairs with blank scratch and zero heads, and full concrete lifted Hoare execution. Supplies the scaling side of actual shared-payload handoff; no duplicate data or conversion work is assumed.

- `Machine/FlatControlledShiftMetadata.lean`: Proves the entire stripped initialized-shift metadata bank is independent of the payload array. Stage metadata can be supplied using a literal blank dummy array; no initial bank needs to contain or name an uncomputed prior stage result.

- `Machine/SharedPayloadFrames.lean`: Exact blank/head-zero contracts for unused private payload slots in stripped stage banks and two-stage input/output. Confirms that only the two permanent payload tapes carry data, with no hidden per-stage copies.

- `Machine/FlatScaleShiftPair.lean`: Concrete actual-network rational scale followed by controlled shift on the same two physical payload tapes. Initial second-stage metadata uses a blank dummy array; real first output supplies second input through proved canonical-word handoff. Exact full-bank endpoint, restored common heads/scratch and bound (2942+120*(abs numerator+denominator)+4*c)*volume+29*(c+1)+284. Canonical dimension descriptors remain supplied; arbitrary fixed-schedule assembly separate.

- `Machine/FlatAffineScalingMetadata.lean`: Proves the entire lifted scaling private input bank, after removing the two permanent payload slots, is independent of the finite input array. Only fixed coefficients and dimension descriptors determine this metadata; later scaling stages can be prepared before their actual input is computed.

- `Machine/SharedPayloadStage.lean`: Exact stage interface bundling an actual program, canonical shared payload pair, input-independent private metadata and proved execution cost. Intended for physical finite-list assembly; actual machine constructors must discharge every contract.

- `Machine/FlatCoordinateStages.lean`: Concrete common-coordinate scale and earlier-control shift Stage constructors at the actual shared prime alphabet. Instantiates all program, payload, metadata-independence and runtime contracts from initialized normalized machines; exact transform theorems prove OrderedAffine symbol transport. Canonical dimension inputs remain explicit; finite-list assembly and uniform schedule theorem separate.

- `Machine/RadixPowerMultipleWord.lean`: Fixed-many counted passes read one preserved binary width and construct its radix power word, with restored scratch and charged initialization, rewind and cleanup. The multiplier belongs to finite control.

- `Machine/RadixPowerMultipleDescriptor.lean`: Actual four-tape constructor of canonical binary q^(k*b) from binary b, with k fixed in finite control. Preserves b and restores both scratch tapes blank; bound (24*k+75)*q^(k*b), including k=0 and b=0. Supplies prefix/suffix powers for coordinate dimension synthesis.

- `Machine/SharedPayloadStageCompose.lean`: Actual finite-list compilation of heterogeneous machine stages onto one common payload pair, preserving each private metadata bank. Proves literal final bank and folded payload semantics, with sum of stage costs plus every joining transition. Concrete coordinate schedule instantiation and runtime-independent skeleton are separate.

- `Machine/SharedPayloadStageSkeleton.lean`: Erases array types, semantic contracts and supplied descriptors to retain only finite machine data. Proves finite-stage compilation depends solely on these skeletons; transports exact bank execution and metadata independence to a previously fixed program. Concrete width-independent coordinate skeletons are established separately.

- `Machine/FlatCoordinateSchedule.lean`: Fixed rational scale/earlier-control shift operation description, canonical dimension descriptors and concrete Stage instantiation. Proves exact primitive transport, costs, and equality of entire finite-machine skeleton to one selected independently of width and record size.

- `Machine/FlatCoordinateScheduleCompile.lean`: One fixed multitape program executes every supported finite rational coordinate schedule for all widths and positive record sizes. Proves exact OrderedAffine.run symbol transport, input-independent private metadata, and explicit linear-volume runtime including all joins. Canonical dimension words remain supplied; their physical synthesis/installation and recursive interchanges are separate.

- `Machine/BinaryDescriptorCopy.lean`: Actual two-tape, five-state binary descriptor copier from a preserved source to a wholly blank destination. Installs the destination sentinel, copies every bit, restores both heads to one and proves exact whole-bank output in 2*length+5 steps; alphabet-lifted contract uses standard encodedBinary tapes.

- `Machine/Shared50NonrecursiveCoordinates.lean`: Actual Shared50 nonrecursive field operations instantiate supported fixed coordinate schedules with proven coefficient occurrence and order. Negative-one scaling support is derived from an actual preFields transform. Proves exact H/D output and one dimension-independent physical machine with linear-volume cost; canonical dimensions supplied and recursive interchange excluded.

- `Machine/BinaryDescriptorCopies.lean`: Fixed-many physical replication of one binary descriptor onto genuinely blank tapes, preserving the sole source and restoring every head. Uses n+1 tapes and 5*n+1 states, no workspace; exact whole-bank contract costs n*(2*length+6), including every join, with a canonical logarithmic bound.

- `Machine/Shared50NonrecursiveSegments.lean`: Actual nonrecursive Shared50 schedule segments compile to one fixed physical machine. Every output symbol follows the exact AffineFieldProgram.run on the embedded H/D coordinates; complete intermediate arrays need not be supplied. Explicit linear-volume bound includes all stage joins; canonical dimension descriptors remain supplied and recursive calls excluded.

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
- `Compact/RepairPipeline.lean`: the assembled exceptional-address repair at
  the list level. On the rank-ordered stream of the actual program's output,
  flag the exceptional addresses, extract those records with their
  destination ranks `e (T (S⁻¹ q))`, radix sort them by destination with the
  stable passes of `RadixSort`, and reinsert them into the flagged holes with
  `Reinsert.fill`; the result is the stream of the ideal map everywhere, for
  any `S`, `T`, exceptional set with the agreement and preservation
  properties, and in particular for both packed programs. The extracted
  records are exactly the exceptional addresses, so their count is the
  exceptional fraction times the volume, the radix passes traverse
  `k · |ℬ| · w` cells, and the written cost expression is at most three
  volumes under the density bound. Tape execution of the scan is not here.
- `Compact/TapeRepairStage.lean`: the pipeline's extracted records, keyed by
  their destination ranks in binary, are the keyed records of the fixed
  eleven-tape stage machine `Machine/RepairStage`; on them and the flagged
  actual output stream it halts with the ideal stream on its output tape,
  within `74k + 4` extracted volumes, one full-stream volume, and `k + 7`,
  the extracted volume being at most `|ℬ|·(k + 2 + w)`. The flagging scan and
  the destination-rank arithmetic that produce the keyed records remain open.
- `Compact/TapeRepair.lean`: the complete repair machine `Machine/RepairScan`
  on the unflagged actual output stream, with the scan's flags and keys being
  membership and the destination rank `e (T (S⁻¹ q))` of the rank's address,
  halts with the ideal stream on the output slot, within the key cost plus
  ten per record, three stream volumes, `74k + 5` extracted volumes,
  `2k + 3` per exceptional address, and `k + 14`. The key routine's tape
  arithmetic is the parameter that remains open.
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
  and a uniform internal vector-factor budget. `ComplexCorrections` supplies
  the correction instructions and kernel expansion; literal tape execution is
  a separate obligation.

- `Networks/ComplexCorrections.lean`: the endpoint corrections as literal
  single-wire instructions around the lowered h=25 factor program. Each
  terminal sign character is the product of one sign flip per support
  coordinate (27 of them), so the corrected program costs the rank total plus
  28 instructions per data wire and sends every input, including dirty
  scratch, to its full forward tensor on the exchanged bank. Every vector
  factor expands into its per-column two-term kernels `aI + bX_v` with
  `a = (1+i)/2`, `b = (1-i)/2` (inverse factors swap the coefficients), giving
  the column-expanded program with `k` kernels per rank factor and `54k+2`
  corrections per address. Literal tape costs remain open.

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

- `Networks/OrderedAffine.lean`: Refines each lower-triangular matrix transform into descending target rows, with a diagonal scaling followed by individual shifts controlled only by earlier coordinates. Exact execution equals matrix multiplication; invertibility supplies diagonal units, coefficient specialization preserves the fixed operation order, and no new coefficients are introduced. Literal ordered-affine tape routines remain separate.

- `Networks/AffineFieldProgram.lean`: Compiles whole-group triangular transforms to scalar ordered-affine steps while retaining explicit cross-group primitives. Exact run semantics, legality, unchanged recursive interchange counts and specialization by arbitrary coefficient maps are proved; the compiler introduces no extra recursive calls.
- `Networks/Shared50AffineControl.lean`: The actual complete optimized interchange has fixed rational scalar-affine schedules, specialized at every width. Protected inverse factors prove every diagonal scaling is a unit; exact execution realizes every physical edge in its original order and retains exactly the improved recursive interchange budget. Literal tape runtime remains open.

- `Networks/Shared50AffineCoefficients.lean`: Every actual scalar-affine coefficient originates in protected matrix entries or cross-group signs, giving its denominator bound and exact literal arithmetic kernel. Actual scale legality at the chosen prime proves numerator coprimality; the fixed signed numerator/denominator recipe is valid at every prime-power width. No numerator-size assumption or tape-permutation runtime is introduced.

- `Networks/AffineFieldCoordinates.lean`: H-before-D coordinate embedding and exact expansion of nonrecursive field operations to ordered scalar operations, including reflected subtraction as negative-one scaling then earlier-control shift. Proves operation/segment semantics and coefficient-map commutation; recursive interchange excluded.

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
- `NLogN/ResamplingPermuted.lean`: §7, resampling with the permutations left
  in the transform. From the explicit factorization `F_s = 2^γ B F_t A` with
  `B = P_s⁻¹ D J C P_t`, moving `P_s` to the left gives the exact identity
  `P_s F_s = 2^γ B₀ P_t F_t A` with `B₀ = D J C / 2^(γ-1)` and `‖B₀‖ ≤ 1`, so
  neither coordinate permutation is executed. The retained frequency
  permutation `Q : j ↦ (-sᵢ jᵢ)ᵢ` of the `d`-dimensional even-length transform
  is a chirp identity with the weighted chirp `exp(π i Σ sᵢ jᵢ² / tᵢ)`, and
  the retained source permutation `R` by coordinatewise units satisfies
  `F R = R⁻¹ F` for any roots, so `R F [(R F u)·(R F v)] = (∏ Nᵢ) (u ∗ v)(-k)`
  in the unnormalized convention. Costs are not here.
- `NLogN/ResamplingPermutedNumeric.lean`: §7, Lemmas 7.1 and 7.2 with their
  numerical maps. Tensoring the permutation-left identity gives
  `R F_s = 2^γ ℬ₀ Q F_t 𝒜` in `d` dimensions with `R = ⊗ P_{sᵢ}`,
  `Q = ⊗ P_{tᵢ}`, `𝒜 = ⊗ Aᵢ`, `ℬ₀ = ⊗ B₀ᵢ`, both tensors contractions. The
  numerical `B̃₀ = D̃' J̃ C / 2` uses the explicit clamped `Ẽ` and no
  permutation; the clamped explicit `Ã` and `B̃₀` approximate `A` and `B₀`
  with scaled errors `(8m+7)/2` and `(24m+23)/2`, below `p²` for `m ≤ p`,
  `p ≥ 13`, and the linewise tensors have errors `d` times these. Costs are
  not here.

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
- `TimeBound.lean`: the complete time bound of §8 as a statement about cost
  functions. With precision `p = 6 lg n`, which is at least `6`, tends to
  infinity, and is at most `12 log n / log 2`, a dominant row
  `C V (log p)^k p^e` with `e < 1 - κ` and volume `V ≤ cV n` is eventually at
  most `C cV 6^(1-κ)` times the target time `n (lg n)^(1-κ)`; a setup cost
  `D p^A` and a cost `D V φ(p)` with `φ` eventually bounded are eventually
  fixed multiples of the target time as well. Finite lists of such rows sum to
  `C n (lg n)^(1-κ)` for all large `n`, and the seven table rows with
  exponents `1 - margin i` instantiate this at `κ = 83 / 10^12`, the exponent
  of `Machine.EndToEnd`. The row costs themselves, and the translation of the
  size parameters `d, K, ℓ, r` into powers of `p`, are supplied by the
  components and remain open.
- `Sizes.lean`: the input and transform sizes of §8. From `b = lg n`, with
  `2^(b-1) < n ≤ 2^b` and `b ≤ n`, the number of axes `d = ⌊b^ε⌋` satisfies
  `1 ≤ d ≤ b` and `d ≤ p^ε`, and eventually `p^ε / 12 ≤ d`; the chunk width
  `K = ⌊d^c⌋` with `c = spacing` satisfies `K ≤ p^(εc)` and eventually
  `p^(εc) / 24 ≤ K`; the transform length `T = 2^⌈log₂ (4n/b)⌉` lies in
  `[4n/b, 8n/b)`, so `24 n ≤ T p < 48 n` for every `n ≥ 1`; eventually
  `b / 2 ≤ log₂ T ≤ b`, hence `p / (12 d) ≤ ℓ ≤ p / (3 d)` for
  `ℓ = ⌈log₂ T / d⌉`, and the axis length `r = 2^ℓ` is at least
  `2^(p^(1-ε) / 12)`. These are the comparison constants `a_d = a_r = 1/12`,
  `b_d = 1`, `b_r = 1/3` of the layer and transform interfaces.
- `CostTable.lean`: the cost table of §8 with the witness margins. Each row's
  cost per unit volume, written in the size parameters, is eventually a fixed
  multiple of `p^(1 - margin i)`: prefix-slot moves `d K`, chunk exchanges
  `p K^(τ-1)`, simultaneous rounds `ℓ d^λ'`, CRT and axis layouts
  `d (1 + ℓ^τ)`, Gaussian line maps `d p^(1/2+δ) α` with
  `α = ⌈(12 d b)^(1/4)⌉`, chirps and twists `d p^δ`, and packed products
  `log (r p)`, with explicit constants. A total cost at most the volume times
  the seven rows, plus polynomial setup and bounded overheads, is therefore
  `O(n (lg n)^(1 - κ))` with `κ = 83 / 10^12`. That the components achieve
  these rows is their own obligation.
- `Assembly.lean`: the reduction of `Machine.EndToEnd` to a program with a
  cost function. A program that halts with the correct product on every pair
  of `n`-bit inputs within `total n` steps satisfies `ComputesWithin` whenever
  `total` is eventually a fixed multiple of the target time, and a `total`
  bounded by the volume times the cost table rows, polynomial setup, and
  bounded overheads is such a function. The program, its correctness, and its
  cost proofs are the remaining obligation.
- `LineCost.lean`: line counting for the tensor interface (§7, Lemma 7.2).
  One-dimensional work `C tᵢ X` on the `T / tᵢ` lines of each axis sums to
  `d C T X`, and with the Gaussian line cost `X = p^(3/2+δ) α` this is the
  volume `T p` times the cost-table row `d p^(1/2+δ) α`; with every
  `tᵢ ≥ r/2` at most `2 d T / r` lines are visited; and any fixed polynomial
  `p^c` of setup per line totals `o(T p)` under the §8 size relations, since
  `r ≥ 2^(p^(1-ε)/12)` outgrows every power of `p`.
- `ExactRecovery.lean`: precision and exact recovery (§8, the final integer
  coefficients). With computed source and opposite transforms within scaled
  error `E_s` of the exact contractions on the half ball and the pointwise
  product truncated to the grid, quarter-ball inputs keep every computed
  array in the disk and the computed opposite transform is within
  `(3 E_s + 2) 2^(-p)` of `G (F u · F v)`. Through the convolution identity
  `G (F u · F v) = (u ∗ v) / S²`, the numerator scaling `16 S` returns the
  normalised convolution of the digit vectors within `16 S (3 E_s + 2) 2^(-p)`,
  and the rounding recovery of `MainReduction` gives the exact product once
  `2^(2k+4) S² (3 E_s + 2) < 2^(p-1)`. With `E_s = 9 · 2^γ T L`, `S ≤ T < 2^k`,
  `L < k`, `γ ≤ k/4` and `p = 6k`, both margins follow from
  `896 k 2^(k/4) < 2^k`, which holds for all large `k`. Tape costs are not
  here.
- `LayoutCost.lean`: the transform layout and its cost (§6, the transform
  layout lemma). Any permutation of `n` positions is a product of at most
  `n - 1` transpositions, so the chunk reorder takes at most `Dq - 1` chunk
  exchanges, costing at most `d ℓ K^(τ-1)` for `qK ≤ ℓ`; at most `D (b+1) ≤ dK`
  slots move to the prefix; the leading, chunk, and prefix rounds number
  exactly `ℓ`; a chunk round sees `P · 2^(DK) · S` records; the nine
  descriptor codes total at most `C_desc p`; `m` truncated contraction rounds
  have error at most `m √2 2^(-p)` and keep the disk; the cost bracket
  `dK + pK^(τ-1) + ℓ d^λ' + log(rp)` is the sum of four cost-table rows,
  below the whole table; and `K + 1 ≤ ℓ` holds for all large `n`. Tape
  execution is not here.
