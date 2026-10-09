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
- `Machine/Gather.lean`: a stride gadget on three tapes, source, control and
  target, unrolled into finite control: for each digit the source head skips
  to a field, each field bit is combined with the digit's control bit by a
  fixed Boolean operation into the target digit at a chosen offset, the other
  target cells are zero, and the heads advance by one source stride, one
  target stride and one control bit. The gathered word is exact and the cost
  is `n(2(sx + st) + 7)`. `ExactFrame` gained step-right and write-zero moves
  and the generic unrolling combinator `iterate` with its chain contract.
- `Machine/PackedLine.lean`: one line of packed address arithmetic on five
  tapes, source, control, offset scratch, accumulator and target: gather the
  packed offset, rewind source, control and offset, combine accumulator and
  offset by a column transducer into the target, erase the offset and rewind
  accumulator and target. Source, control and accumulator are preserved, the
  target holds the exact transduced word, the scratch is blank again and the
  cost is linear in the widths. `ColumnTransducer` gained the modular
  subtraction instance with its integer-residue value; `ExactFrame` a rewind
  from inside a longer word; `Gather` accepts a source longer than the
  scanned strides.
- `Machine/PackedArith.lean`: the forward packed program of the
  compact-control address arithmetic on nine tapes for digit widths `q` and
  `b` with `b + 1 ≤ q`: the four packed updates of `packedEarly` in the
  radices `2^q` and `2^b` as five gather-and-transduce lines, with exact
  list-level word semantics, the input words and control preserved, the
  offset scratch blank again, intermediate and final words on their own tapes
  and every head at its origin; linear cost.
- `Machine/GuardTest.lean`: comparing a fixed number of cells of a word with
  a constant word, the order kept in a single cell updated column by column
  (the `BinaryCompare` order semantics), and a flag cell writing whether the
  order is "smaller" or "larger" onto a flag word and erasing the order cell.
- `Machine/GuardGadget.lean`: the guard test on seven tapes: for each block
  of the first word its upper bits are compared with two constants, for each
  block of the second word the block with a third, each comparison appending
  one flag bit; unrolled finite control, exact flag word, words and constants
  preserved, linear cost.
- `Machine/AnyFlag.lean`: a two-tape scan over a flag word writing whether
  any flag is set at the key head, which advances; the flag word is preserved
  with its head on its blank end.
- `Machine/PlacementBank.lean`: reading a replaced bank cell by cell: at an
  active slot the replacement appears, elsewhere the original bank is
  unchanged; an exact contract placed by an injective slot map yields an exact
  whole-bank contract once the banks are compared index by index.
- `Machine/KeyRoutine.lean`: the repair key routine on seventeen tapes for
  the compact-control instance in the radices `2^q`, `2^b`: copy the rank's
  bits from the counter into the two address words, run the guard test and
  write the membership flag at the key's origin, run the inverse packed
  program and the ideal toggle, append the destination words to the key when
  flagged, and erase every scratch word. The counter, control and constants
  are preserved, the key holds the flag word of the repair scan, every head
  returns to its origin; linear cost. The placements and frames are
  generated mechanically. Widths and digit counts are built into finite control
  through counted copies and iterated guard/packed programs; this is a proved
  program family, not the fixed runtime-driven key required by EndToEnd.
- `Machine/OrderedSelect.lean`: ordered selection of records by a modular
  counter on six tapes (input, output, counter, addend, modulus, flag). One
  pass over nonblank records separated by single blanks: before each record the
  addend is accumulated into the counter and compared with the modulus; at or
  above it the modulus is subtracted and the record is copied, otherwise the
  record is skipped. Exact bank contract `select_hoare` with the counter word
  and selected records given by recursion, the value identity (running sum
  modulo the modulus, `rWord_value`, `sel_eq`), width invariants, and the
  closed cost `cost_le`: the input volume plus `10 L + 52` per record for a
  modulus of `L` bits.

- `Machine/TwosComplement.lean`: two's complement words, least significant
  bit first: the signed value `signed`, its bounds and its agreement with the
  unsigned value modulo `2^n`, sign extension `extTo`, the modular sum
  `addMod` of an extended word into a wider accumulator (exact when the sum
  fits, `signed_addMod`), and negation `negWord` (`signed_negWord`, except for
  the most negative value).

- `Machine/SignExtendAdd.lean`: the two-tape, four-state adder realizing
  `addMod`: one transition per accumulator cell, the addend head advancing
  over its bits and parking on its blank, the final carry dropped
  (`add_hoare`).

- `Machine/Negate.lean`: in-place two's complement negation on one tape,
  two states, one transition per bit (`neg_hoare`).

- `Machine/RulerAdvance.lean`: advance (`RulerAdvance.advance_hoare`) or
  retreat (`RulerRetreat.retreat_hoare`) a data head by the length of a
  unary ruler word, with the ruler head parked at its end or origin.

- `Machine/RulerCopy.lean`: copy as many zero-filled cells as a ruler is long
  from a source head to a destination (`copy_hoare`, the same `cells`
  semantics as the unrolled `CopyCells`), and `WriteSymbol`, a one-cell
  writer of a fixed symbol.

- `Machine/FixedMul.lean`: signed fixed-point multiplication on twelve tapes
  (generated like the key routine): operand copies replaced by magnitudes
  with the signs in two flag cells, the unsigned `BinaryMultiply` product
  padded to `2w` bits by a ruler copy, bits `p` to `p + w` copied into the
  output word, negated when the signs differ, all scratch erased
  (`mul_hoare`, cost `w(7w+18) + 50w + 4p + 140`).

- `Machine/FixedMulValue.lean`: the result word's signed value is the
  product truncated toward zero by `p` bits, `(x * y).tdiv 2^p`
  (`signed_result`), for widths `w ≥ p + 2` and magnitudes at most `2^p`.

- `Machine/RecordTape.lean`: blank-separated records: the cell before a
  record's origin is blank (`bg_left`), bit words map to records
  (`getD_map`), and `BackWord`, a four-state move from the origin of one
  record back to the origin of the previous one (`back_hoare`).

- `Machine/GaussianLine.lean`: the Gaussian window sums of the resampling
  map on twenty-two tapes (generated like the key routine). For each output
  `k`, the window loop runs `2m + 1` terms on a unary ruler: the weight word
  times the real and imaginary input words by two placed `FixedMul`s, the
  truncated products accumulated exactly into two `W`-bit accumulators
  (`accR`, `accI`); then the accumulators are written to the output and
  reset to zero words by a ruler copy, the input is rewound by `2(2m+1)`
  records with `BackWord`, and a modular counter (`OrderedSelect.rWord`)
  advances the input by one record exactly when the centre `⌊sk/t⌋` moves
  (`centre_succ`). Exact loop-state contracts `body_hoare`, `inner_hoare`,
  `rewind_hoare`, `cond_hoare`, `outer_hoare` and the whole line
  `line_hoare`, with the outputs `outWords` and cost `t` times
  `outerBound`.

- `Machine/GaussianLineValue.lean`: the accumulators of the Gaussian line
  hold the exact sums of truncated products: `accR_signed`, `accI_signed`
  give `signed (accR k i) = ∑_{j<i} (w_j · a_j).tdiv 2^p` when every word has
  magnitude at most `2^p`, width at least `p + 2`, and the accumulator width
  exceeds `p + log₂(2m+1) + 1` (`abs_tdiv_pow_le`, `abs_sum_le`).

- `Machine/PackedInverse.lean`: the inverse packed program on nine tapes:
  the four packed updates undone in reverse order with negated offsets as
  five gather-and-transduce lines, with exact list-level word semantics, the
  input words and control preserved, the offset scratch blank again and the
  recovered words on their own tapes with every head at its origin; linear
  cost.
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

- `Machine/BinaryDescriptorInstall.lean`: Places the actual five-state descriptor copier between arbitrary distinct tape slots. Exact whole-bank output replaces only the blank destination with the copied canonical descriptor at head one; source and every complementary tape/head are preserved. Runtime 2*length+5 and placement size derived from distinctness.

- `Machine/BinaryDescriptorInstallRaw.lean`: Actual copy followed by two-transition marker removal yields the marker-free descriptor at head zero required by bootstrap machines. Exact complete-bank setTape postcondition preserves source and all other tapes; fixed eight-state program costs2*length+8 including the join.

- `Machine/DimensionProductDescriptor.lean`: Physical six-tape product-descriptor constructor from two canonical binary inputs and wholly blank workspace. Installs markers, executes counted multiplication, restores scratch and preserves both inputs; exact canonical product output with bound53*N*W+28 for positive W.

- `Machine/TranslationDimensions.lean`: Actual nine-tape dimension bank from sole canonical b/W inputs. Fixed prefix/suffix counts select finite control; computes Q=q^b, P=q^(p*b), S=q^(s*b), B=S*W, preserves inputs and restores scratch. Exact canonical words and bound(24*p+24*s+333)*P*Q*B include every setup, conversion, product and join.

- `Machine/FlatCoordinateDimensions.lean`: Specializes physical dimension synthesis to an actual shared-prime coordinate target. Proves the constructed words literally match the canonical Q/P/B expected by FlatCoordinateSchedule, with common-volume runtime, preserved b/W inputs and blank initial workspace. Canonical b/Q/P/B descriptor lengths are bounded by twice common volume, charging later setup scans. Full stage-input installation remains separate.

- `Machine/PrefixWidthCopies.lean`: Replicates a sole preserved binary width into the exact physical PrefixCounterInit descriptor slots, with all fields, clocks and spare tapes initially blank. Proves full output-bank equality and runtime c*(2*length+6), including all copy joins.

- `Machine/PrefixWidthCopiesAt.lean`: Places prefix-width replication beside an arbitrary retained dimension bank, sharing its existing width source. Preserves every dimension-bank tape/head and constructs exact prefix input from blank, with no extra supplied source and unchanged copy bound.

- `Machine/FlatControlledShiftLayout.lean`: Exact complete input decomposition for the actual controlled-shift bootstrap. Exposes the prefix width bank and seventeen-tape suffix with only B/Q/P and payload supplied; every other tape/head is blank/zero. Identifies concrete descriptor slots for physical installation.

- `Machine/ControlledShiftDimensionInstall.lean`: Actual three-copy program installs B/Q/P from the retained nine-tape dimension bank into the controlled-shift suffix, starting each destination blank. Exact full-bank contract preserves dimensions and payload, with cost2*(length B+length Q+length P)+17 including joins.

- `Machine/FlatCoordinateShiftFromDimensions.lean`: Complete actual earlier-control shift from sole canonical exponent/record-width descriptors and payload, with all generated storage blank. Physically builds dimensions, installs prefix widths and B/Q/P, executes normalized shift, retains exact dimension bank and canonical transformed array. One dimension-independent machine has explicit linear common-volume bound charging all setup, scans and joins.

- `Machine/FlatCoordinateShiftInput.lean`: Exact initial common-payload contract and payload-independent private metadata for fully synthesized shift. Proves distinct physical payload slots and literal blank workspace at every slot except the sole exponent/record-width inputs and original payload. Supplies initialized-stage assembly contracts.

- `Machine/BinaryDescriptorInstallList.lean`: Compiles a fixed list of physical marker-free descriptor installations, with shared preserved sources and distinct blank destinations. Exact fold/setTape final bank, destination contents and frame preservation are proved. Costs sum(2*length+9), including cleanup and every join, with a uniform length bound.

- `Machine/FlatAffineScalingInputLayout.lean`: Fixed structural classification of every raw scaling input tape as workspace, payload or B/Q/P descriptor. Proves exact complete raw, ready and alphabet-lifted input banks, including all repeated dimensional words and blank head-zero workspace. Exposes the literal target layout for physical installation.

- `Machine/SharedBank.lean`: Actual placement of any fixed number of common tapes shared with a stage. Proves exact whole-bank execution with unchanged runtime; unused private selected slots remain literally blank frames, without implicit copying or head movement.

- `Machine/SharedBankFrames.lean`: Projection, clearing and frame lemmas for fixed shared banks, including exact empty private metadata through append/composition. Supports compiling initialized stages while keeping only permanent common inputs nonblank.

- `Machine/FlatCoordinateShiftInitializedStage.lean`: Fully synthesized controlled shift instantiates the original two-payload Stage interface with exact transform, private input independence and charged setup-inclusive linear cost. Entire program skeleton is independent of runtime width/record size; each private bank still supplies b/W.

- `Machine/FlatCoordinateShiftSharedBank.lean`: Four-tape common interface for initialized shifts: payload, output scratch and original b/W headers. Proves injective physical slots, exact common input/output with preserved headers, and literally blank entire private input after stripping common tapes; enables schedules with one physical b/W pair.

- `Machine/FlatAffineScalingInstall.lean`: Physical fixed descriptor-copy list installs every marker-free B/Q/P copy in the actual scaling input. Proves source-bank preservation, exact full layout handoff from blank workspace and coefficient-dependent linear-volume copying cost.

- `Machine/FlatCoordinateScalingConstruct.lean`: Complete actual coordinate scaling from sole canonical b/W and array. One coefficient/target-dependent program constructs dimensions, installs all descriptor copies, executes and normalizes the scaler, retaining dimension bank. Exact canonical scaled payload and blank workspace contract; explicit linear-volume bound includes every setup, scan and join.

- `Machine/SharedBankPair.lean`: Actual composition of two heterogeneous machines sharing any fixed common tape bank. Exact private frames and payload handoff are preserved with one charged join; unused private common slots remain blank.

- `Machine/SharedBankStage.lean`: Concrete stage contract and physical finite-list compiler over any fixed common-bank size. Proves folded common-state semantics, exact complete output, sum of stage runtimes plus all joins, and propagation of literally blank private input storage.

- `Machine/SharedBankSkeleton.lean`: Extracts fixed machine data from shared-bank stages and proves finite compilation depends only on those skeletons. Transports exact execution to a program selected independently of runtime semantic data, including a stronger theorem with entirely blank private inputs.

- `Machine/FlatCoordinateShiftSharedStage.lean`: Fully initialized controlled shift instantiates the four-common-tape Stage contract. Payload and sole b/W headers are shared, private input is literally blank, transition table independent of runtime dimensions, and exact affine transport and linear-volume cost are proved.

- `Machine/FlatCoordinateScalingSharedBank.lean`: Four-common-tape interface for fully initialized scaling, proving unique actual source classification, injective payload/header slots, exact common input/output and entirely blank private input. The original b/W descriptors are preserved physically.

- `Machine/FlatCoordinateScalingSharedStage.lean`: Actual initialized scaling instantiates the same four-common-tape Stage contract as shifts. Proves fixed skeleton, empty private metadata, coefficient/target-dependent linear cost and exact OrderedAffine transport; no computed dimensional input is supplied.

- `Machine/SharedBankStageInput.lean`: Literal common-bank input theorem: the first common tapes contain the supplied payload and headers, all others are blank at head zero. Fixed compiled Hoare execution preserves the exact final common bank and charges all stage costs and joins.

- `Machine/FlatCoordinateInitializedSchedule.lean`: One fixed physical machine executes any supported finite mixed scaling/shift schedule from the array and sole canonical b/W inputs with blank private storage. Exact ordered-affine output, preserved headers and explicit linear-volume runtime include all dimension synthesis, descriptor installation and joins.

- `Machine/Shared50InitializedSegments.lean`: Actual nonrecursive Shared50 field-program segments execute from sole b/W and payload with all private tapes blank. The fixed machine has exact field-program symbol transport and a setup-inclusive linear-volume bound; recursive interchanges and heterogeneous spectator layouts remain separate.

- `Machine/RunSupport.lean`: Actual transition induction bounds head displacement and changed cells by elapsed transitions, with exact preservation of all exterior cells. Hoare contracts from blank inputs yield concrete blank-workspace support bounds.

- `Machine/FlatCoordinateScheduleSupport.lean`: The verified initialized mixed schedule has private heads and nonblank private cells within its explicit linear-volume runtime interval. Exact common-bank output and affine semantics are retained; physical cleanup is not inferred from support alone.

- `Machine/StackPop.lean`: Fixed arbitrary-alphabet destructive stack transfer, controlled by a reusable binary clock. Heads move left together, preserving original data order and erasing exactly the popped region; all exterior cells, the immutable length descriptor and restored clock are retained. Exact whole-bank semantics and 7n+7 descriptor-length+16 time; initial head positioning and descriptor construction remain caller obligations.

- `Machine/RecursiveInterchangeLayout.lean`: Seven-factor recursive child descriptors preserve literal spectator order, exact role volume and next-depth row divisibility; physical scheduling is separate.

- `Machine/RecursiveInterchangeScaling.lean`: Actual normalized rational scaling on either H or D in an arbitrary positive seven-factor recursive layout. Exact serialized input/output and address transport preserve all rows and spectators, with a linear-volume runtime; canonical prefix/modulus/suffix descriptors remain supplied.

- `Machine/FixedControlTranslationStream.lean`: Actual counted family of rational-controlled D-fiber translations with a stationary physical H control. The middle-spectator count is arbitrary, every offset refresh/copy/join is charged, and the exact recurring endpoint preserves control. Prepared descriptors and markers remain explicit.

- `Machine/FlatFixedControlShift.lean`: Flat-array bridge for stationary-control translation across arbitrary middle spectators. Literal source word, exact destination coordinate transport, preserved physical H control and 529 times volume plus 23 runtime are proved. Outer H/prefix iteration and full bootstrap remain separate.

- `Machine/CyclicRowCopy.lean`: Arbitrary-alphabet row copy into one fixed role tape, with literal source/destination symbols, exact entire bank and reusable binary clock. No payload terminator assumptions; row count descriptor preserved.

- `Machine/CyclicRowCycle.lean`: One fixed finite cycle distributes successive equal-length rows over every fixed role tape using a shared reusable descriptor/clock. Exact role contents and all heads, with every copy and join charged.

- `Machine/CyclicRowSplit.lean`: Runtime-counted grouping repeatedly executes a fixed role cycle. Role j receives precisely its row from every group, including arbitrary payload symbols; complete bank and restored controls, fixed tapes/states independent of runtime dimensions and explicit 74-times-volume bound. Descriptor construction and positioning are separate.

- `Machine/CyclicRowMergeCopy.lean`: One actual arbitrary-symbol row transfer from a selected role back to a common output, preserving all other roles and restoring binary loop controls.

- `Machine/CyclicRowMergeCycle.lean`: Fixed role-by-role physical merge cycle with exact output concatenation, preserved input streams and summed count/copy/join runtime.

- `Machine/CyclicRowMerge.lean`: Runtime-counted physical merge restores cyclic row order from all role streams. Exact complete bank and advanced heads, restored controls and 74-times-volume bound; row permutation wiring, descriptor synthesis and rewinds remain caller work.

- `Machine/StackPush.lean`: Destructive arbitrary-symbol parking append via actual reflected StackPop transitions. Exact forward head displacement, preserved symbol order, source erasure and outside-region frames; reusable clock and immutable descriptor, with the same explicit length-plus-descriptor runtime.

- `Machine/CountedPosition.lean`: Fixed arbitrary-alphabet counted head motion preserves every payload cell, immutable binary descriptor and restored clock. Exact displacement for either direction, runtime 7n+7 descriptor-length+16 and canonical linear bound, including zero distance. No free seek is used.

- `Machine/RecursiveInterchangeRows.lean`: Actual cyclic split/merge instantiated for seven-factor recursive descriptors. Proves literal flat source and role serialization, original row roles*g+j, exact role descriptor addresses and 74-times-parent-volume bounds. Canonical row/group descriptors, prepositioned heads and role permutation wiring remain explicit.

- `Machine/TrackedCleanup.lean`: Actual data/tracker cleanup from a visited interval with an origin marker. Erases internally blank arbitrary data and tracker cells, restores both heads to zero, and proves a linear-radius bound without scanning parked ancestors.

- `Machine/TrackedExecution.lean`: Fixed two-transition simulation of each original transition on doubled tapes/states, same alphabet. Synchronized tracker heads and marked visited intervals preserve exact original execution and bound every private written cell; no runtime size changes the finite controller.

- `Machine/TrackedInit.lean`: Physically constructs tracker origin/initial-position marks from blank extra tapes for a fixed zero/one initial head pattern in two transitions, preserving original data.

- `Machine/TrackedHoare.lean`: Initialization plus tracked execution has exact original output, generated visited intervals, private support and 2 times original bound plus3 cost. No prebuilt trackers or runtime boundary descriptors are assumed.

- `Machine/TrackedCleanupOne.lean`: Tracker-only erasure restores its blank tape and head zero while permitting the associated common data tape and head to remain untouched.

- `Machine/TrackedCleanupAt.lean`: Physical placement of data/tracker or tracker-only cleanup in fixed bank slots with exact frame preservation and complete resulting banks.

- `Machine/TrackedCleanupList.lean`: Fixed finite list cleans every tracker and every selected private data tape, retaining designated common tapes/heads. Runtime is tapeCount times (5 times radius plus6); all runtime interval boundaries come from actual trackers.

- `Machine/CleanExecution.lean`: Generic actual composition initializes trackers, executes a fixed machine, and erases all private data/tracking storage. Exact retained output and blank workspace have explicit constant-factor time overhead.

- `Machine/FlatCoordinateCleanSchedule.lean`: One fixed initialized mixed affine schedule starts and ends with literal common array/scratch/b/W plus wholly blank private tapes and trackers. Every symbol has exact ordered-affine semantics; all initialization, execution and cleanup are linear in volume, enabling workspace reuse.

- `Machine/Shared50CleanSegments.lean`: Actual nonrecursive Shared50 field segments execute from sole canonical b/W and array, return the exact transformed canonical array and retained headers, and erase all private metadata/trackers with heads zero. Exact field-program semantics and linear-volume time; recursive heterogeneous execution remains separate.

- `Machine/CyclicRowRewind.lean`: Actual counted rewind of common and role heads preserves every arbitrary symbol. A fixed role cycle reuses the existing row/group descriptors without constructing a product count, and restores exact original heads in linear-volume time.

- `Machine/CyclicRowNormalized.lean`: Actual cyclic split/merge followed by counted rewinds return every payload head to its original position, retain exact source and role words, and restore both binary controllers. Canonical positive dimensions give a 149-times-volume bound.

- `Machine/RecursiveInterchangeRowsNormalized.lean`: Normalized split/merge specialized to literal seven-factor recursive arrays: exact cyclic role semantics, original heads restored, preserved controls and 149-times-parent-volume time. Descriptor synthesis and full recursive dispatch remain caller obligations.

- `Machine/PointwiseBinary.lean`: Fixed finite binary symbol operation executed over a runtime-counted pair of streams. Exact source preservation and pointwise destination/frame theorem, physical head advancement, restored clock and explicit runtime. XOR specializes correctly on encoded bits; payload rewinds and full sparse-circuit assembly remain separate.

- `Machine/RepeatedControlTranslationExecution.lean`: Actual middle-spectator translation group followed by one physical H increment. Exact recurring bank and charged arithmetic/control transitions; arbitrary middle count uses binary runtime control.

- `Machine/RepeatedControlTranslationStream.lean`: Nested physical middle-spectator/H loops handle arbitrary outer prefix cardinality, preserve exact source/output streams and restore zero H after complete cycles. Fixed20-tape machine,570 times volume plus 23; canonical descriptors and prepared metadata remain explicit.

- `Machine/FlatRepeatedControlShift.lean`: Literal flat-array source and every destination symbol for heterogeneous H-controlled D shifts, including exact rational offset and zero-control restoration across arbitrary prefix cycles.

- `Machine/CountedHyperVolumeLoop.lean`: Four independently counted runtime dimensions drive actual fixed finite loops, restoring all binary loop controls and charging every countdown/copy/join. No product descriptor or unrolled runtime-dependent program is assumed.

- `Machine/FlatHyperArrayNormalize.lean`: Physical four-dimensional array normalization copies the result, erases old payload scratch and returns both payload heads, using supplied dimension descriptors with all scans charged.

- `Machine/FlatRepeatedControlNormalize.lean`: Four-dimensional normalization placed on the existing 20-tape repeated-control bank, preserving all arithmetic metadata while returning canonical payload pair.

- `Machine/FlatRepeatedControlArray.lean`: Exact canonical transformed array for the normalized heterogeneous shift, with source/scratch payload interface and full-bank runtime 1005 times volume plus 26.

- `Machine/RecursiveInterchangeShift.lean`: Actual normalized H-controlled D shift on arbitrary positive seven-factor layouts. Exact rational H offset, preserved rows/spectators, canonical input/output arrays and restored zero control, with linear-volume time. Canonical B/Q/C/N descriptors and prepared arithmetic bank remain explicit; construction/cleanup separate.

- `Machine/FiniteReturnStack.lean`: Actual fixed-width binary return-address push/pop preserves all older frames, erases popped bits and restores the stack top. Pop halts in a finite state carrying the decoded address; width/state count depend only on fixed schedule, with depth-independent exact runtime.

- `Machine/FiniteDispatch.lean`: Fixed finite family dispatcher branches from an actual front-program halt state into its selected continuation in one charged transition. Exact execution, halting state and Hoare composition; all continuation programs are fixed in the finite controller.

- `Machine/FiniteReturnDispatch.lean`: Actual binary stack pop in a selected tape slot followed by decoded return-address dispatch into a fixed continuation family. Preserves the entire other-tape frame and charges width plus 2 plus continuation time. Full cyclic recursion and descriptor frames remain separate.

- `Machine/CyclicRowPermutedMerge.lean`: Fixed tape wiring restores logical cyclic row order when network output role j occupies physical tape rho j. Actual normalized merge retains exact role data/heads and unchanged runtime; no free payload permutation is assumed.

- `Machine/PointwiseBinaryNormalized.lean`: Counted finite-symbol operations followed by real two-head rewind preserve exact pointwise arrays and return both payload heads; immutable count and clock restored, with explicit normalized runtime and encoded XOR semantics.

- `Machine/PointwiseRoleGate.lean`: Actual normalized XOR placed between arbitrary distinct fixed role tapes, sharing one preserved binary length descriptor and restored clock. Exact complete bank and all unrelated words/heads retained.

- `Machine/PointwiseRoleCircuit.lean`: Fixed list of physical role XOR gates composes with exact folded array semantics and charged gate/join runtime. The finite machine is selected independently of runtime stream length.

- `Machine/SparseRoleCircuit.lean`: Literal tape execution of existing SparseCircuit.copies lists equals their Circuit.run and pointwise sum semantics on encoded ZMod2 arrays, with normalized heads and linear-volume bounds.

- `Machine/OneSourceCircuit.lean`: Proof-carrying compiler retains actual scalar instruction lists certified as distinct-source XOR gates, supporting finite restriction/embedding/renaming and exact tape-level Circuit.run semantics.

- `Machine/Shared50XorLists.lean`: Symbolic certificates show the actual optimized DAG, sparse input/output/central lists, invocation/inverse/exchange and reused-world global program are distinct-source XOR lists without expanding enormous instruction sequences.

- `Machine/Shared50TapeInvocation.lean`: Actual optimized local sparse invocation and exchange compile into fixed tape machines with exact data-bank transformations and arbitrary dirty-scratch restoration, preserved heads/backgrounds and charged linear stream runtime.

- `Machine/Shared50TapeGlobal.lean`: Actual complete reused-world Shared50 XOR program exchanges its data banks and restores arbitrary scratch streams on one fixed machine, with explicit linear tape-transition bound from the certified gate count. Canonical stream-length descriptor supplied; framed address transforms and recursive scheduling remain separate.

- `Machine/FiniteFlow.lean`: Actual fixed finite block controller permits terminal-state-dependent cycles, back-edges and self-edges. Each real block trace yields an exact machine run with one charged tape-preserving transition per jump; states equal the fixed sum of block states, independent of runtime depth.

- `Machine/FiniteReturnFlow.lean`: Binary return-address pop is a real block of the cyclic controller; decoded terminal states jump into fixed continuations and may revisit entry or pop. Exact charged return execution preserves other tapes. Recursive algorithm termination/correctness is separate.

- `Machine/RecursiveInterchangeVolume.lean`: Along actual seven-factor child selections, proves exact row and logical-volume division by roleCount^depth, unchanged non-row volume, retained original chunk lower bound and power-width depth bound. Parked ancestors never enter logical child volume; physical recursive execution remains separate.

- `Machine/RecursiveDimensionBank.lean`: Actual 13-tape dimension arithmetic preserves six canonical seven-factor headers, computes Q and successive A*rows, A*rows*beforeH, and full H-prefix count from blank outputs and scratch. Exact canonical outputs and 258 times volume plus 87 bound; physical installation into the shift bank is separate.

- `Machine/RepeatedControlBootstrap.lean`: Actual 21-tape bootstrap constructs physical zero H and every repeated-control metadata marker from B/Q/C/N/width and payload. No precomputed offset or radix control is supplied; exact prepared output and 15 times width plus 30 cost. Dimension-bank installation remains separate.

- `Machine/DelimitedReverseCopy.lean`: Actual reverse copy scans non-delimiter data until a physical marker, preserving source and arbitrary outside regions with exact head and linear word-length contracts.

- `Machine/DescriptorStackControl.lean`: Literal descriptor-stack seek and control steps, with genuine markers and scans rather than unknown-length seek primitives.

- `Machine/BinaryDescriptorStack.lean`: Fixed eight-state push/pop store delimiter-framed reversed binary descriptors and restore original bit order. Each costs 2 times bit length plus 7, with exact source/stack frames and no supplied runtime length; empty descriptors supported.

- `Machine/BinaryDescriptorStackRoundtrip.lean`: Concrete three-tape push/pop preserves source and complete older stack/head, restoring the exact canonical descriptor on an initially blank destination in 4 times bit length plus 15. Representation matches RadixZeroFill headers.

- `Machine/RecursiveDescriptorSize.lean`: Actual child-selection paths bound recursion depth by log2 of logical child volume. Root-bounded canonical descriptor lengths are at most a fixed role-count-dependent multiple of child log-size, hence of child volume. This charges linear descriptor scans without counting parked ancestors; arbitrary polynomial descriptor algorithms and physical recursive execution are separate.

- `Machine/RecursiveDescriptorStack.lean`: Connects the actual delimiter-based binary push/pop roundtrip to the recursive descriptor-size theorem. Exact restored descriptor and complete older-stack preservation cost at most (8*(log2 roles+2)+15) times logical child volume; an intervening recursive call remains separate.

- `Machine/BinaryDescriptorInstallMarkedList.lean`: Fixed lists of physical marked binary-header copies preserve the source bank and charge all copies, markers and joins; runtime descriptor values never enter the transition table.

- `Machine/RecursiveShiftInstall.lean`: Five physical descriptor copies connect the generated recursive dimensions to a blank shift workspace, preserving original headers and payload.

- `Machine/RecursiveShiftInitialize.lean`: One fixed machine constructs all heterogeneous shift metadata from six canonical layout headers and payload, with exact prepared endpoint and linear-volume setup cost.

- `Machine/RecursiveInterchangeShiftConstruct.lean`: Complete 34-tape heterogeneous H-controlled D shift from six original headers and payload, with all private input blank. Exact seven-factor symbol transport and normalized payload cost 1288 times volume plus 186, including physical setup; generated metadata remains at output.

- `Machine/BinaryDescriptorStackAt.lean`: Places actual variable-length descriptor push/pop on any two distinct tape slots, preserving every other tape and charging exact runtime.

- `Machine/BinaryDescriptorFrames.lean`: Fixed lists of runtime binary headers push in order and pop in reverse with exact older-stack restoration. Actual same-bank roundtrip preserves source fields and writes initially blank distinct destinations, costing four times total bit length plus sixteen times field count plus one; programs are independent of descriptor lengths.

- `Machine/RecursiveInterchangeShiftClean.lean`: Clean reusable 68-tape heterogeneous controlled shift from six canonical layout headers and sole payload. Exact transformed array, retained original headers, all generated private metadata and trackers erased at head zero, with setup/execution/cleanup bound 221536 times volume plus 32370. Fixed machine independent of runtime layout.

- `Machine/Shared50OrderedPieces.lean`: Actual fixed clean machines for certified nonrecursive segments and globally wired scalar XOR gates from the ordered control. Segment semantics use equal-width coordinates; heterogeneous header construction, whole-bank joining and recursive continuations remain separate.

- `Machine/Shared50PieceSchedule.lean`: Fixed actual list of certified segments, explicit role-and-coordinate recursive calls, and scalar gates. Expansion equals the original control atom by atom, with exact improved recursive-call count. Whole-machine compilation remains separate.

- `Machine/RecursiveDescriptorFrames.lean`: Actual fixed-list descriptor push/pop and same-bank roundtrip charged to logical child volume using canonical root-bounded header lengths. Six-field roundtrip costs at most (48*(log2 roles+2)+97) times child volume.

- `Machine/RecursiveHeaderBounds.lean`: Every actual six-field recursive header is bounded by its layout volume and the original root volume. Canonical active or saved-ancestor headers therefore satisfy the child-volume scan bound without a separate descriptor-size assumption; parked ancestor storage is excluded.

- `Machine/FiniteReturnStackAt.lean`: Places real binary PC push and decoded dispatch on one selected tape while framing all other tapes. Exact dispatch retains the finite terminal-state result for controller composition.

- `Machine/RecursiveFrameControl.lean`: Concrete static call/body/return assembly physically saves descriptor fields and PC, restores fields, pops PC and dispatches to the decoded continuation. Exact tape and terminal-state contracts charge every join. The supplied body must establish intact saved stacks and blank restoration destinations; recursive child execution remains an explicit obligation.

- `Machine/BinaryDescriptorCleanupList.lean`: Fixed physical list of marked binary-header erasures. Every bit and marker is erased, heads return to zero and all other tapes are framed; exact cost two times total bit length plus five times field count. No runtime length enters control.

- `Machine/BinaryDescriptorFrameRestore.lean`: Actual cleanup followed by descriptor-frame pop accepts nonblank child headers, physically erases them and restores saved ancestor headers in the same slots. Exact older stack/head and spectator preservation, with cleanup, joining and pop costs explicit.

- `Machine/RecursiveHeaderRestore.lean`: Actual parent-header restoration costs at most (fieldCount*(8*(log2 roles+2)+13)+1) times logical child volume. Canonical old/current layout headers and paths discharge size assumptions; six-field bound is (48*(log2 roles+2)+79) times child volume. No free header reset.

- `Machine/RecursiveDescriptorDivision.lean`: Bounds the actual five-tape binary long-division runtime by (40*(log2 roles+2)^2+54*(log2 roles+2)) times logical child volume for canonical root-bounded input descriptors. Proves the quadratic logarithm estimate and retains exact shifted remainder/quotient output banks; canonical output normalization and caller integration remain separate.

- `Machine/RecursiveScalingDimensions.lean`: Physical 16-tape construction of heterogeneous scaling dimensions from six canonical layout headers, including required suffix or prefix products for H or D. Exact outputs, preserved headers and 364 times volume plus 145 setup cost.

- `Machine/RecursiveScalingInstall.lean`: Fixed physical marked-header installation and scaling workspace setup connects synthesized dimensions to the normalized scaler; exact canonical metadata and framed payload, with every copy and join charged.

- `Machine/RecursiveInterchangeScalingConstruct.lean`: Complete initialized H/D scaling from six original headers and payload with blank private input. Physical dimensions, installation, arithmetic and normalization give exact spectator-preserving array transport and an explicit coefficient-dependent linear-volume bound.

- `Machine/RecursiveInterchangeScalingClean.lean`: Clean reusable heterogeneous H/D scaling retains six original headers and normalized payload pair, erasing all generated metadata and trackers at head zero. Exact canonical bank independent of H/D selection and explicit setup/execution/cleanup linear-volume bound; coefficient and tape count are fixed independently of runtime layout.

- `Machine/CleanSubbank.lean`: Fixed injective placement executes a clean local machine on selected permanent tapes with blank private storage. Exact input/output payload agreement and spectator framing imply the unchanged runtime contract for the whole bank; no implicit copies or head resets.

- `Machine/CleanSubbankCompile.lean`: Finite physical composition of clean permanent-bank stages returns literal blank private input/output and charges every joining transition. Works for arbitrary permanent banks and heterogeneous layouts, with actual stage contracts supplied.

- `Machine/RecursiveShiftRoleBank.lean`: One layout-independent machine shifts a selected permanent role in any positive seven-factor layout. Shared six canonical headers, all other roles and arbitrary auxiliary tapes are preserved, private work is blank again, and exact symbol transport costs 221536 times volume plus 32370. Header updates are separate.

- `Machine/RecursiveCleanReturn.lean`: Actual header cleanup, saved-descriptor restoration and binary PC pop/dispatch composed into one return routine, with exact selected continuation terminal state. Conditional body interface allows nonblank child headers and charges all erasure and joins; recursive body implementation remains open.

- `Machine/DigitInterchangeRows.lean`: Literal serialization for width-one interchange: the first cyclic split role word equals the second split input, and transposing fixed radix-role indices gives exactly the transposed leaf words while preserving arbitrary outer, middle and suffix fields.

- `Machine/DigitInterchangePasses.lean`: Actual normalized tape contracts for both split and both merge levels of single-digit interchange. Input/output words match literally, heads and descriptors are restored, and the total pass cost including joins is at most (597+2*q) times volume. Whole-bank joining, counter synthesis and private cleanup remain separate.

- `Machine/BinaryCanonicalTrim.lean`: Actual backward erasure of high zero bits in a marked binary word followed by origin reset. Four states, exact canonical value-preserving output at head one, including empty and all-zero words.

- `Machine/BinaryQuotientNormalize.lean`: Nine-state two-tape erase-copy, zero trim and rewind normalizes a raw division quotient in two times its length plus eight transitions. Raw source is wholly blank at head zero; destination is canonical at head one.

- `Machine/BinaryDivideQuotient.lean`: Six-tape physical division followed by quotient normalization. Exact quotient arithmetic and canonical output on sixth tape, erased raw quotient tape, with original division cost plus two times dividend length plus nine. Input head preparation and shifted remainder cleanup remain explicit.

- `Machine/RecursiveQuotientDivision.lean`: Physical division-plus-normalization runtime bounded by (40*A^2+58*A+9) times logical child volume, where A=log2 roles+2, for canonical root-bounded descriptors. No free quotient normalization; full canonical input preparation and remainder cleanup remain separate.

- `Machine/RecursiveChildDimensions.lean`: Nineteen-tape physical construction of child layout powers and products from six parent headers plus explicit canonical divided-width and divided-row headers. Eight real arithmetic stages emit exact six child headers with bound (48*(m-1)+512) times child volume plus 119; no derived product oracle.

- `Machine/RecursiveChildDimensionsClean.lean`: Thirty-eight-tape clean child-header constructor retains parent and quotient headers plus required child products, erasing all intermediate powers, scratch and trackers. Exact canonical child descriptor, volume division and bound 97*(48*(m-1)+512) times child volume plus 11756. Quotient production and child-bank installation remain separate.

- `Machine/BinaryDescriptorDivisionRaw.lean`: Physical raw division and quotient normalization at cell-one origins, exposing exact shifted remainder and retained dividend/divisor banks for boundary setup and cleanup.

- `Machine/BinaryDescriptorDivisionBoundary.lean`: Actual marked-input preparation, dividend scan, division invocation and marker restoration. Every seek and boundary operation is charged; supplies fixed zero/one input heads for physical workspace tracking.

- `Machine/BinaryDescriptorDivision.lean`: Complete fixed 12-tape marked binary division from two input headers and blank workspace. Inputs preserved, canonical quotient returned at head one, and all nine other private tapes physically erased at head zero, including shifted remainder. No free input setup, quotient normalization or cleanup.

- `Machine/RecursiveCleanDescriptorDivision.lean`: The complete clean descriptor divider has runtime at most (1280*A^2+1920*A+710) times logical child volume for canonical root-bounded inputs, A=log2 roles+2. Exact division arithmetic, input preservation and clean quotient endpoint share the same fixed machine.

- `Machine/BinaryDescriptorReplaceList.lean`: Fixed physical replacement of occupied binary-header slots: erase old marked words, install new words from disjoint sources, preserve all other tapes. Exact bank theorem and fieldCount*(4*maxWidth+11)+1 runtime include every erased bit, copy and join.

- `Machine/RecursiveChildHeaderInstall.lean`: Fixed five-header replacement in the actual child-constructor bank, retaining A in place. Generated-output source and destination conditions are discharged; exact installed child words and (40*(log2 roles+2)+56) times child-volume bound. Parent values must be saved before destructive installation; duplicate source cleanup and full caller composition remain separate.

- `Machine/RecursiveScalingRoleBank.lean`: Layout-independent physical H/D scaling of a selected role on the same permanent bank used by recursive shifts. Retains six headers, other roles, arbitrary auxiliary data and clean private storage; exact array transport and coefficient-dependent linear-volume cost.

- `Machine/RecursiveXorRoleBank.lean`: Actual selected-role XOR on the permanent recursive bank, preserving all headers, spectators and supplied length/clock control. Exact binary addition and 14 times volume plus 14 times descriptor length plus 33 runtime; length synthesis is separate.

- `Machine/RecursiveRoleSerialization.lean`: Exact equality between canonical four-symbol shift/scaling payload words and the pointwise XOR bit-stream encoding. Mixed operations need no uncharged representation conversion.

- `Machine/RecursiveMixedSchedule.lean`: One runtime-independent fixed mixed shift/scaling/XOR program on a shared permanent bank. Exact whole-block semantics, literal blank private input/output and sum-of-stage-costs plus charged joins; explicit compile-time linear-volume coefficient. Uses one unchanged six-header view and a supplied short stream-length descriptor; paid coordinate regrouping and recursive calls remain separate.

- `Machine/RecursiveChildQuotientsConstant.lean`: Fixed compile-time divisor word is physically initialized with marker and head restoration, charging three times bit length plus six transitions.

- `Machine/RecursiveChildQuotients.lean`: Two clean divisions plus actual fixed-divisor initialization/erasure generate width/m and rows/roles from six parent headers. Exact 38-tape output matches the child-dimension constructor input, with no supplied divisor or quotient words.

- `Machine/RecursiveChildQuotientsBound.lean`: The actual paired quotient computation has linear logical-child-volume cost, absorbing fixed divisor lengths into its constant without assuming divisors are root-volume bounded.

- `Machine/RecursiveChildHeaderHandoff.lean`: Physically installs generated child headers and erases temporary quotient/product copies. Exact final standard six-header bank, every other tape blank at zero; bound30 times maximum header length plus82. Composes directly with dimension generation.

- `Machine/RecursiveChildPrepare.lean`: One fixed 38-tape machine starts with only six canonical parent headers and ends with only the actual six canonical child headers. Divisors, quotients, powers, products, occupied-header replacement, copy erasure and joins are all physical and charged to logical child volume. Saving parent headers and array/recursive control remain caller operations.

- `Machine/DigitInterchangeBank.lean`: One fixed bank for width-one interchange with source, role streams, radix-pair leaf streams, merge streams, clocks and four supplied counters. Exact per-pass placements and spectator preservation support the whole-bank sequence.

- `Machine/DigitInterchangeCompile.lean`: Actual same-bank sequence of two outer passes and twice-radix inner passes transposes the digit fields and overwrites the original source. Exact intermediate serialization and head restoration; cost at most (597+2*q) times volume including joins.

- `Machine/DigitInterchangeClean.lean`: Physically initializes loop markers, executes the entire single-digit interchange, then erases all temporary streams, clocks and trackers. Same canonical source/scratch bank with four retained descriptors, exact transposed payload and explicit linear-volume cost. Counter synthesis from six recursive headers remains separate.

- `Machine/RecursiveVolumeConstruct.lean`: Fixed 295-state machine physically computes full stream volume from six canonical layout headers and initializes the XOR clock. Exact canonical product and retained headers, with417 times volume plus176 setup cost.

- `Machine/RecursiveVolumeClean.lean`: Clean 34-tape volume/clock constructor retains only six original headers and the two generated controls. Every private tape and tracker blank at zero; bound36279 times volume plus15503, hence51782 times positive volume. Canonical generated word has bit length at most volume.

- `Machine/RecursiveVolumeRoleBank.lean`: Physical volume/clock initialization on the permanent recursive role bank, starting with both control tapes blank. Every role and arbitrary auxiliary tape is preserved; exact prepared endpoint and private cleanup.

- `Machine/SharedBankRawCompose.lean`: Actual fixed-skeleton composition with changing leading common banks and blank private endpoints. Proves exact input/output bank and sum of runtimes plus one joining transition, independent of semantic-stage packaging.

- `Machine/RecursiveMixedInitialized.lean`: One fixed machine initializes its own XOR clock and volume word from six canonical headers, then executes the actual mixed shift/scaling/XOR list. Exact role-array semantics and clean private endpoint, bound(51783+sum operation coefficients+operation count) times volume. Generated controls remain explicit at output; per-operation coordinate-view changes and recursive calls remain separate.

- `Machine/RecursiveChildCallSetup.lean`: Actual fixed 40-tape call entry saves six parent headers and compile-time return PC, then physically computes/installs child headers. Both saved stacks survive complete arithmetic. Exact child bank and coefficient RecursiveChildPrepare.constant+24*(log2 roles+2)+50+PCwidth times child volume; array parking and recursive body remain separate.

- `Machine/RoleArrayStackMoves.lean`: Physical counted role-array head movement and control-marker setup/erasure used by destructive parking and recovery. Arbitrary payload symbols and exact whole-bank endpoints; no delimiter-based payload scan.

- `Machine/RoleArrayStack.lean`: Actual destructive role-array push with source reset to blank/head zero and inverse pop restoring source and older stack exactly. Work clock initialized and erased physically; push14*N+14*bitLength+45, pop14*N+14*bitLength+49.

- `Machine/RoleArrayStackAt.lean`: Injective placement of the actual four-tape role-array push/pop routines into a fixed larger bank with exact spectator framing.

- `Machine/RoleArrayFrames.lean`: Fixed-list inactive role parking and reverse recovery, independent of runtime lengths. Every vacated role/work clock becomes blank/head zero; exact older stack and original roles recovered with allocated-interval blank precondition. Canonical positive volume gives88*count*N push,92*count*N pop, and(180*count+1)*N actual roundtrip.

- `Machine/RecursiveDigitLayout.lean`: Width-one recursive array view with exact full row-major serialization and digit-transpose address semantics, preserving every outer/middle/suffix spectator for arbitrary native alphabet payloads.

- `Machine/RecursiveDigitDimensions.lean`: Physical construction of all four base-case counters from six recursive layout headers: scaling suffix products plus a real outer-times-middle product. No derived counter inputs;417 times volume plus174 setup cost.

- `Machine/RecursiveDigitInstall.lean`: Four actual marked copies install generated dimensions into the single-digit interchange bank, preserving original headers and payload and charging every copy and join.

- `Machine/RecursiveDigitInterchangeConstruct.lean`: Complete width-one interchange from six original headers and sole array. Physically constructs/install counters, initializes loop markers, executes the whole-bank interchange and returns exact transposed source; explicit setup-inclusive linear-volume bound.

- `Machine/RecursiveDigitInterchangeClean.lean`: Fully initialized clean recursive base case: sole six canonical headers and array, width one, fixed q-dependent program. Exact digit-swapped array on original source with blank scratch, original headers retained, every private tape/tracker erased at zero, and explicit full linear-volume bound.

- `Machine/RoleArrayMove.lean`: Physical destructive arbitrary-symbol transfer into a blank origin tape, with source and reusable clock erased and both heads reset. Exact spectator preservation; canonical positive count gives87*N runtime.

- `Machine/RoleArrayCall.lean`: Actual inactive-role parking, active-role move into common child source, explicitly framed child execution, move back and reverse recovery. Exact whole-bank result changes only the active array under the child contract; overhead(180*roleCount+178)*N, including every join.

- `Machine/RecursiveAffineViews.lean`: Within-H, within-D and cross coordinate views preserve exact index/volume identities and literal serialized payload words.

- `Machine/RecursiveAffineDimensions.lean`: Actual four-power/four-product constructor for within-group coordinate-view headers, with all seven joins charged.

- `Machine/RecursiveAffineDimensionsBound.lean`: Every generated power and product is bounded by unchanged stream volume; physical constructor costs at most(96*m+512)*V+119.

- `Machine/RecursiveAffineDimensionsClean.lean`: Fixed output relabelling aligns generated view headers with handoff ports; physical tracked cleanup erases all private intermediates.

- `Machine/RecursiveAffinePrepare.lean`: Complete within-group view preparation from sole six canonical headers: quotient synthesis, powers/products, occupied-header replacement and source erasure, with linear unchanged-volume cost.

- `Machine/RecursiveCrossPrepare.lean`: Complete cross-group view preparation on canonical38-tape bank with preserved row count and linear volume cost, requiring no root-path hypotheses.

- `Machine/RecursiveViewRoleBank.lean`: Fixed cross/within selector places paid view changes on permanent roles/scratch/header/aux bank; exact preservation of every payload and auxiliary, all private tapes blank. Parent header save/restore and scalar semantic composition remain separate.

- `Machine/RecursiveRowsQuotient.lean`: Real constant-role initialization and clean marked division compute canonical rows/roles from parent headers. Fixed38-tape bank, preserved six headers and explicit linear parent-volume cost.

- `Machine/RecursiveRowsDimensions.lean`: Actual quotient, scaling products and row/group products construct normalized cyclic-transfer descriptors from sole six parent headers. Exact generated values, canonicality, header preservation and linear volume bound; installation, source erasure and transfer assembly remain separate.

- `Machine/RecursiveWidthBranch.lean`: Actual fixed three-block finite flow selects supplied base or recursive block from the physical guard, with at most three charged transitions. Canonical38-tape headers and power-width depth select the correct actual branch; branch bodies remain explicit.

- `Machine/RecursiveWidthGuard.lean`: Physical four-state width-one test preserves the exact bank in at most two transitions; canonical descriptor value selects actual base/recurse terminal state for finite-flow dispatch.

- `Machine/RecursiveStackAllocation.lean`: Blank suffix invariants discharge descriptor, PC and role-array free-interval premises. Actual pushes and child payload entry preserve availability at the advanced stack head; concrete saved header/PC stacks retain both free suffixes, without a recursion-depth capacity assumption.

- `Machine/RecursiveDigitRoleBank.lean`: Places the fully initialized clean digit interchange at one permanent role, with canonical six headers, exact Fin4 serialization, all spectator roles/auxiliaries preserved and complete private cleanup. Symbolic port proofs and explicit linear-volume cost.

- `Machine/RecursiveBaseBranch.lean`: Actual digit-role base machine bound into the physical width controller. Width-one input runs guard/edge and complete base interchange within the base linear bound plus three transitions, preserving the exact shared bank and terminal control; the recursive block remains supplied.

- `Machine/RecursiveViewFrame.lean`: Fixed six-header push and occupied-header cleanup/pop on a dedicated stack, exact older-stack preservation, explicit free interval and runtime bounds independent of word lengths in control.

- `Machine/RecursiveViewFrameRoleBank.lean`: Places real six-header save/restore on the permanent role bank with a dedicated stack and clean private workspace, retaining all payloads and auxiliary tapes exactly.

- `Machine/RecursiveViewedAction.lean`: One fixed physical push/view/shift-or-scale/restore composition returns parent headers, dedicated stack and private work exactly, retaining auxiliaries and producing the transformed array in its parent-volume type. Linear coefficient is view cost plus action cost plus202; matching ordered scalar descriptions remains separate.

- `Machine/CountedBankReset.lean`: Actual simultaneous counted erasure and rewind of selected arbitrary-symbol tapes, preserving spectators and physically restoring heads; descriptor-sensitive and linear runtime bounds.

- `Machine/CountedBankResetHeader.lean`: Initializes counted bank reset from a canonical count header and two blank work tapes, including descriptor copy and clock setup with every transition charged.

- `Machine/RecursiveRowsInstall.lean`: Physically copies generated row/group headers and initializes both loop clocks for the normalized cyclic transfer bank.

- `Machine/RecursiveRowsConstruct.lean`: Composes quotient/product construction, descriptor installation and normalized split/permuted merge from sole six parent headers, with exact intermediate banks and charged setup.

- `Machine/RecursiveRowsResetCount.lean`: Physically computes common or role volume from generated row dimensions for counted payload erasure.

- `Machine/RecursiveRowsMove.lean`: Actual initialized cyclic split erases the copied common source; actual permuted merge erases every consumed role source. No supplied derived counters or free resets.

- `Machine/RecursiveRowsClean.lean`: Complete tracked workspace cleanup after initialized destructive split/merge. Same reusable bank with original six headers and output payloads, all private tapes blank and heads restored; explicit linear parent-volume cost.

- `Machine/RecursiveRowsRoleBank.lean`: Fixed injective placement of clean initialized split/permuted merge on permanent roles/scratch/six-header/auxiliary bank. Deterministic updated role payloads, exact spectators, blank consumed sources and private workspace; native arbitrary alphabet.

- `Machine/RoleArrayCallBoundary.lean`: Separate fixed physical entry park/move and return move/recover blocks expose exact entered banks without embedding a child program. Entry(88*roleCount+88)*V and return(92*roleCount+88)*V, including joins, support cyclic control edges.

- `Machine/RecursiveChildSetupRoleBank.lean`: Places actual40-tape header/PC save and child preparation on permanent role bank with fixed two-stack auxiliary suffix, preserving payloads and other auxiliaries with blank private workspace. Generic placed_hoare also lifts exact header/stack return contracts.

- `Machine/RecursiveRowsSerialization.lean`: Exact Fin4 parent-array to cyclic child-role serialization and inverse permuted merge on the permanent shared bank, inheriting the physical clean-transfer runtime. Deterministic data banks supply all frame equalities; spectator child-layout casts preserve literal tape words with parent headers retained until physical child setup.

- `Machine/SharedBankFamily.lean`: Pads a finite family of clean leading-bank machines to one fixed sum-bounded tape count, preserving each state count, every common slot, exact blank private endpoints and original runtime. No tape movement or runtime dimension enters the workspace bound.

- `Machine/Shared50RecursiveControl.lean`: Fixed finite graph over the exact Shared50 piece list: physical width guard, split/body/merge nodes, shared header restoration and real PC pop, per-call entry/recovery nodes, and a root halt sentinel. Actual call-site codes decode to their recovery nodes; root header/PC initialization is physically charged. Different fixed private banks are padded to one finite-family tape count; block implementations and recursive execution remain explicit obligations.

- `Machine/RecursiveCoordinateDigits.lean`: Exact one-field and ordered control/target decompositions of the existing MSB-first rank encoding, with literal coordinate-update identities.

- `Machine/RecursiveScalarSelection.lean`: Static compiler maps actual ordered scalar descriptions to within-H, within-D or cross paid views and exact rational shift/scaling operations, preserving reflected subtraction order.

- `Machine/RecursiveScalarCoordinates.lean`: Selected-view typed indices equal original heterogeneous positions exactly; writes to exposed H/D coordinates are writes to the original numbered fields.

- `Machine/RecursiveScalarTransport.lean`: Paid view/action/restore arrays implement the original scalar instruction on original field coordinates, preserving every other role; compile_entry and compile_other bridge actual scalar descriptions.

- `Machine/RecursiveScalarSchedule.lean`: Finite physical composition of paid varying-view scalar wrappers restores parent headers, dedicated stack and auxiliaries between stages, with exact ordered semantics and a fixed linear-volume coefficient.

- `Machine/Shared50RecursiveSegments.lean`: Instantiates every actual Shared50OrderedPieces.Segment on its original wire. Clean permanent-bank output implements exactly original AffineFieldProgram.run on heterogeneous coordinates, preserves all other roles, and costs coefficient times volume. Applicable to row-reduced role descriptors without another row division.

- `Machine/RecursiveRoleChildCallSetup.lean`: Correct recursive network call entry saves already-row-reduced parent headers and return PC, then physically installs a cross child view with divisor1. Rows remain unchanged, avoiding double division. Same permanent-bank placement; setup and matching occupied-header return have path-free linear role-volume bounds.

- `Machine/RecursiveChildCallReturn.lean`: Accepts the exact bank and savedStacks generated by actual child entry, physically erases occupied child headers and restores parent headers while retaining the pending PC frame. Exact bank compatibility, with free descriptor stack supplied by its blank-suffix invariant.

- `Machine/RecursiveChildReturnRoleBank.lean`: Places header restoration on the permanent bank independently or before actual PC pop/decode/continuation execution. Exact final continuation state survives both compositions; original roles/auxiliaries and older stacks restored. Same-root path bound is(48*(log2 roles+2)+PCwidth+82)*childVolume plus continuation cost.

- `Machine/SharedBankFamilyExact.lean`: Uniform private workspace padding preserves exact execution lengths, terminal finite states and halted configurations; finite-family members retain both bank and control endpoints.

- `Machine/Shared50RecursiveExecution.lean`: The actual uniformly padded cyclic width guard preserves the complete bank and selects the base or split block in at most three transitions, including its real finite-flow edge. Recursive body execution remains open.

- `Machine/RecursiveRowsNodeLayout.lean`: Splitting once and then creating a divisor-one child equals the original child layout; reduced-row descriptors retain positivity under divisibility.

- `Machine/RecursiveRowsNodeHeaders.lean`: Physically installs the quotient row header, erases its temporary source, and preserves the other five headers, with canonical reduced-row values and a linear-volume bound.

- `Machine/RecursiveRowsNodeRoleBank.lean`: Places paid reduced-row header construction on the permanent role bank with exact payload and auxiliary preservation and blank private workspace.

- `Machine/RecursiveRowsNode.lean`: Actual node entry saves six original headers, splits rows and installs reduced headers; exit restores occupied headers and performs permuted merge. Exact banks, linear-volume costs and nested descriptor-stack availability are proved; network execution remains separate.

- `Machine/Shared50RecursiveReturnExecution.lean`: Actual placed and uniformly padded PC pop erases the encoded frame, restores the older stack and preserves every spectator tape. Its real finite-flow jump selects the encoded recovery or root halt node in exactly k+2 transitions, retaining decoded control states throughout.

- `Machine/RecursiveCallCount.lean`: Physically generates the role volume from six canonical headers on fixed private workspace, retaining a blank loop clock and preserving all other common tapes; exact count erasure restores its slot.

- `Machine/RecursiveCountedCallBoundary.lean`: Separate payload entry and recovery machines construct their own volume count, park or recover role arrays, and erase the count. Clock and count are blank at recursive boundaries; all setup and cleanup are charged linearly in volume.

- `Machine/RecursiveCallBank.lean`: Permanent bank places role payloads, scratch, six headers, clock/count/payload stack, auxiliary spectators and descriptor/PC stacks in fixed slots; actual payload entry preserves this layout.

- `Machine/RecursiveCallProtocol.lean`: Actual child entry composes initialized payload parking/movement with same-row header and PC setup. Recovery regenerates the restored parent volume, retrieves payloads and clears controls. Exact banks and linear role-volume costs are proved; matching child execution to the recovery input and global auxiliary placement remain separate.

- `Machine/RecursiveMixedClean.lean`: Physically erases the generated mixed-operation clock and volume descriptor after execution, retaining exact original headers, payloads and auxiliaries with all private work blank; linear-volume bound includes cleanup.

- `Machine/RecursiveMixedRoleBank.lean`: Places complete initialized and cleaned mixed operations on permanent role/header banks, preserving arbitrary saved stacks and other auxiliaries without supplying any XOR controls.

- `Machine/Shared50RecursiveGates.lean`: Every literal Shared50 scalar gate has an actual fixed tape machine with complete setup/cleanup and exact original module-gate semantics on arbitrary encoded bit streams, including dirty scratch. Cost is at most 51858 times logical volume.

- `Machine/Shared50NodeSegments.lean`: Original paid nonrecursive segments run on unchanged World role indices plus a final common input/output tape. Exact field-coordinate semantics and IO preservation with fixed linear-volume costs.

- `Machine/Shared50NodeGates.lean`: Literal gates on the complete node payload bank preserve common IO and arbitrary stacks; original binary module-gate semantics, exact whole-bank endpoints and fully charged linear-volume execution.

- `Machine/Shared50RecursiveNodeLayout.lean`: Original World enumeration remains in its existing role slots, with common IO last; role count equals W and physical merge permutation is the conjugated involutive original route.

- `Machine/Shared50RecursiveNodeRows.lean`: Cyclic split and permuted merge match the exact parent H/D transpose through row and suffix packing, including within-role address swapping.

- `Machine/Shared50RecursiveNodeSemantics.lean`: Full fixed Shared50 control on binary cyclic fibers yields exactly the permuted merge input; actual node exit restores original headers and merges to parent transpose. Actual piece execution equivalence remains separate.

- `Machine/Shared50RecursiveNodeTranspose.lean`: Quotient/remainder decomposition covers every original row; transpose semantics hold at every seven-factor and complete scalar-coordinate address.

- `Machine/Shared50RecursiveNodeBinary.lean`: Actual split and fixed-control output arrays equal the node gate binary encodings with blank common IO. Flat cyclic serialization agrees with scalar-coordinate routed transpose, providing the binary induction bridge.

- `Machine/Shared50RecursiveBank.lean`: Fixed tape permutations align local common banks with the call bank without moving data or adding transitions. Distinct clock, count, payload, node-view, scalar-view, descriptor and PC slots; exact endpoint reconstruction and return-stack placement.

- `Machine/Shared50RecursiveBankNodes.lean`: Actual split/merge, scalar-segment and gate skeletons execute on the single call-compatible permanent bank. Saved node frames and blank scalar-view stacks are distinct; exact bank endpoints and original runtime costs are retained.

- `Machine/Shared50RecursiveBankReturn.lean`: Actual base interchange and ancestor-header restoration share the global bank. Exact payload/header/stack endpoints, linear role-volume return cost and literal pending-PC reset match the physical decoder.

- `Machine/Shared50PieceSemantics.lean`: The actual segment/call/gate piece list expands exactly to the original fixed interleaved control; its full routed H/D transpose semantics follow in original execution order.

- `Machine/Shared50NodePieceTransport.lean`: Actual segment/gate array folds match original scalar-coordinate fibers, preserve IO, and give routed transpose conditional on the exact selected-coordinate child interchange contract. No physical child execution is supplied by this theorem.

- `Machine/Shared50RecursiveCallLayout.lean`: Fixed parking order includes exactly the original World roles except the active stream, excludes the separate IO tape and is duplicate-free. Used by actual controller call entry/recovery.

- `Machine/Shared50RecursiveImplementation.lean`: Instantiates every Shared50 controller block with actual global-bank machines: base, node split/merge, return restoration, segments, gates and fixed-order child entry/recovery. One compile-time PC capacity, actual root header/sentinel setup and fixed cyclic graph; no runtime width/depth or supplied block implementation is a program parameter. Total recursive correctness and runtime recurrence remain unproved.

- `Machine/Shared50RecursiveBlockExecution.lean`: Clean physical block contracts lift to exact runs of the padded cyclic machine and its real next-table edge, with full bank endpoints and at most one additional transition. These trace rules support assembly; recursive traces remain to prove.

- `Machine/RecursiveScalarIndex.lean`: Every flat payload cell has an original heterogeneous scalar-coordinate address, for general field count and digit width; no fiber or row is omitted.

- `Machine/Shared50RecursiveNodeBoundary.lean`: Binary node entry yields the exact encoded World split bank and saved-stack availability; binary exit consumes encoded routed output and restores the parent transpose with symbolic linear-volume bounds.

- `Machine/Shared50RecursiveNodePieces.lean`: Actual segment/gate/child array fold equals the exact node networkData on every cell, assuming only the explicit selected-coordinate ChildSpec. Physical exit accepts this fold output and returns parent transpose. Establishing ChildSpec from actual recursive machine execution remains open.

- `Machine/Shared50RecursiveRoot.lean`: Actual root header/sentinel initialization equals the existing savedStacks call frame on the global bank. Charged setup, preserved free suffixes and linear-volume setup bound; its root composition rule still requires the graph body.

- `Machine/Shared50RecursiveBaseExecution.lean`: Complete width-one execution of the actual fixed root program: root frame setup, guard, digit interchange, occupied-header restoration, real PC decode/return edge and final halt. Exact transformed stream, all spectator banks/stacks restored and fixed-coefficient linear logical-volume runtime; recursive widths remain open.

- `Machine/Shared50RecursiveCallSemantics.lean`: Actual parking/movement leaves all original World work tapes blank and the active word on common IO; header setup has the exact canonical child bank. Source replacement commutes with entry into IO replacement, array support is derived, and the payload stack preserves an unbounded blank suffix.

- `Machine/Shared50RecursiveCallRecovery.lean`: Actual initialized count/move/reverse-parking/cleanup recovery consumes the returned IO word and restores precisely the parent array with one selected World stream updated. Source support and free intervals follow from canonical arrays and blank suffix; binary child outputs preserve all World bit encodings.

- `Machine/Shared50RecursiveChildPermutation.lean`: Full transpose of the actual cross-child layout equals exactly the selected parent H_i/D_j swap. Literal serialized input/return words match, spectators are preserved, and binary selected-coordinate ChildSpec follows, independently of row-split divisor.

- `Machine/Shared50RecursiveDepth.lean`: Positive power-width descriptors with W^depth dividing rows remain valid after exactly one split and divisor-one child preparation. Child width/depth decrease, exact parent volume/W and old/current header bounds are proved.

- `Machine/Shared50RecursiveBinaryInvariant.lean`: Binary World arrays and blank common IO are preserved by every actual piece array operation and literal schedule, using the exact selected child contract and coverage of every flat coordinate. Dirty work roles may hold arbitrary bits.

- `Machine/Shared50RecursiveCallReady.lean`: Actual call entry constructs child headers and canonical binary source bank, preserving available payload/node/descriptor/PC stack suffixes and blank scalar-view workspace. All child induction input invariants follow from parent readiness and physical entry.

- `Machine/Shared50RecursivePieceExecution.lean`: Actual segment/gate graph transitions and call entry-child-return-recovery composition execute every remaining literal schedule piece. Binary invariant-aware suffix induction charges all graph edges, exact s child calls and fixed linear logical-volume overhead; each recursive child trace remains the induction premise.

- `Machine/Shared50RecursiveBasePermutation.lean`: Width-one digit interchange equals full parent H/D transpose at every flat cell, and canonical source-bank IO updates match the exact recursive output serialization.

- `Machine/Shared50RecursiveBudget.lean`: Natural-valued recursion budget charges fixed base/node work and exactly s child budgets at logical volume parent/W. Occupied-header cleanup/return costs are bounded from actual word lengths; proving execution meets the recursive budget remains separate.

- `Machine/Shared50RecursiveInductionBase.lean`: The actual fixed graph executes canonical binary width-one input to the complete transpose and decoded caller address, preserving all stacks/spectators and meeting the same logical-volume budget used by the recursive induction.

- `Machine/Shared50RecursiveNodeExecution.lean`: Actual graph guard, physical node split, literal binary schedule, permuted merge, ancestor-header restoration and decoded return compose with exact canonical transpose output and fully charged runtime. Only the actual recursive child traces remain premises for depth induction.

- `Machine/Shared50RecursiveBudgetBound.lean`: The concrete natural-valued budget is bounded uniformly by logical volume times width to the certified exponent 1−296/10^11, including natural floor division and all fixed coefficients. This proves the analytic bound without assuming a runtime recurrence; actual recursive execution must still meet the budget.

- `Machine/Shared50RecursiveBudgetAssembly.lean`: Symbolic arithmetic absorbs all actual node controller joins, header-return costs and literal-schedule overhead into the natural recursive budget, using only positive logical volume and reduced role volume bounded by parent volume. Raw fixed coefficients avoid expanding enormous closed constants during proof checking.

- `Machine/Shared50RecursiveCallInductionBridge.lean`: Canonical binary child input and full-transpose return banks equal the actual parked call and recovery endpoints. Exact payload/node/descriptor/PC readiness bridges permit recursive induction without an assumed child trace.

- `Machine/Shared50RecursiveInduction.lean`: Depth induction proves actual fixed cyclic graph termination, exact binary full-chunk transpose, physically decoded caller return, all restored bank/stack endpoints and the natural recursive runtime budget. Every literal child trace is derived from the induction hypothesis; no abstract execution oracle remains.

- `Machine/Shared50RecursiveRootExecution.lean`: One concrete fixed root program physically sets up its sentinel and headers, executes the proved recursion, restores all stacks/spectators and genuinely halts with exact binary chunk transpose. Its actual steps obey one uniform positive constant times logical volume times width to exponent 1−296/10^11, for power widths and recursively divisible rows.

- `Machine/ArbitraryWidthPieceBudget.lean`: The sum of the completed fixed root machine budgets over the literal base-125000 piece list obeys one uniform positive constant times logical volume times full width to the certified exponent. This proves the actual call-budget sum; physical wrapper preparation, padding and tape composition must still be charged.

- `Machine/ArbitraryWidthPieces.lean`: The literal base-125000 power-piece list covers every chunk width, with certified depth/count/offset bounds. Consecutive piece swaps compose to the exact numerical full-address swap; each slice descriptor preserves total logical volume and satisfies the proved power-width Shape on common divisible rows. Its finite cost sum equals the manuscript digit-weighted sum. Physical padding and paid slice/list construction remain separate.

- `Machine/ArbitraryWidthSliceTranspose.lean`: Literal slice descriptors and serialized words implement exactly the selected MSB digit-window exchange, preserving all original seven-factor spectators and binary encodings. Generic interval-rank decomposition handles arbitrary offsets and lengths. This supplies the semantic interface for calls to the completed power-width machine; paid view construction remains open.

- `Machine/RecursiveRowPadding.lean`: Flat prefix/row/suffix zero extension and cropping are exact inverses on retained rows and commute with arbitrary within-row permutations. The original descriptor chunk transpose is exactly such a permutation, so padding/interchange/cropping yields the full original transpose. Padded logical volume is bounded by the row enlargement factor. Physical movement and generated controls remain separate.

- `Machine/BoundedProductDescriptor.lean`: One fixed forty-state six-tape machine generates a canonical binary product from bounded possibly noncanonical outer counts. All workspace markers are physically initialized and erased; original inputs remain exact and cost is at most 53 times the bounded product plus 28.

- `Machine/RowPaddingSpanCounts.lean`: One fixed nine-tape machine preserves canonical row, padded-row and suffix-length inputs and actually constructs canonical valid-span R*L and zero-padding-span (R′−R)*L, erasing subtraction and arithmetic scratch completely. Runtime is at most 112*(R′*L)+83; constructing the rounded row count R′ itself is separate.

- `Machine/CountedRawFill.lean`: Actual delimiter-free filling of an exact finite interval from an immutable binary span descriptor. Every data write, countdown setup and clock reset is charged; surrounding cells and supplied descriptor remain exact.

- `Machine/CountedRawMove.lean`: Actual delimiter-free destructive word transfer with source erasure from an immutable binary span descriptor. Exact arbitrary-symbol output, surrounding-cell preservation and all paid countdown/clock cleanup; data heads advance by precisely the span.

- `Machine/CountedPairPosition.lean`: Fixed counted motion of two payload heads with exact whole-tape preservation, reusable supplied span descriptor and charged clock preparation/reset. Supports restoring both row-padding payload origins.

- `Machine/RowPaddingBlock.lean`: Physical valid-span transfer followed by binary-zero padding, and inverse valid-span transfer plus physical padding erasure. Original span descriptors are retained and every primitive/join is paid.

- `Machine/RowPaddingStream.lean`: Actual counted prefix loop streams every original row group to its zero-padded group, or physically crops and erases padded groups. Exact flattened words and supplied span/prefix controls, with all group-loop work charged.

- `Machine/RowPaddingReset.lean`: Physical counted rewind restores both payload origins after grouped padding or cropping while preserving every tape cell and immutable span controls.

- `Machine/RowPaddingExecution.lean`: One fixed seven-tape padding or cropping program includes marker setup, every grouped transfer/fill/erase, counted origin restoration and final clock erasure. Exact full-tape endpoints with both clocks blank/head zero and linear cost at most 148*P*(N+M)+53; canonical span/count descriptors are explicit inputs.

- `Machine/RowPaddingWord.lean`: Flat descriptor arrays serialize to exactly the physical per-prefix row words and appended binary-zero spans. Padding/cropping word identities and the full transpose-after-padding output bridge connect the semantic row wrapper to the actual streamed data layout.

- `Machine/FixedBasePowerStep.lean`: One fixed binary-descriptor multiplication step retains the fixed base, replaces the old power with the canonical product, physically erases both old value and temporary product and restores every workspace tape. Cost is at most 110 times the new positive value.

- `Machine/FixedBasePowerDescriptor.lean`: One fixed eight-tape program computes B^k from a retained canonical runtime exponent for a fixed base B≥2. It physically writes the base and initial one, executes all k multiplication steps, and erases the base and countdown workspace. Exact canonical output and uniform fixed-base constant times B^k runtime.

- `Machine/RecursiveRowDivisor.lean`: Specializes the actual fixed-base power program to the fixed Shared50 World count W. The runtime depth produces canonical W^k on the unchanged finite alphabet, with preserved exponent and blank workspace; a dominating row range absorbs the complete construction cost linearly.

- `Machine/RoundedRowDescriptor.lean`: One fixed fifteen-tape program physically computes the least multiple of a positive canonical divisor that encloses a positive canonical row count. Original inputs are retained, the output is canonical and all temporary tapes are erased. Exact ceiling formula, divisibility, minimality and less-than-twice-row bound when D≤R; runtime is at most 4096 times the rounded row count.

- `Machine/RowPaddingConstructed.lean`: One fixed twelve-tape padding or cropping program generates both span descriptors from retained canonical prefix, row, rounded-row and suffix dimensions, executes the physical grouped scan and erases every generated counter. Exact serialized array endpoints, restored payload origins and entirely blank workspace; complete runtime at most 413 times padded volume.

- `Machine/SliceExponentPowers.lean`: One fixed nine-tape machine physically subtracts selected offset and width from the parent exponent, constructs both required fixed-radix powers, and erases temporary differences. Original exponent, offset and width are retained; complete runtime is linear in a dominating volume.

- `Machine/ArbitrarySliceDimensions.lean`: One fixed seventeen-tape machine constructs all three canonical arbitrary-window slice dimensions from six original headers and runtime offset/width controls. Original inputs are retained, every power/difference/intermediate product is erased, and the exact slice dimensions cost at most 700 times parent volume. Physical header installation is separate.

- `Machine/ArbitrarySliceHeaders.lean`: One fixed eighteen-tape wrapper physically saves six parent headers, constructs runtime slice dimensions, replaces occupied fields, and erases generated descriptors. Paid restoration returns the exact original headers and older frame stack. Entry costs at most 900 times volume and return at most 128 times volume; offset/width controls and all scratch endpoints are exact.

- `Machine/ArbitraryWidthSchedule.lean`: The literal power-piece schedule has computed offsets and depths and composes to the exact full chunk transpose. Each slice has an actual fixed recursive root execution contract with certified budget and exact serialized endpoints. Installed slice headers are an explicit premise; runtime schedule construction and whole driver remain open.

- `Machine/ArbitraryWidthHighRows.lean`: Computable least high-digit count Nat.clog(q*q)D exactly equals the manuscript ceiling when D=W^k. Integer-power domination, first-stop uniqueness, previous-power minimality and less-than-q-squared overshoot are proved, including the zero-exponent edge case. The physical selection loop is separate.

- `Machine/BinaryDescriptorCompare.lean`: One fixed three-tape twelve-state comparison program scans two immutable marked binary operands, writes their exact less-than flag and physically rewinds both heads. Complete cost is max width plus both operand widths plus eleven; a paid flag-clear primitive restores blank result workspace.

- `Machine/BinaryDescriptorIncrement.lean`: A fixed widened-alphabet one-tape three-state incrementer retains the marked descriptor representation, grows its highest bit as needed and returns to head one. Exact value increment, canonicality preservation and cost twice carry length, bounded by twice input width plus two.

- `Machine/RadixRangePadding.lean`: Numerical enlargement of both chunk ranges is exactly two grouped row extensions with literal flat-word regrouping. Reverse grouped crops equal direct restriction; padding, padded chunk transpose and cropping yield exactly the original chunk transpose. The enlarged volume is bounded by the square of the range factor. Whole physical two-range preparation and runtime dimension synthesis remain separate.

- `Machine/SliceHeaderPlacement.lean`: Injective generic placement shares the six actual root header tapes and appends exactly twelve offset/width/work/frame tapes. Exact active-bank and complement preservation lemmas avoid enumerating the large compiled recursive tape bank.

- `Machine/ArbitrarySliceCall.lean`: One fixed complete prepare/root/restore program executes any runtime selected power-width window. Actual slice dimensions and occupied headers are constructed, the fixed recursive root program executes, and original headers, frame stack, controls and spectators are restored. Exact window output and runtime rootBudget plus 1030 times parent volume; only canonical input, stack availability and the proved width/row shape are required.

- `Machine/FixedBasePowerUntilBound.lean`: Least stopping exponent and repeated descriptor-scan bounds for a fixed-base growing-power loop. Canonical threshold widths and all repeated comparisons are absorbed into a fixed-base constant times the final power.

- `Machine/FixedBasePowerUntilRange.lean`: The actual least-power selector has runtime linear in its positive input threshold, using strict less-than-one-base overshoot of the final power. Exact paired-digit exponent and range identities connect its output to the manuscript high-row selector.

- `Machine/FixedBasePowerUntil.lean`: One fixed nine-tape program physically initializes base/current/exponent, repeatedly compares and multiplies while below a retained runtime threshold, increments its exponent and clears each flag. It genuinely terminates at Nat.clog B D, retains canonical final power and exponent, clears all other workspace and costs at most a fixed-base constant times the final power.

- `Machine/ArbitraryWidthHighLayout.lean`: Literal finite row-major address bijections implement the manuscript high-field exchange/join and reverse separation. Exact numeric index/volume identities identify joined high digits as rows. The low recursive transpose, even with row padding and cropping, returns the original full-width transpose after separation. Physical high-field movement remains separate.

- `Machine/BinaryDescriptorAdvance.lean`: One fixed three-tape program physically advances a marked binary offset by a retained runtime count through repeated growing increments. It initializes and erases its work clock and restores the immutable count. Exact offset addition, canonicality and amortized cost 10 times count plus twice offset width plus seven times count width plus 28.

- `Machine/RadixDigitMoveRows.lean`: Moving one fixed-radix digit across an arbitrary spectator block is exactly a cyclic split into long rows followed by a cyclic merge of singleton rows. Literal source/output words and exact equal role words connect the two actual streaming primitives; head positioning and complete physical composition remain separate.

- `Machine/BinaryCanonicalData.lean`: Canonical little-endian binary descriptors have injective numerical value; a canonical zero descriptor is empty. This identifies actual normalized machine outputs with exact deterministic digit words.

- `Machine/BinaryDescriptorDivMod.lean`: One fixed fourteen-tape machine retains binary operands and returns both canonical quotient and remainder, restoring operand heads and clearing all arithmetic and tracking tapes. Exact division/modulus values and linear input-value cost for a fixed divisor.

- `Machine/ArbitraryWidthPieceCounter.lean`: A fixed-base extraction stage physically initializes the divisor, obtains canonical quotient/remainder, clears the divisor and replaces the consumed remaining width with its quotient. The remainder is the actual next base digit; every transition and cleanup is charged linearly.

- `Machine/ArbitraryWidthPieceLoop.lean`: One fixed finite outer loop repeatedly extracts actual runtime base digits until the canonical remaining width is zero, then clears all fourteen control tapes. Deterministic emitted digits match the manuscript partition. A fixed consume continuation must still implement repeated slice calls and depth/width/offset updates; no concrete whole piece driver is claimed.

- `Machine/SliceOffsetAdvance.lean`: Fixed placement advances the runtime offset in the existing twelve-tape slice tail, using its blank arithmetic work tape as the paid clock. The complete recursive root bank, saved frame and all other controls are exact spectators.

- `Machine/ArbitrarySliceStepBudget.lean`: The complete paid slice step is bounded by rootBudget plus 1087 times volume under explicit width bounds. This includes header preparation/restoration and physical offset updates; summing its literal power-piece budgets preserves the exact certified width exponent with a positive fixed constant.

- `Machine/ArbitrarySliceStep.lean`: One fixed program composes paid slice-header preparation, actual recursive root execution, original-header restoration and physical runtime offset advancement. Exact selected-window output and next offset, with every join, scan, carry and cleanup included in the cost.

- `Machine/ArbitraryWidthLevelAdvance.lean`: One fixed seven-tape program increments the canonical recursion-depth descriptor and multiplies the canonical selected width by the fixed base. Setup physically initializes the base, width one and depth zero; separate base or full cleanup is paid. Arbitrary framed data/offset controls are preserved; level advancement costs at most 120 times the new width.

- `Machine/RangePaddingDimensions.lean`: One fixed seventeen-tape constructor retains canonical prefix/chunk/gap/suffix/enlarged-range inputs and generates PN, PNG, GM and GMB by four actual product calls. All arithmetic workspace is erased. Separate paid cleanup clears the four outputs while preserving arbitrary payloads; both costs are linear in a dominating padded volume.

- `Machine/RowCropAny.lean`: The actual constructed row-cropping program works on arbitrary discarded rows, including nonzero tails. Exact arbitrary-array restriction, generated span-count cleanup, restored payload origins and linear padded-volume runtime extend the physical crop contract beyond zero-padded inputs.

- `Machine/RadixRangePaddingExecution.lean`: Complete fixed seventeen-tape padding and cropping programs generate their own grouped dimensions, execute both coordinate scans and erase every derived descriptor. Exact two-chunk pad and arbitrary crop endpoints with clean payload/workspace; each costs at most 1200 times padded volume. After the padded transpose the actual crop returns the original transpose. Runtime binary/radix range synthesis and composition with the interchange remain separate.

- `Machine/ArbitrarySliceRepeat.lean`: One fixed counted controller executes the actual paid slice-step program as many times as specified by a runtime base digit. Every slice trace is derived from the completed recursive root proof; offsets advance physically and exact repeated window swaps compose in order. Clock setup and cleanup are paid; optional consume also clears the digit descriptor. Certified digit-weighted budgets include all loop and erase costs. Whole outer dispatcher composition with level updates remains separate.

- `Machine/BinaryRadixRangePrepare.lean`: One fixed nineteen-tape program constructs both numerical ranges and the least radix exponent from the sole binary width, then physically pads both chunk coordinates. It retains original prefix/gap/suffix/width headers and exact generated metadata, with all private workspace blank. The inverse arbitrary-content crop clears all generated metadata and returns the exact original transpose after a padded transpose. Both bounds are fixed-radix constants times original volume; the intervening interchange must still be composed.

- `Machine/RadixRangeDescriptors.lean`: One fixed twelve-tape program constructs the binary chunk range 2^u, then the least enclosing fixed-radix power and its runtime exponent from the sole canonical binary width. The original width is retained, all scratch is cleared, and exact canonical outputs satisfy the range overshoot and exponent bounds. Construction and descriptor cleanup cost linearly in 2^u. Composition with the physical numerical padding scans remains separate.

- `Machine/RadixDigitMoveCore.lean`: Actual cyclic split, rewind, merge and rewind redistributes compatible literal row plans, with exact payload and role-bank endpoints.

- `Machine/RadixDigitMoveInitialized.lean`: Physical initialization of two runtime clocks and full erasure of roles, clocks and trackers around actual redistribution; four original descriptors retained.

- `Machine/RadixDigitMoveCounts.lean`: Construct and erase digit-movement dimensions from sole prefix and spectator lengths, including the constant one and prefix-times-spectator count; linear-volume cost.

- `Machine/RadixDigitMovePrepared.lean`: Exact forward and inverse fixed-radix digit permutation for prepared canonical controls, with physically rewound payload and erased private storage.

- `Machine/RadixDigitMovePlacement.lean`: Fixed injective placements compose count synthesis and redistribution while preserving original descriptors and spectator tapes.

- `Machine/RadixDigitMoveExecution.lean`: Complete suffix-one digit movement from sole canonical prefix/spectator descriptors and arbitrary payload. All generated controls and private tapes are erased, with fixed-radix linear-volume forward/inverse bounds.

- `Machine/RadixDigitMoveBlockRows.lean`: Literal digit exchange across a spectator block with an arbitrary trailing block. Exact split/merge word identity, role compatibility and mutually inverse forward/backward array permutations.

- `Machine/RadixDigitMoveBlockCounts.lean`: Construct spectator-times-suffix and prefix-times-spectator descriptors from the three original positive canonical lengths. All arithmetic workspace is cleared; construction and cleanup have linear-volume bounds.

- `Machine/RadixDigitMoveBlockPrepared.lean`: Prepared arbitrary-suffix digit movement and its actual inverse, with exact serialized endpoints, restored payload origin, erased role storage and paid linear-volume cost.

- `Machine/RadixDigitMoveBlockPlacement.lean`: Fixed tape placements share retained shape controls between block-dimension construction and the redistribution machine, preserving unrelated payload and descriptor tapes.

- `Machine/RadixDigitMoveBlockExecution.lean`: One fixed machine and its inverse exchange a radix digit across arbitrary spectator and suffix blocks, from sole prefix/spectator/suffix controls. Every derived count, clock, tracker and role tape is erased; payload is rewound. Tape count is 2Q+18 and runtime is at most (1516Q+11403) times volume. The repeated high-field joining/separation loop remains separate.

- `Machine/ArbitraryWidthHighPrepare.lean`: One fixed nineteen-tape program constructs k=clog_m(e), D=W^k, rho=clog_(q²)(D), R=q^(2rho) and the rounded multiple Rprime from the sole positive canonical runtime width. All intermediate workspace and the unused envelope are erased. Exact manuscript ceiling, divisibility and overshoot formulas are proved; construction costs constant(q) times rounded rows. Paid cleanup erases all five derived descriptors and retains only the original width.

- `Machine/FixedBaseDescriptorQuotient.lean`: One fixed fourteen-tape program replaces its sole canonical runtime descriptor by the canonical quotient by a compiled fixed base and physically erases the remainder. All thirteen private tapes are blank again. Exact divisible suffix shrinking and a fixed-base linear-input-value bound support the repeated high-digit movement controller.

- `Machine/ArbitraryWidthConsumePlacement.lean`: Injective placement of the actual runtime-counted slice consume program into the fourteen-tape digit dispatcher prefix and shared slice bank. The emitted digit and clock are shared physically while all other dispatcher controls and auxiliary tapes are preserved.

- `Machine/ArbitraryWidthLevelPlacement.lean`: Actual depth and power-width advance shares the slice-width descriptor while preserving the recursive bank, offset, original parent headers and remaining-width controls. Fixed placements have exact clean framed endpoints.

- `Machine/ArbitraryWidthPieceConsume.lean`: The actual continuation first executes the digit-counted paid slice calls, then physically advances recursion depth and power width. Exact repeated-window output, digit erasure, offset increment and clean level update are derived without a callback execution assumption. Certified cost includes both programs and their composition; whole dispatcher initialization, invariant and final cleanup remain separate.

- `Machine/ArbitraryWidthPiecePrefix.lean`: The runtime outer dispatcher has an exact base-digit prefix schedule. Cumulative offset plus the remaining quotient contribution equals original width, proving every step fits. Literal repeated-slice images compose at successive levels and the final image is the full transpose, including zero width. Selected levels satisfy the common padded-row divisor bound.

- `Machine/ArbitraryWidthHighBudget.lean`: The actual high-digit selector satisfies an explicit constant times every positive width exponent, for all positive widths. The logarithmic construction cost and every fixed-coefficient per-digit movement therefore preserve the certified exponent rather than weakening it to a linear-width bound.

- `Machine/ArbitraryWidthHighExchangeControls.lean`: Actual setup writes zero offset, unit slice width and zero recursion depth, and copies the retained runtime high-digit count into the slice dispatcher. Paid cleanup erases generated offset, width and depth; count source is retained.

- `Machine/ArbitraryWidthHighExchangePlacement.lean`: Injective tape placement shares high-exchange controls with the complete recursive slice bank. Exact framed initialization and cleanup preserve every original parent descriptor, stack and payload spectator.

- `Machine/ArbitraryWidthHighExchangeSemantics.lean`: Exact numeric high-prefix swap agrees with the literal width-rho slice permutation on every serialized address, including unchanged low digits and gap fields.

- `Machine/ArbitraryWidthHighExchange.lean`: One actual fixed program initializes controls, executes rho real depth-zero slice calls and clears every created descriptor. Sole original canonical headers and retained rho suffice; exact high-field interchange and constant times (rho+1) times parent volume include all root calls, offset advances and cleanup. Joining and separation loops remain distinct.

- `Machine/ArbitraryWidthHighGuard.lean`: The concrete integer depth and high-row selectors equal the manuscript real ceilings. High depth is positive beyond unit width and eventually below the original width, proving a fixed bounded set suffices for the elementary fallback. This proves the branch arithmetic, not the fallback machine.

- `Machine/ArbitraryWidthHighMetadataBudget.lean`: The actual rounded high-row count is uniformly bounded by a fixed multiple of the original array volume, for every width. The large-width branch uses the selected high-depth guard; the bounded fallback uses monotonicity of the runtime divisor. Thus constructing row metadata before branch selection has a paid linear-volume bound on both branches.

- `Machine/ArbitraryWidthElementary.lean`: One actual fixed program takes sole original canonical parent headers and a completely blank sixteen-tape private bank. It copies the width header, executes all corresponding unit-digit swaps with the proved recursive base machine, and erases the copy. Exact full transpose, restored headers/stacks and complete private cleanup hold even at zero width. Every fixed bounded set of positive widths has linear-volume runtime and therefore satisfies the unchanged positive width exponent.

- `Machine/ArbitraryWidthLevelLifecycle.lean`: Physical setup initializes base, unit power width and zero depth on the shared slice-control bank. Final cleanup clears all six level controls while preserving arbitrary parent payload, original shape descriptors and caller tapes.

- `Machine/ArbitraryWidthPieceExecution.lean`: One concrete fixed outer program repeatedly extracts actual runtime base digits, consumes them with real repeated slices, advances depth and power width, and follows the proved prefix invariant. Its complete dispatcher endpoint is the full transpose, with physically advanced controls. No callback execution oracle is supplied; exact accumulated costs are paid.

- `Machine/ArbitraryWidthPieceSetup.lean`: From sole original parent headers and blank private controls, physically copy the original width into the remaining counter, construct the zero offset, and initialize the fixed base/depth/power controls. Every copied or constructed descriptor is charged.

- `Machine/ArbitraryWidthPieceCleanup.lean`: Complete physical final erasure of remaining width, final offset and all depth/power/base controls. Original parent headers, array, stacks and framed caller storage survive exactly.

- `Machine/ArbitraryWidthPieceRun.lean`: The actual fixed dispatcher composes sole-header initialization, every real extracted-digit slice call, exact full transpose and final control cleanup. All fourteen dispatcher, eleven slice-work and six level private controls return blank, while original metadata and caller banks are restored. A complete paid natural cost expression is proved; converting its accumulated cost to the certified exponent remains separate.

- `Machine/PlacedDescriptorConstruction.lean`: Exact single-output framing places power and product constructors into an arbitrary larger bank. Every tape and head outside the generated output is retained literally; no supplied runtime result is assumed.

- `Machine/RadixHighBlockJoinBank.lean`: Fixed shared bank for high-block joining and separation, retaining source, spectator size, original prefix/suffix and outer count. Mutable prefix/suffix/base and thirteen arithmetic tapes have exact descriptor and blank-workspace layouts.

- `Machine/RadixHighBlockJoinSetup.lean`: Fixed injective placements route the retained runtime exponent into actual power construction and original lengths into product construction, sharing the movement bank. Exact descriptor updates and blank-workspace views preserve every outer tape.

- `Machine/RadixHighBlockJoinInitialize.lean`: Complete actual sole-original-header setup for both ordered high-block movement directions. Physically copy one original length, write the fixed radix, construct its runtime power and enlarged length, then erase the intermediate power. Original payload, shape, count and clock are retained; a fixed-radix linear-volume bound pays every step.

- `Machine/RadixHighBlockJoinCleanup.lean`: Actual cleanup erases mutable prefix, suffix and radix descriptors after either direction, preserving payload and sole original shape/count/clock. Any canonical terminal working lengths bounded by volume satisfy the explicit fixed-radix linear cleanup cost.

- `Machine/ScanRight.lean`: One fixed single-tape sentinel scan preserves all symbols and charges exactly one transition per traversed cell, at arbitrary integer head positions.

- `Machine/BinaryDescriptorNormalize.lean`: Physically scan a marked descriptor from head one to its end, trim high zero bits and return to head one. Exact canonical output of unchanged value, including zero, with all scans and rewinds paid.

- `Machine/BinaryDescriptorDifference.lean`: One fixed three-tape finite-alphabet program subtracts arbitrary-width immutable marked operands and physically normalizes the result. Both original words and heads are preserved, the output is canonical at head one, and no padded operands or derived result are supplied. Exact runtime is bounded by six times the larger descriptor length plus21, or six times the original minuend value plus27 for canonical inputs.

- `Machine/ArbitraryWidthPieceCost.lean`: The complete actual piece dispatcher runtime is bounded by the fully paid digit-weighted slice budgets plus explicit physical control overhead. Its sole-header setup, all runtime digit steps and complete cleanup satisfy a fixed positive coefficient times volume times positive width to the unchanged certified exponent; a width-plus-one version includes zero. No callback execution or cost oracle is assumed.

- `Machine/RadixHighBlockJoinSemantics.lean`: Successive single-radix movements join an entire runtime high block in its original digit order. Exact indexed cells and equality to the whole block transpose are proved for arbitrary payload symbols and all spectators.

- `Machine/ArbitraryWidthHighMovementSemantics.lean`: The actual high-prefix exchange followed by ordered joining has exactly the manuscript joined-row layout, with literal prefix/spectator/suffix dimensions and explicit finite-index casts. Separation agrees with the return layout, and exchange, join, low transpose and separation compose to the exact original full transpose.

- `Machine/ArbitraryWidthHighBranch.lean`: One fixed fifteen-state finite controller physically compares retained high depth with width, tests positive canonical high depth, selects the exact manuscript high or fallback branch and erases its comparison flag. Both operands and every head are preserved, with exact selected terminal state and length/value/volume runtime bounds.

- `Machine/ArbitraryWidthHighBranchPlacement.lean`: Injective shared-bank placement of the actual high-width selector takes only literal canonical descriptor, head and blank flag premises. It proves the exact selected state, genuine halt and complete tape/head preservation with no supplied comparison result or active-view oracle.

- `Machine/RadixHighBlockJoinPlacement.lean`: Exact shared-bank views place the existing digit movement machine and its arithmetic tail into the ordered high-block body while preserving all other tapes.

- `Machine/RadixHighBlockJoinArithmetic.lean`: Actual prefix growth and suffix shrinking operate on the shared movement bank, preserving arbitrary payload, original headers, spectators and all framed arithmetic storage.

- `Machine/RadixHighBlockJoinBody.lean`: One fixed body physically shrinks the working suffix, executes the literal ordered radix digit movement, and grows the prefix. Both forward and inverse directions have exact serialized endpoints and fixed-radix linear-volume cost.

- `Machine/RadixHighBlockJoinLoop.lean`: A concrete runtime-counted loop executes every high digit in order from a canonical retained exponent. Its computed trace is proved step by step from the actual body; the final payload is exactly the whole-block ordered join, with paid clocks and preserved inputs.

- `Machine/RadixHighBlockJoinRun.lean`: The complete actual forward high-block join starts from sole original shape/count descriptors and blank private storage. It constructs movement controls, executes the real counted loop and erases every private descriptor. Exact ordered payload output and fixed-coefficient volume-times-count bound are proved; the actual high-depth selector retains every positive target width exponent.

- `Machine/RadixHighBlockSeparateSemantics.lean`: Repeated trailing-digit movement separates the joined high block in exact original digit order. Its recursive array is proved equal to the literal whole-block separation, preserving every spectator and arbitrary payload symbol.

- `Machine/RadixHighBlockSeparateLoop.lean`: The actual retained-exponent counted loop executes every inverse high-digit movement, with a computed step trace and exact whole-block separated endpoint. All clocks and shared arithmetic work are paid and restored; no callback execution oracle is supplied.

- `Machine/RadixHighBlockSeparateRun.lean`: The complete inverse high-block separator constructs its movement controls from sole original shape/count headers, executes the actual counted loop and erases every private descriptor. The exact whole-block move and fixed-coefficient volume-times-count bound are proved, preserving every positive target width exponent for the actual runtime high-depth selector.

- `Machine/ArbitraryWidthHighDimensions.lean`: An actual seventeen-tape constructor takes only retained canonical P/G/B/width/high-depth headers and blank private storage. It physically computes low width by normalized immutable subtraction, both radix powers and all three high-block movement dimensions, preserving original inputs and restoring all six arithmetic tapes. Exact generated values and a fixed-radix linear original-volume runtime bound are proved.

- `Machine/ArbitraryWidthHighDimensionsCleanup.lean`: One actual finite list-erasure program clears all six generated high-layout descriptors and restores their heads to zero while retaining the original five headers and all arithmetic storage. Exact constructor-output to sole-header-input cleanup is proved, with runtime at most54 times the original positive volume.

- `Machine/RowPaddingConstructedAlphabet.lean`: The actual twelve-tape row padding/cropping machines are adapted by exact finite-alphabet simulation to the recursive interchange alphabet. Literal larger-alphabet bank endpoints preserve canonical dimensions, erase consumed source words and write exact zero-padded or cropped arrays. Both general encoded-symbol and literal bit-array contracts retain the complete413-times-padded-volume bound, including all descriptor construction and erasure.

- `Machine/ArbitraryWidthJoinedHeaders.lean`: One actual twelve-tape program copies retained prefix, rounded rows and spectator headers, writes the unit before-H header and computes the low width by immutable canonical subtraction. It produces all six literal padded-joined root headers, preserves all originals and proves their semantic Headers predicate; paid initialization costs at most83 times a dominating volume.

- `Machine/ArbitraryWidthJoinedHeadersCleanup.lean`: The actual six-header cleanup erases every generated padded-joined root descriptor and returns all target heads to zero while retaining the original six headers. Exact output-to-input restoration and a54-times-dominating-volume cost are proved.

- `Machine/ArbitraryWidthHighPaddingSuffix.lean`: The actual product constructor operates directly on retained generated high-movement lengths and produces the exact joined row suffix, preserving originals and restoring arithmetic scratch. Literal rowLength equality and original/padded-volume bounds are proved; construction and subsequent erasure cost at most81 and8 times the suffix length.

- `Machine/ArbitraryWidthHighPrefix.lean`: The three original prefix factors are physically folded into one canonical descriptor by two real products followed by intermediate erasure on eight tapes. All originals and scratch are retained/restored; construction costs at most174 times a dominating volume and final cleanup8 times it. Exact folded volume and address identities cover arbitrary original row/prefix factorizations.

- `Machine/ArbitraryWidthHighExchangeShared.lean`: The actual complete high-prefix exchange is placed on an arbitrary caller source through the true recursive I/O slot. It preserves every other caller tape and the private recursive root/header/stack/control bank, with the exact high-exchanged binary word and its fully paid original-volume runtime. No callback execution trace is supplied.

- `Machine/ArbitraryWidthHighMovementPlacement.lean`: Actual complete high-block joining and separation run through one physically shared source tape in an arbitrary caller bank. All other caller tapes and heads are preserved, the exact ordered payload is returned and the private movement bank is fully restored; runtime uses the actual sole-header Run programs.

- `Machine/ArbitraryWidthHighPaddedBudget.lean`: The exact runtime high-row rounding increases original payload volume by at most two. The selected depth automatically supplies the actual low dispatcher width/divisibility conditions, so its physical execution requires no supplied depth or row-divisor oracle. Its complete runtime, including initialization and cleanup, satisfies twice its certified coefficient times original volume times original width to the unchanged exponent.

- `Machine/ArbitraryWidthHighFoldSemantics.lean`: Literal finite-index folding combines all original prefix and row factors without changing any serialized cell. The full transpose of any valid original row-divisor view equals the folded row-one transpose, with exact source-word and binary-encoding identities.

- `Machine/ArbitraryWidthHighExchangeJoinEncoding.lean`: The recursive I/O source encoding is exactly the literal larger-alphabet word consumed by ordered movement. High exchange commutes with bit encoding, and the actual ordered join word is exactly the manuscript exchangeJoin view.

- `Machine/ArbitraryWidthHighSeparateShared.lean`: The actual inverse separator operates on the joined binary I/O source through one physically shared caller tape. Its output is exactly the manuscript separateExchange word, all other caller and private-bank cells/heads are restored, and its complete runtime is paid against original volume and retained high-digit count.

- `Machine/ArbitraryWidthHighExchangeJoin.lean`: One actual fixed stage physically exchanges the high prefixes and joins their ordered block on the same caller source tape. Both complete private banks are restored, every other caller tape/head is retained and the output is exactly the encoded manuscript joined view. The paid coefficient-times-volume-times-count bound includes the real sequential edge; no callback execution is supplied.

- `Machine/ArbitraryWidthHighPrepareShared.lean`: Actual high-row preparation reads the original canonical caller width through one physically shared descriptor tape. It computes depth, divisor, high-digit count, rows and rounded rows into nineteen blank private tapes, retains every caller tape/head and subsequently erases the complete metadata bank. No derived metadata or execution trace is supplied.

- `Machine/ArbitraryWidthHighFoldHeaders.lean`: An actual sixteen-tape program folds the three retained original prefix factors, writes the two unit headers and copies width/spectators into six blank target root headers. All original six headers and arithmetic scratch are retained/restored. Exact folded Headers correctness and a224-times-dominating-volume setup bound are proved.

- `Machine/ArbitraryWidthHighFoldHeadersCleanup.lean`: The actual six-target root-header erasure restores the complete folded-header input bank while retaining every original descriptor and blank arithmetic tape. Exact lifecycle restoration and a54-times-dominating-volume cleanup bound are proved.

- `Machine/ArbitraryWidthPaddedPiecePlacement.lean`: The complete actual runtime piece dispatcher shares its true recursive I/O source with an arbitrary caller payload tape. Every caller tape outside the source and the entire private recursive/dispatcher/frame bank are preserved exactly.

- `Machine/ArbitraryWidthPaddedPieceArrays.lean`: Literal bit-array serialization identifies the recursive I/O source with grouped row padding and cropping at descriptor-level volumes. All finite-index casts, zero fills, row views and exact consumed-word erasure are proved.

- `Machine/ArbitraryWidthPaddedPiecePadding.lean`: Actual larger-alphabet constructed padding and swapped cropping have literal original/padded descriptor endpoints and canonical header contracts. Both data tape heads and private counters are restored, with the complete413-times-padded-volume bound in each direction.

- `Machine/ArbitraryWidthPaddedPieceRun.lean`: One actual fixed program physically pads the rows, runs the complete piece dispatcher on the shared padded data, and crops back onto the original source. Its exact unpadded full transpose, restored work/private banks and natural runtime826-times-padded-volume plus the actual dispatcher cost plus two transitions are proved.

- `Machine/ArbitraryWidthPaddedPieceShared.lean`: The actual complete pad-dispatch-crop program operates through an arbitrary caller source. It returns the exact unpadded transpose, preserves every other caller tape/head and restores its entire private padding/root/dispatcher bank without an execution callback.

- `Machine/ArbitraryWidthHighCost.lean`: The sum of fully paid exchange-join, padding, actual low dispatcher, cropping, separation, five sequential edges and any fixed linear metadata coefficient has a positive coefficient times original volume times original width to the unchanged certified exponent. Numerical assembly is separate from physical execution, which is supplied by HighRun for the body.

- `Machine/ArbitraryWidthHighRun.lean`: One actual fixed high-width body composes high-prefix exchange, ordered joining, physical row padding, the complete low-width dispatcher, physical cropping and inverse separation on the same caller source. The result is exactly the original full transpose and every private execution bank is restored. Runtime-selected depth/divisibility premises are derived internally, all five sequential edges are charged, and the actual natural runtime retains the certified exponent. Canonical derived headers are still explicit inputs; their constructors and branch/outer-wrapper assembly remain separate.

- `Machine/FixedHeaderBankCopy.lean`: One actual finite program copies a fixed family of retained canonical caller descriptors into appended blank target tapes, preserving every caller tape/head even when sources repeat. Exact target bank and fixed-family linear-volume construction and erasure costs are proved.

- `Machine/FixedHeaderSparseBankCopy.lean`: Actual header copying and cleanup are placed into fixed injective named slots of a larger private bank. All other private tapes remain blank, all caller storage is retained, repeated sources are supported, and both exact banks and linear-volume costs are proved.

- `Machine/ArbitraryWidthHighDimensionsShared.lean`: The actual shared dimension lifecycle first copies five original caller headers into a blank seventeen-tape bank, computes low width/radix powers/movement dimensions and later erases both generated and copied descriptors. Every caller tape/head is preserved; complete setup and cleanup have fixed-radix linear original-volume bounds. No preconstructed generated bank is supplied.

- `Machine/ArbitraryWidthElementaryShared.lean`: The actual elementary multiplier-width transpose fallback shares its recursive I/O source with an arbitrary caller. It physically copies the original width, performs every digit swap and erases the count, while retaining all other caller and private-bank fields. Exact full transpose, bounded-width linear cost and the certified positive-exponent budget are proved.

- `Machine/ArbitraryWidthHighBranchComposition.lean`: One actual finite-flow composition runs the physical high-width selector and jumps into the selected high or elementary branch program with its flag erased and bank restored. Exact conditional outputs, genuine halting and all selector/jump/branch costs follow from branch contracts. The actual high-depth fallback set has a fixed cutoff. Instantiating the complete original-header wrapper remains separate.

- `Machine/ArbitraryWidthHighFoldHeadersShared.lean`: Copies the six original caller descriptors into blank private storage, constructs the folded prefix and root headers, and erases the complete private bank after use. Literal caller and generated-header views and paid linear construction/cleanup bounds are proved.

- `Machine/ArbitraryWidthJoinedHeadersShared.lean`: Constructs canonical padded joined-root headers from retained caller descriptors in a wholly blank twelve-tape bank, preserving the caller and paying all copying, subtraction, unit writing and cleanup.

- `Machine/ArbitraryWidthHighDimensionsAndSuffixShared.lean`: Constructs the high movement dimensions and joined-row suffix from original caller headers in a blank seventeen-tape bank, then erases every copied and generated descriptor. Literal header values, canonicality, source slots, and linear-volume lifecycle costs are proved.

- `Machine/ArbitraryWidthExecutionPrivateHeadersCore.lean`: Defines literal blank control and stack banks and structural sparse-header identities without runtime initialization assumptions.

- `Machine/ArbitraryWidthExecutionPrivateHeadersAppend.lean`: Proves exact sparse header banks across appended private storage, with named slots and preserved blank complements.

- `Machine/ArbitraryWidthExecutionPrivateHeadersRoot.lean`: Identifies the exact seven exchange and six elementary private header slots and their sparse banks, including the retained high count.

- `Machine/ArbitraryWidthExecutionPrivateHeadersPadding.lean`: Identifies all ten actual padding and low-dispatch root header slots and proves their sparse private-bank equality.

- `Machine/ArbitraryWidthExecutionPrivateHeadersMovement.lean`: Identifies all five actual movement header slots and their literal private-bank equality. The clock contains a canonical zero marker and must be physically initialized.

- `Machine/ArbitraryWidthElementaryInitialize.lean`: Physically copies six retained caller headers into the actual elementary private bank and erases them afterward, starting and ending with wholly blank storage. Setup and cleanup cost at most sixty and fifty-four times a dominating volume.

- `Machine/ArbitraryWidthElementaryInitializedRun.lean`: Composes actual header initialization, the complete elementary transpose and private cleanup. All private storage starts and ends blank; no ready-bank or generated-header premise is supplied. Exact transpose and bounded-width linear and certified-exponent budgets include every sequential edge.

- `Machine/ArbitraryWidthHighExecutionInitialize.lean`: Physically copies seven exchange, five movement and ten padding/root descriptors from retained caller sources into three wholly blank execution banks. Repeated source slots are allowed; exact literal private banks and a two-hundred-twenty-two-times-volume setup bound are proved, including the movement clock marker.

- `Machine/ArbitraryWidthHighExecutionInitializeCleanup.lean`: Actually erases all high execution headers in reverse padding, movement and exchange order, restoring three blank private banks and retaining the arbitrary caller. The two-hundred-times-volume cleanup includes physical erasure of the canonical-zero clock marker.

- `Machine/ArbitraryWidthZeroHeaderShared.lean`: An actual fixed writer constructs the canonical-zero descriptor marker from a blank appended tape, and an actual eraser restores blank storage. Every caller tape is preserved; exact six-transition setup and four-transition cleanup are proved.

- `Machine/ArbitraryWidthHighHeaderBounds.lean`: Derives canonicality and twice-original-volume bounds for every exchange, movement and padding/root header from the semantic descriptor and runtime high-layout contracts. No separate header-size oracle is supplied.

- `Machine/ArbitraryWidthHighInitializedRun.lean`: One actual program initializes all twenty-two execution headers in blank private banks, runs the complete high-width body and physically erases every header afterward. Exact transpose and blank-bank restoration are proved without Ready or Free premises. All copying, execution, cleanup and sequential edges retain the certified exponent.

- `Machine/ArbitraryWidthHighOriginalEncoding.lean`: Proves that folding the original prefix/row factors changes no literal serialized source cell, and that the high branch output is exactly the original full transpose for any valid positive row divisor.

- `Machine/ArbitraryWidthHighCommonPrepare.lean`: Physically folds the six original caller headers and constructs runtime depth, divisor, high count, rows and rounded rows from the sole original width, starting in blank sixteen- and nineteen-tape banks. Reverse cleanup restores both blank banks, retains the original caller, and has paid linear-volume bounds.

- `Machine/ArbitraryWidthHighBranchPrepare.lean`: Physically constructs high movement dimensions and row suffix, joined padded-root headers, and the canonical-zero clock in three wholly blank banks. The reverse lifecycle erases all storage; exact banks, all sequential edges, and dominating original-volume setup and cleanup bounds are proved.

- `Machine/ArbitraryWidthHighRuntimeHeaderWiring.lean`: Defines the actual exchange, movement and padding copy-source slots across the constructed dimension, joined-root and zero-clock banks. Literal tape/head source contracts, canonical generated movement words, row-padding headers and the low-root Headers interface are proved from the real metadata constructors.

- `Machine/ArbitraryWidthHighPreparedRun.lean`: One actual high program constructs all arithmetic/joined/zero metadata from retained sources, initializes the blank execution banks, runs the complete interchange and erases both execution and metadata banks. Literal transpose, entirely blank private endpoints, and the unchanged certified exponent are proved.

- `Machine/ArbitraryWidthHighCommonHeaderWiring.lean`: Maps the actual common folded/root and row-preparation banks to exchange, movement-original and joined-original source families. All literal source tapes, canonicality, values and prefix positivity follow from the original six descriptor headers.

- `Machine/ArbitraryWidthHighCommonHighBody.lean`: Instantiates the prepared high execution using only the actual common preparation output and original descriptor headers. It returns the exact original full transpose and restores every high-private bank to blank. No supplied derived headers or execution contracts enter its correctness or certified runtime bound.

- `Machine/ArbitraryWidthHighCommonFallback.lean`: Composes actual common preparation, initialized elementary transpose and common cleanup from original headers, paying every transition and restoring all private banks. A separate zero-width execution avoids positive-width metadata preparation.

- `Machine/ArbitraryWidthHighCommonFallbackBody.lean`: Runs the actual elementary transpose after common preparation without repeating metadata setup. It preserves every common generated field and restores elementary private storage, with exact original transpose and bounded-width cost.

- `Machine/ArbitraryWidthHighFramedFallback.lean`: Places the actual original-header elementary fallback on the same complete private-bank layout as the high branch. Every unused high bank and common metadata field is preserved; the payload becomes the original full transpose and elementary storage is restored blank.

- `Machine/ArbitraryWidthHighCommonSelector.lean`: Runs the actual high/fallback comparison on constructed high-count and original-width descriptors, using a proven blank common slot for its flag. The complete bank is restored, slot separation is proved, and comparison time has a uniform linear original-volume bound even on fallback widths.

- `Machine/ArbitraryWidthHighCommonDispatch.lean`: Instantiates the actual physical selector with the complete prepared high and framed elementary programs on one bank. Only original descriptor headers and payload are assumed; the selected real branch yields the same exact original transpose and restores all branch-private storage.

- `Machine/ArbitraryWidthHighCommonDispatchCost.lean`: Proves one positive uniform coefficient for the actual selector and selected high/fallback execution at the certified width exponent. The finite fallback cutoff follows from the actual high-count selector; comparison, real branch work and the jump are all charged.

- `Machine/ArbitraryWidthOriginalZeroBranch.lean`: A real one-transition branch reads the retained canonical width header, whose scanned symbol is blank exactly at zero width. The zero branch runs the actual elementary machine on the full blank global workspace and restores every private bank. The positive body still requires concrete outer-run instantiation.

- `Machine/BinaryRadixRangePrepareAlphabet.lean`: Executes binary-to-radix range preparation and inverse cropping on the recursive alphabet through the actual alphabet lift. Literal encoded bit and descriptor banks, exact pad/transpose/crop endpoints and unchanged paid runtime are proved.

- `Machine/BinaryRadixRootHeadersShared.lean`: Physically writes a temporary canonical one, copies six recursive root headers from the prepared binary bank, and erases the temporary one. All caller storage is retained; exact root Headers, literal copy slots, and original-binary-volume setup/cleanup bounds are proved.

- `Machine/BinaryRadixRootEncoding.lean`: Identifies the numerical padded-range array with the recursive root descriptor at every serialized cell and full-transpose output. Literal bit encoding and padding zero-fill bridges eliminate any assumed payload conversion between the two actual machines.

- `Machine/BinaryAdjacentWidthInterchange.lean`: Proves exact rectangular transposition for binary widths differing by one as an equal-width transpose and one actual fixed-radix-two movement, with the inverse orientation using real unmovement first. Literal serialized endpoints and paid movement proofs cover arbitrary spectators and zero shorter width. Header construction and full composition with the equal-width wrapper remain separate.

- `Machine/ArbitraryWidthOriginalRun.lean`: One actual positive-width program constructs common metadata from the original six descriptor fields, executes the physical selector and selected complete high/fallback branch, and erases all common and branch-private storage. Exact original transpose and a positive uniform coefficient at the certified width exponent are proved without derived metadata or execution callbacks.

- `Machine/ArbitraryWidthOriginalTotalRun.lean`: Instantiates the actual zero-width read with the complete positive-width original run. The fixed program handles every width from only original canonical headers and payload, produces the exact full transpose and restores all private banks to blank. Its paid runtime has one positive uniform coefficient times original volume times max-one-width to the certified exponent.

- `Machine/BinaryAdjacentWidthHeadersShared.lean`: Actually writes the zero high-count control and constructs P, binary-range times G, and binary-range times B from the four original P/G/B/width headers. Named movement source slots, literal canonical values, caller preservation and reverse erasure of every generated field have linear rectangular-volume bounds.

- `Machine/BinaryAdjacentWidthMovementShared.lean`: One actual shared-source lifecycle constructs binary movement dimensions from only the original four P/G/B/width headers, physically copies the three execution headers, executes radix-two movement or inverse movement, and erases every generated and copied descriptor. All forty private tapes start and finish blank; exact movement words, arbitrary caller preservation and linear rectangular-volume runtime are proved without generated-header or preimage assumptions.

- `Machine/BinaryRadixRangeRuntimeBudget.lean`: Bounds the actual total radix-run cost after numerical binary range padding, and absorbs preparation, physical root-header setup/cleanup, cropping and four real joins. The complete stage cost preserves the certified exponent against original binary volume and max-one binary width.

- `Machine/BinaryRadixEqualRun.lean`: One actual fixed five-stage machine prepares binary-to-radix data, physically constructs six root headers, runs the complete total radix interchange, erases the root headers, and crops while erasing numerical range metadata. Exact original binary transpose, wholly blank private endpoints, zero-width coverage and one positive uniform coefficient at the certified exponent are proved.

- `Machine/BinaryRadixEqualShared.lean`: Physically copies the four original caller shape/width headers into blank private storage, shares the literal payload with the complete binary interchange, and erases the copied headers afterward. Exact transpose and preservation of all other caller fields and private blank storage are proved, with the unchanged certified exponent.

- `Machine/BinaryAdjacentWidthPrefixShared.lean`: Physically writes the canonical one and constructs the doubled spectator prefix from original headers using the radix-two dimension engine. Literal doubled-prefix sources, canonical values, caller preservation, paid rectangular-volume budgets and complete eighteen-tape erasure are proved.

- `Machine/BinaryAdjacentWidthRun.lean`: One actual long-H program performs prefix construction, the complete caller-shared equal-width binary transpose, constructed binary movement and all cleanup. The long-D program performs actual inverse movement before the equal-width call. Both return the exact original rectangular transpose from sole original headers with every private bank blank, including zero shorter width, and a positive uniform coefficient at the certified exponent.

- `Machine/BinaryAdjacentWidthSelector.lean`: Actually compares both canonical original widths, reuses and erases a blank flag, and halts in one of three finite states: equal, longer H, or longer D. All original cells and heads are restored. Exact state/value equivalences, adjacent-width consequences and a linear original-volume comparison budget cover zero-width cases.

- `Machine/BinaryAdjacentWidthSelectorDispatch.lean`: A real finite-flow composition connects the physical three-way selector to the selected supplied branch program and its genuine halt. Conditional branch contracts and all selector/jump/branch costs are proved. Instantiating the final concrete equal/adjacent machine is separate.

- `Machine/BinaryInterchangeRun.lean`: A fixed concrete binary rectangular interchange machine reads the original five canonical headers, physically selects equal or adjacent-width branches, returns the exact transpose, and preserves all other caller tapes while restoring every private tape and head. Covers zero widths with no branch callbacks or derived-header inputs.

- `Machine/BinaryInterchangeBudget.lean`: Proves one positive uniform coefficient bounds the actual comparison, dispatch and selected concrete branch runtime by original rectangular volume times max-one maximum width to the certified exponent 1−296/10^11.

- `Machine/CountedGatherField.lean`: A fixed five-tape eighteen-state machine copies and applies a Boolean operation to a runtime-counted field while holding the control head fixed. Exact whole-word and interior-field semantics retain source/control and arbitrary target exterior, restore both binary controls and pay linear field time, including zero.

- `Machine/CountedGatherPadding.lean`: Fixed five-tape eighteen-state machines seek either direction or write an exact runtime-counted run of false symbols, preserving all spectators and arbitrary exterior. Immutable descriptors and reusable clocks are restored; zero counts and canonical linear bounds are proved.

- `Machine/CountedGatherDigit.lean`: Composes runtime-counted source prefix/suffix seeks, target zero prefix/suffix writes, mapped field copying and one control-head step in one fixed nine-tape ninety-two-state machine. Exact digitWord output preserves source/control and target exterior, restores all five immutable descriptors and the clock, and costs at most fourteen times both strides plus121 for canonical counts.

- `Machine/CountedGatherRun.lean`: A fixed eleven-tape108-state machine loops the concrete gather digit using an independent runtime digit-count descriptor. Proves the exact whole gathered word with arbitrary exterior and all eight controls restored, including zero counts/strides. Paid canonical runtime is at most134 times digit count times source stride plus target stride plus one, plus23. Shape metadata construction and packed arithmetic composition remain separate.

- `Machine/CountedGatherMetadata.lean`: A fixed ten-tape machine executes four immutable descriptor subtractions from six original gather controls to construct both suffix lengths. Original and derived literal cells, canonical values and the five digit-header sources are identified; complete derived-header erasure and linear setup/cleanup costs include zero dimensions. Sharing this bank with the gather and initializing its clocks remain separate.

- `Machine/CountedPackedLine.lean`: A uniform thirteen-tape line executes the actual runtime-counted gather, physical source/control/offset rewinds, modular column transduction, offset erasure and accumulator/result rewinds. Exact result semantics retain all inputs and controls, restore every payload head, and have canonical runtime at most140 times total digit stride plus three accumulator lengths plus42, including zero cases. Shape metadata and complete multi-line packed-control execution remain separate.

- `Machine/CountedGatherClockPair.lean`: Physically writes two independent marked-zero clocks from blank storage in one transition and erases both in two transitions. Exact native and arbitrary-caller placement contracts preserve every spectator; no prepared marker or input initialization is assumed.

- `Machine/CountedPackedShapeHeaders.lean`: Constructs the six original gather headers for each of the three static packed-line shapes from caller-owned canonical q/b/n alone. Physically writes and erases temporary zero/one, copies all six headers, preserves the caller and erases all eight private tapes on cleanup; setup and cleanup are linear in q+b+n+1. No derived-header input is supplied.

- `Machine/MultiplicationInputSplit.lean`: A fixed three-tape thirteen-state parser preserves the original MSB-first x/separator/y input and physically writes least-significant-first copies of both operands to blank tapes. Literal endpoint, genuine halting and cost at most three x lengths plus two y lengths plus twelve include empty operands. Connecting multiplication and exact-width output installation remains separate.

- `Machine/CountedGatherOriginalRun.lean`: One actual fixed gather constructs four suffix headers and two independent clocks from blank storage, executes the complete runtime-driven gather through caller-owned payload and original six headers, then physically erases every private tape. Exact gathered output, retained source/control and originals, arbitrary target exterior and a uniform169-times-full-stride bound include zero dimensions/counts; no prepared metadata or branch callbacks are supplied.

- `Machine/ElementaryMultiplyCore.lean`: One fixed four-tape machine parses original packed input, physically positions the reversed operands and executes the literal Horner multiplier. The original input is retained and the literal accumulator has exact product value; equal-length runtime is at most24 times n squared plus n plus one, including empty operands. Exact twice-length MSB output installation and the fast path remain separate; no sublogarithmic claim is made.

- `Machine/CountedPackedOriginalLine.lean`: One fixed seventeen-tape modular line constructs and erases all gather suffixes and both clocks from blank workspace, performs exact gathered column arithmetic, erases offset scratch and restores every payload head. Only the six original canonical gather headers remain inputs; they are retained, all six private tapes return blank, and the total uniform full-stride bound includes zero cases. Runtime q/b/n shape construction and multi-line composition are separate.

- `Machine/CountedPackedRuntimeLine.lean`: One fixed twenty-two-tape line constructs shape headers from only original q/b/n, executes the original-header gathered modular arithmetic and erases all fourteen private tapes. Exact result semantics retain source/control/accumulator and original q/b/n, restore every payload head and offset scratch, and have uniform530-times-full-stride plus three accumulator lengths, including zero digits. The static shape kind and Boolean/rule operations are compile-time choices; no runtime dimensions appear in the program.

- `Machine/DoubleClockReverseCopy.lean`: Fixed two-state machines use a literal bit word as a length clock to seek two source cells or copy two descending source cells per clock symbol. Exact twice-length execution retains every source/clock cell, preserves arbitrary target exterior and maps blank source cells to false bits, including empty clocks. Product-specific output semantics and final multiplication installation remain separate.

- `Machine/CountedPackedArith.lean`: Fixed twenty-six-tape forward packed arithmetic composes five runtime-driven modular lines from original q/b/n and blank metadata storage. Exact packedEarly values, restored original descriptors and all fourteen private metadata tapes blank are proved, with uniform2669-times-full-stride cost. Intermediate payload words remain; reusable copy-back and payload erasure are separate.

- `Machine/CountedPackedInverse.lean`: Fixed twenty-six-tape inverse packed arithmetic composes five runtime-driven lines, proves a true packedEarly preimage and restores original q/b/n and fourteen private metadata tapes with the same uniform stride bound. Intermediate payload words remain; physical permutation and reusable payload cleanup are separate.

- `Machine/ElementaryMultiplyOutputData.lean`: Connects literal descending accumulator reads to exactly twice-length MSB product bits, padding blanks as zero. Proves output length and value for the Horner accumulator including empty operands; actual output installation is provided separately.

- `Machine/ElementaryMultiply.lean`: One fixed four-tape machine parses original multiplication input, computes the Horner accumulator, physically erases input and copies exactly twice-length MSB product bits using an operand clock. Genuine halting, literal outputCorrect and Assembly.RunsWithin at40 times n squared plus n plus one hold for every equal input length, including zero. This completes the ordinary quadratic fallback; fast-path assembly and the sub-n-log-n bound remain open.

- `Machine/EqualWordReplace.lean`: One fixed two-tape seven-state machine copies an equal-width word over an existing target, rewinds both heads and preserves arbitrary exteriors. A literal overwrite lemma justifies replacing every target cell without a preliminary erasure; total cost is at most three lengths plus six, including empty words.

- `Machine/WordBankCleanup.lean`: Generic fixed-slot word replacement and physical scan/erase act on a selected caller bank, preserving the full complementary frame. The target and source heads return to their original positions; exact contracts charge all transitions and handle zero widths.

- `Machine/CountedPackedRecycle.lean`: One fixed nine-tape seven-stage cleanup copies both new packed outputs into the original target and temporary tapes, then physically erases five intermediate payload words. Exact restored heads and a uniform affine word-length bound work for forward and inverse layouts, including unguarded addresses.

- `Machine/CountedPackedReusable.lean`: Complete fixed forward and inverse packed arithmetic reads original q/b/n, copies both output words back into the original payload slots and physically erases every generated payload and metadata tape. Exact word endpoints retain all source/control exteriors and original descriptors, restore every head and have uniform2720-times-full-stride cost, including zero digits. Physical payload permutation and late-control load/unload remain separate.

- `Machine/CountedPackedGuarded.lean`: Proves literal word equality for the fixed runtime-driven packed early gadget on good input blocks: only selected low target bits toggle, and every temporary bit is restored. Connects actual block/control words to the packed integer correctness theorem, then lifts this to the reusable physical gadget with all intermediate payload and metadata tapes blank, heads restored and uniform2720-times-full-stride cost. The physical payload permutation remains separate.

- `Machine/BinaryPackedFieldSwap.lean`: Actual runtime-header binary field interchange retains complete payload records, arbitrary prefix/intervening/suffix fields and dirty back coordinates. Two real calls restore the entire caller payload and every private tape, charging both executions and the join; the uniform certified width exponent is retained. A data conjugation lemma identifies front actions by swap/back-action/swap. The physical packed-controlled back action and row reservation wiring remain separate.

- `Machine/BinaryOffsetStreamRead.lean`: Fixed ten-state reader physically clears the previous marked offset, copies the next literal blank-delimited bit word, restores the offset head and advances the control head across its delimiter. The complete control tape is retained; exact cost is two previous lengths plus two next lengths plus eleven, including empty words.

- `Machine/StreamedFiberTranslation.lean`: Fixed fifteen-tape243-state machine consumes one actual canonical offset word per prefix fiber, synthesizes split descriptors and physically rotates that fiber, retaining the entire control tape. Runtime is at most481 times payload volume plus23. Recurring metadata markers remain explicit inputs, final offset and advanced heads explicit outputs; initialization and normalization are separate.

- `Machine/StreamedFiberTranslationArray.lean`: Connects the actual streamed-offset machine to literal finite arrays: each prefix/back/suffix entry reaches back address plus its physically read offset modulo Q. Exact source/control preservation, destination tape and advanced heads are proved, including empty prefix families. No payload permutation or preparation callback is assumed.

- `Machine/StreamedFiberTranslationAlphabet.lean`: Lifts the real fixed streamed-offset rotation to any larger finite alphabet with unchanged runtime, literal encoded array source, exact bit destinations, retained original Q/B/n headers and full control stream. The first four symbols preserve their actual blank/bit/separator identities, enabling placement with the binary interchange alphabet. Recurring markers and retained final offset remain explicit; initialization and normalization are separate.

- `Machine/CountedPackedParityHeaders.lean`: Constructs gather headers [b,0,1,1,0,n] from only original canonical b/n on physical tapes, with paid zero/one initialization, exact source preservation and cleanup of all private header storage. Width one is supported without a stronger artificial width restriction.

- `Machine/CountedPackedParityRun.lean`: One fixed nineteen-tape program extracts the lowest bit of every dirty b-bit source block into an n-bit control word, clocked by a literal dummy control word and original b/n headers. Source/control and original descriptors are retained, every head restored and fourteen private tapes returned wholly blank, with bound330 times full stride. Includes b=1 and n=0; later-source load/unload remains separate.

- `Machine/StreamedFiberTranslationInitialized.lean`: Complete fixed fifteen-tape streamed rotation lifecycle reads only original B/Q/n headers and a literal offset stream, physically initializes recurring markers, executes every payload fiber rotation and erases the last offset and all private markers. All nine private slots return wholly blank at head zero; source/control and original headers are retained. Actual payload/control heads advance explicitly; total cost is at most483 times payload volume plus35, including empty streams.

- `Machine/StreamedFiberTranslationInitializedAlphabet.lean`: Executes the complete blank-private-storage streamed rotation on any larger finite alphabet with literal input/output banks and unchanged483-volume-plus35 cost. Exact encoded array and control words, retained original B/Q/n headers and all nine private tapes blank/head zero enable interchange-alphabet integration. Final payload/control normalization and complete packed-gadget assembly remain separate.

- `Machine/CountedPackedParityValue.lean`: Proves physically extracted low block bits equal the parities of the power-of-two radix digits, then connects the actual clean parity-extraction run to the later-source packed integer specification with its exact uniform stride bound. No control word is supplied by an arithmetic oracle; full late-gadget composition remains separate.

- `Machine/CountedPackedControlLoadHeaders.lean`: Physically constructs the six original gather headers [1,0,1,b,0,n] from retained canonical b/n, including paid zero/one setup and full private header cleanup. Width one and zero counts are supported.

- `Machine/CountedPackedControlLoadLine.lean`: A fixed twenty-one-tape gathered modular line constructs and erases all shape headers, suffixes and clocks from only original b/n. It realizes a static add/subtract rule and leaves only exact result payload words; runtime dimensions do not occur in finite control.

- `Machine/CountedPackedControlLoadRun.lean`: Complete reusable fixed dirty-control load/unload physically copies the one-bit control source, applies gathered modular arithmetic, copies the result over the original dirty word and erases every scratch payload and metadata tape. X and original b/n are retained with all heads restored and seventeen private tapes blank; bound380 times full stride includes b=1 and n=0.

- `Machine/CountedPackedControlLoadValue.lean`: The actual load/unload output words have value U plus/minus the packed control-bit integers modulo the full power-of-two word radix. Their widths equal the original dirty word, with no stronger width restriction or supplied arithmetic offset oracle.

- `Machine/PackedOffsetStreamEmit.lean`: Fixed six-state emission physically copies canonical bits into the control stream, writes and crosses a blank delimiter, and erases the marked source scratch. Literal output and full scratch cleanup include canonical zero.

- `Machine/PackedOffsetStreamBlock.lean`: Fixed thirty-state runtime-width body copies one raw binary block, physically trims high zeros and emits its canonical little-endian representation plus a delimiter. Source is retained, scratch returns wholly blank and the width descriptor/clock are preserved.

- `Machine/PackedOffsetStream.lean`: Fixed seven-tape51-state machine initializes both private clocks, processes all runtime-counted packed blocks and erases every clock/scratch tape. Literal emitted stream contains the canonical block values, source and original width/count headers survive, private three tapes return blank/head zero and total cost is at most66 times n times w-plus-one plus28, including zero width/count.

- `Machine/PackedOffsetStreamRaw.lean`: Connects the actual stream builder to a raw n*w-bit input word: emitted canonical values are precisely its radix-two-power digits, each below2^w, in their literal order. Source and descriptors are retained, output length is at most n*(w+1), all private tapes blank and physical advanced heads explicit. No canonical offset stream is assumed as input.

- `Machine/CountedPackedLateData.lean`: Exact word specification for the two early gadgets and physical dirty load/unload: all six intermediate/final widths match their originals, and the unrestricted integer triple is precisely packedLate. On actual guarded input blocks, only selected low target bits toggle and both dirty temporary words are restored literally. Sequential machine execution is proved separately.

- `Machine/CountedPackedLateRun.lean`: Complete fixed twenty-eight-tape later-source arithmetic physically extracts parity, runs an early gadget, erases parity, loads dirty control, extracts new parity, runs the second early gadget, erases parity and unloads. Only original V/W/U/X and q/b/n are supplied; all twenty-one private tapes return blank/head zero. Exact packedLate values and guarded literal target toggling with both dirty words restored have bound7000 times full stride, including b=1 and n=0. Physical implicit-address payload permutation and row placement remain separate.

- `Machine/StreamedFiberTranslationReusable.lean`: Complete fixed streamed binary payload rotation physically initializes private metadata, rotates every fiber, rewinds source/output, copies equal-width rotated output back over the original source and erases the temporary output. Source exterior/head, original B/Q/n and all private tapes are restored; control symbols retained with its head explicitly at stream end. Uniform500-volume-plus70 cost includes empty arrays. Control-head normalization and full packed-offset/interchange assembly remain separate.

- `Machine/MarkedControlStreamReset.lean`: Fixed one-tape machines rewind and erase a separator-marked control stream even when it contains internal blank delimiters. Exact costs retain every stream cell during rewind and erase the complete stream during reset, with the final head at zero.

- `Machine/PackedOffsetPayload.lean`: One fixed seventeen-tape machine synthesizes canonical controls from a literal packed bit word, rotates each payload fiber in place, erases the generated stream and restores both original heads. Original B/Q/n/w descriptors and tape exteriors survive, all private tapes return blank and cost is at most600 times payload volume plus150.

- `Machine/PackedOffsetPayloadValue.lean`: Identifies each physical fiber rotation offset with the actual integer value of its corresponding fixed-width packed source field, connecting the tape endpoint to the original packed bits rather than a supplied offset stream.

- `Machine/PackedOffsetPowerHeader.lean`: A fixed placed power-descriptor machine synthesizes the canonical Q=2^w header from the original width descriptor. All six other active scratch slots are restored, the complementary frame is retained and actual cleanup erases Q. Synthesis and cleanup have separate bounds proportional to Q, including empty payloads.

- `Machine/PackedOffsetPayloadOriginal.lean`: One fixed seventeen-tape machine generates Q=2^w from the original width, synthesizes offsets from the packed source, rotates full payload records and erases both the control stream and Q. Only original B/n/w and bit words are inputs; every private tape and both source heads are restored. Cost explicitly includes Q for zero fibers and is linear in payload volume when n is positive.

- `Machine/CountedPackedLatePlacement.lean`: Places the reusable guarded early and late gadgets into any static injective caller tape slots. Literal target toggles, original descriptors, blank private workspace, all heads and the complete complementary frame are proved together; fixed control and existing2720/7000 full-stride costs are retained.

- `Machine/CountedGuardTest.lean`: A fixed six-tape comparison-and-flag machine reads its runtime width from an original canonical descriptor, compares exactly those physical bits, appends the exact ordering flag, erases order/countdown scratch and retains the descriptor. Cost14 times width plus32 includes zero; outer record traversal and the complete uniform repair-key routine remain open.

- `Machine/PackedOffsetPayloadArray.lean`: Returns the physically rotated payload as a canonical Bool array and proves exact per-address packed-offset destination semantics. This supplies a literal array handoff for subsequent binary interchanges without a free copy or permutation.

- `Machine/PackedOffsetPayloadAlphabet.lean`: Lifts the original-header packed-offset rotation to any larger fixed alphabet with exact literal payload array, original head retention, complete private cleanup and unchanged charged runtime.

- `Machine/PackedOffsetPayloadPlaced.lean`: Shares caller payload, packed source and B/n/w descriptors directly through static injective wiring. Twelve private tapes start and return wholly blank; all caller spectators and heads are retained, with an exact canonical-array endpoint and paid power-synthesis cost.

- `Machine/BinaryRepeatedOffsetAction.lean`: identifies the physically generated repeated parity, selected, correction and negative parity-XOR offset words with the actual swap/rotate/swap permutation. Proves exact packed parity, selected two-times-control-times-digit, and signed correction offsets and destination entries, retaining the dirty back coordinate and every suffix bit. Physical producer/action sequencing remains separate.
- `Machine/BinaryPackedOffsetData.lean`: Exact swap/packed-back-rotation/swap array semantics. The front field reaches its modular offset destination, indexed by the original dirty back coordinate; that back coordinate and every suffix bit are retained literally.

- `Machine/BinaryPackedOffsetRun.lean`: One fixed shared-caller machine executes two actual binary field interchanges around the placed original-header packed-offset rotation. Both private banks are blank on return, caller headers and packed source are retained, and every call and sequencing transition is charged. Complete packed-arithmetic and reservation assembly remains separate.

- `Machine/BinaryPackedOffsetBudget.lean`: The actual complete swap/rotate/swap cost retains the certified interchange width exponent. Power-header generation, payload rotation, physical erasure and both sequencing transitions are absorbed into full nonempty payload volume; no call cost is omitted.

- `Machine/CompactRowHeaders.lean`: Physically constructs the six row-split headers from original canonical total-row/role-count/record-width descriptors, retains originals, erases temporary zero/one writers and cleans every generated descriptor with charged bounds.

- `Machine/CompactRowSplit.lean`: A fixed-role-count machine composes actual runtime-header construction, destructive complete-row splitting and generated-header cleanup. The source is erased, full role words installed, original descriptors retained and all private storage blank.

- `Machine/CompactRowArray.lean`: Connects actual row splitting to Compact.Layout.splitRows on literal finite arrays. Every suffix cell, including dirty temporary fields, is preserved. Positive rows/width and static positive role count are explicit; runtime and full cleanup are linear in total payload volume.

- `Machine/CountedGuardGadgetPosition.lean`: Fixed placed runtime-counted left/right head movements retain the full caller frame and clean countdown workspace. These replace within-record width-unrolled guard replays; no free head normalization is assumed.

- `Machine/CountedGuardGadgetHeaders.lean`: Physically constructs the q−1 comparison descriptor from original q/b/n and blank work, erases the temporary one and retains originals. Exact width value, canonical form and cleanup include q=1; full multi-record guard execution remains separate.

- `Machine/CompactRowPaddingRound.lean`: Physically writes the static role count, derives the least enclosing row multiple from original runtime row count/width, erases role-count arithmetic scratch and returns the exact Compact.Layout.paddedRows descriptor. Every positive row/role case is included.

- `Machine/CompactRowPaddingRun.lean`: A fixed twenty-five-tape machine rounds original row count, constructs all span descriptors, pads complete binary records and physically erases all twenty-one private tapes. Original headers/heads and tape exteriors survive. Bound4600 times padded volume,9200 times original volume when roles≤rows, and a fixed-role bound handle all positive rows. Padding-to-role-split composition remains separate.

- `Machine/BinaryAddressTableData.lean`: Defines the literal little-endian fixed-width address rows, proves every row has its stated rank and width, and proves enumeration wraps exactly to zeros after2^w rows, including width zero.

- `Machine/BinaryAddressTableStep.lean`: A fixed physical body copies one address row, restores its source head and increments the counter. Exact next-row and wrap semantics have cost at most4 times width plus7.

- `Machine/BinaryAddressTableFill.lean`: Physically initializes the fixed-width zero counter from the original width descriptor and blank storage, with exact literal cells and restored descriptor; no prepared address table is supplied.

- `Machine/BinaryAddressTable.lean`: A fixed nine-tape machine generates the entire regular address table from the sole original canonical width, physically synthesizes its2^w loop bound, executes every copy/rewind/increment, returns output head zero and erases all seven private tapes. Cost is proportional to(w+1)*2^w; payload-volume absorption requires record width at least w+1. Selected/parity gather composition remains open.

- `Machine/CountedGuardGadgetRecord.lean`: Fixed eleven-tape per-record guard bodies execute all physical comparisons, descriptor-driven target replay and constant rewinds. Exact legacy V/W flags, clean private comparison/replay storage and44q+104/15b+35 costs are proved; runtime n-loop assembly remains separate.

- `Machine/BinaryPackedRowCount.lean`: A fixed thirteen-tape machine physically derives the fiber count P*2^w*G from original P/G/B/w headers through one power and two products. Original headers are retained, intermediate Q/PQ and all scratch are erased, and only the canonical derived count survives, including width zero.

- `Machine/BinaryPackedRowCountPlaced.lean`: Shares four static injective original-header slots with a caller bank and nine blank private tapes. The generated count occupies the first private slot, every other private tape returns blank, and the complete complementary frame is retained. Actual count erasure restores the original caller and all private tapes.

- `Machine/BinaryPackedRowCountBudget.lean`: The actual original-header count preparation has bound(constant2+110)*fiberCount+75 for positive P/G. Retained count erasure costs at most2*fiberCount+6; every power/product/setup/join/cleanup is paid. Wiring this producer into the full payload permutation remains separate.

- `Machine/CountedGuardGadgetArray.lean`: Two actual fixed counted n loops generate exactly the legacy V/W guard flag word, physically initialize and erase the outer clock, retain q−1/b/n descriptors, and include zero records. Canonical n gives cost n*(44q+15b+165)+54; original-q setup and finalization are separate.

- `Machine/CountedGuardGadgetFinish.lean`: Physically rewinds both guarded sources and flag word, scans the actual AnyFlag result into blank output, erases the complete flags and retains all spectators. The exact cleanup/finalization budget is source lengths plus three flag lengths plus13.

- `Machine/CountedGuardGadgetOriginal.lean`: Actual original-q/b/n preparation, fixed runtime n loops and physical q−1 cleanup produce the exact legacy guard flag word. Original headers, sources and constant words survive; no derived comparison descriptor or flags are supplied.

- `Machine/CountedGuardGadget.lean`: Complete fixed fifteen-tape guard gadget physically constructs q−1, traverses both runtime n loops, rewinds inputs, scans AnyFlag and erases flags/private workspace. Exact legacy result, all original q/b/n and constant words/heads retained, and350-times-full-stride cost include n=0 and q=1. Certified mathematical membership and complete repair-key assembly are separate.

- `Machine/CountedGuardGadgetValue.lean`: Connects the actual fixed-control guard result cell to exceptional-address membership under the certified power-of-two comparison constants. Full paid execution decides not earlyGood within350 times full stride, deriving field-range bounds from literal word lengths. Constant synthesis and complete rank/key assembly remain separate.

- `Machine/CompactRowReservationPlacement.lean`: Places complete-row splitting onto the actual padded destination and role outputs with retained physical rounded/role/width headers. Original row count and the complete padding workspace are framed.

- `Machine/CompactRowReservationData.lean`: Literal padded role-array specification, with exact source/role/suffix coordinates. Original rows retain every payload bit and dirty suffix field; added whole rows are zero.

- `Machine/CompactRowReservationRun.lean`: One fixed-role machine executes original-header rounding and padding, writes static role count, splits the padded complete records, and physically erases all retained role/rounded headers. Exact final original headers, erased source/padding destination, literal role words and clean private banks are proved.

- `Machine/CompactRowReservationBudget.lean`: The complete physical pad/split/erase path costs a static-role constant times original row count and record width for all positive cases, including fewer input rows than roles. The usual roles≤rows range has the sharper twice-original-volume bound.

- `Machine/CompactRowReservationEndpoint.lean`: Explicit whole-bank endpoint for the original-descriptor binary reservation path: original row/width headers and heads retained, complete padded role words installed, original source/padding destination and every private tape blank at head zero. Reserved compact-gadget slot/capacity instantiation remains separate.

- `Machine/BinaryPackedOffsetOriginalRun.lean`: One fixed original-header wrapper computes P*2^w*G from the four original interchange headers, executes the actual swap/rotate/swap on the supplied literal packed-offset word and canonical payload, physically erases the generated count and restores every private bank. Exact result and all preparation/action/cleanup/sequencing costs are proved; implicit-address offset production and packed arithmetic assembly remain separate.

- `Machine/BinaryPackedOffsetOriginalBudget.lean`: The complete original-header count/action/erasure path preserves the certified interchange exponent. Actual count preparation and cleanup are absorbed into nonempty payload volume; no derived count word or free preparation is assumed.

- `Machine/CountedGuardConstantsData.lean`: Exact padded little-endian comparison patterns with certified widths and power-of-two values for b≥1 and b+3≤q.

- `Machine/CountedGuardConstantsFill.lean`: Actual runtime-counted zero/one fills and paid rewinds from binary width descriptors, with exact words and framed caller storage.

- `Machine/CountedGuardConstantsEdit.lean`: Physical runtime b-positioned bit overwrite and return, with exact padded-pattern semantics and charged linear-width execution.

- `Machine/CountedGuardConstantsPlacement.lean`: Eight-tape shared placements for constant filling, rewinding and editing preserve the original q/b and all complementary tapes.

- `Machine/CountedGuardConstants.lean`: One fixed eight-tape machine constructs all three literal guard constants from sole original canonical q/b headers, with exact widths/values, retained headers and blank private descriptor/one/clock. Cost40q+80b+300 charges fills, edits, returns and cleanup. Composition into the fifteen-tape guard remains separate.

- `Machine/CountedGuardOriginalSetup.lean`: Places the physical q/b constant constructor into the existing fifteen-tape guard bank, preserving literal V/W and original q/b/n while synthesizing exact constants from blank private storage.

- `Machine/CountedGuardOriginalCleanup.lean`: Physically scans and erases all three generated guard constants, retaining source words, original descriptors and the actual result bit with charged linear cleanup.

- `Machine/CountedGuardOriginal.lean`: Complete fixed fifteen-tape exceptional-address guard from only original V/W and canonical q/b/n. Physically constructs constants, executes the actual guard, decides not earlyGood and erases every private tape except the result bit. Original heads are restored; bound1000*(n+1)*(q+b+1) includes zero records. Repair-key assembly remains separate.

- `Machine/CountedIdealToggle.lean`: Fixed twenty-two-tape ideal selected-parity toggle from original q/b/n descriptors: actual controls-at gather plus XOR returns exactly the target word exclusive-or the padded control mask, retains all original inputs/heads and erases every generated descriptor, clock and mask. Integer toggle semantics and bound533*(n+1)*(q+b+1) are proved; repair-key placement remains separate.

- `Machine/BinaryAddressOffsetHeaders.lean`: Physically derives q*n,2^(q*n) and n*2^(q*n) descriptors from original canonical q/b/n, retaining originals and clearing arithmetic scratch with charged setup and erasure.

- `Machine/BinaryAddressOffsetData.lean`: Literal regular-address parity offsets with exact n*b-bit row width, low-bit destinations and zero padding for every source address and packed digit.

- `Machine/BinaryAddressOffsetPrepare.lean`: Physically constructs the regular address table and the counted dummy-zero control stream from original headers; every descriptor, initialization and output rewind is paid.

- `Machine/BinaryAddressOffsetGather.lean`: Actual runtime parity gather traverses the generated address table and dummy controls, produces all offsets in rank order and restores original descriptors and private gather metadata.

- `Machine/BinaryAddressOffsetCleanup.lean`: Physically erases the generated regular address table, dummy control and all derived dimension headers, rewinds the retained offset output and restores all private tapes.

- `Machine/BinaryAddressOffset.lean`: Fixed thirty-tape parity-offset producer from sole original q/b/n, including zero digits. Original headers survive, only the literal offset word remains and all other private tapes are blank. BoundK*2^(n*q)*(n+1)*(q+b+1) is absorbed under an explicit record-width allowance; caller placement and repetition across dirty-back/spectator coordinates remain separate.

- `Machine/BinaryAddressOffsetValue.lean`: Connects each literal generated offset row to the packed parity of the source address digits, with exact integer value and target modular range. No prepared offset table is assumed.

- `Machine/CountedRankSplitCopy.lean`: Fixed runtime-counted bit copier reads actual blank-tail cells as zero, writes literal field words and retains source/control storage. No padded source word is assumed.

- `Machine/CountedRankSplitPosition.lean`: Placed physical counted left walks restore source and destination heads while retaining caller tapes and erasing countdown workspace.

- `Machine/CountedRankSplitData.lean`: Exact zero-extended low/middle field words for arbitrarily short rank counters, value splitting and in-range rank reconstruction without a stored-width premise.

- `Machine/CountedRankSplitBank.lean`: Twelve-tape rank-split wiring derives n*q and n*b from original headers, copies both fields, physically rewinds all heads and erases generated dimensions with complete frame lemmas.

- `Machine/CountedRankSplitRun.lean`: One fixed runtime-driven machine produces both literal rank fields from original q/b/n while preserving the original counter and every head, erasing all six scratch tapes. Exact paid budget is bounded by400*(n+1)*(q+b+1).

- `Machine/CountedRankSplitEndpoint.lean`: Direct contract for the actual RepairScan growing counter with no padded/canonical stored-length premise. Both copied fields reconstruct the in-range rank, original counter/headers are retained and all private tapes are physically erased; full repair-key assembly remains separate.

- `Machine/BinaryAddressOffsetRepeatData.lean`: Literal packed-offset expansion order: repeat each row over trailing spectators then repeat the complete expanded table over preceding coordinates, including dirty back fields. Exact lengths and row concatenation are proved; the complete physical expansion is separate.

- `Machine/BinaryAddressOffsetRepeatCopy.lean`: Fixed two-tape actual word copy plus source rewind, preserving the source and advancing only the destination. Exact cumulative repeated words and cost2*length+3 include empty words.

- `Machine/CountedControlWordRepeat.lean`: Fixed four-tape original control-word repetition driven by an immutable runtime count. Physically initializes/cleans its loop clock, copies and rewinds every source word, restores output head and retains source/count. CostN*(3*length+9)+7*descriptorLength+31 is absorbed by54*N*(length+1) for positive canonical counts.

- `Machine/BinarySelectedOffsetPrepare.lean`: Fixed seventeen-tape preparation for the selected mask-shift offset load. From original b/q/n and one original control word, builds the complete regular temporary-address table and its physically repeated controls, retains originals and clears local clocks. Exact table/control words and all setup/copy/return costs are proved; selected gather, value linkage and final table/header erasure remain separate.

- `Machine/BinarySelectedOffsetData.lean`: Literal selected mask-shift offsets over regular temporary addresses with physically repeated original controls. Exact source/control/output widths are proved, including zero digits.

- `Machine/BinarySelectedOffsetGather.lean`: Actual fixed original-header mask-shift gather traverses the generated regular table and repeated controls, retains the original b/q/n and control word, and restores all generated shape/count metadata with charged runtime.

- `Machine/BinarySelectedOffsetCleanup.lean`: Physically erases both generated streams and every derived width/range/count descriptor, rewinds the packed offset output and retains original headers/control. Exact whole-bank endpoint and every cleanup transition are proved.

- `Machine/BinarySelectedOffset.lean`: Fixed thirty-one-tape selected mask-shift offset producer from original b/q/n and one original control word. Builds every table/control/header, executes the actual gather, erases generated inputs and private storage, and returns the exact packed offset word at origin. CostK*2^(n*b)*(n+1)*(q+b+1) includes zero digits; payload absorption requires an explicit record-width allowance. Caller repetition and full packed-gadget assembly remain separate.

- `Machine/BinarySelectedOffsetValue.lean`: Each physically generated selected-offset row is exactly the packed2*z*w load for the first early-source update. Proves original-control alignment, complete literal row equality and integer offset value for every regular temporary address; no repeated controls or offset oracle are supplied.

- `Machine/BinarySelectedOffsetPlaced.lean`: Places the complete selected mask-shift producer on any larger alphabet and five distinct caller ports for b/q/n, original controls and output. Preserves all complementary caller tapes/heads, retains original controls/headers, returns literal packed offsets and restores26 appended private tapes with unchanged certified cost.

- `Machine/CountedRepairKeyBank.lean`: Thirty-tape fixed repair-key bank and exact shared placements for rank splitting, inverse arithmetic, original-input guard and ideal toggle. The original short scan counter/control/q/b/n are retained.

- `Machine/CountedRepairKeyPrefix.lean`: Actual fixed-control rank split, exceptional guard, inverse packed arithmetic and ideal toggle composition. Exact flags/recovered words and all sequencing costs are proved from original runtime descriptors.

- `Machine/CountedRepairKeyAppendMoves.lean`: Physical flag write, source-head positioning, destination copies and marked-key returns for the conditional repair key, preserving all framed tapes.

- `Machine/CountedRepairKeyAppend.lean`: Actual conditional destination append: true flags receive the exact toggled-inverse destination words, false flags receive only the flag. Source/key rewinds are paid.

- `Machine/CountedRepairKeyWrite.lean`: Thirty-tape actual guard-controlled key write preserves original words/headers/counter, returns every source/key head and charges the conditional branch and all copied destination cells.

- `Machine/CountedRepairKeyCleanup.lean`: Physically erases every generated rank/inverse/toggle word and the guard result, restoring complete private storage while retaining the written key and original inputs.

- `Machine/CountedRepairKeyRun.lean`: One fixed thirty-tape complete repair-key machine from original canonical q/b/n, control and actual short scan counter. Exact conditional key, original-input preservation and full workspace restoration hold within5100*(n+1)*(q+b+1).

- `Machine/CountedRepairKeyValue.lean`: Actual short-counter membership flag and destination-word semantics equal the compact instance rankFlag/rankKey. Zero extension is justified by physical blank-tail copies; no padded counter is supplied.

- `Machine/CountedRepairKeyScan.lean`: Places the fixed key machine into the actual forty-two-tape repair scan bank and proves RepairScan.KeyContract with exact rank flags/destination keys, retained non-key scan tapes and reusable28-tape scratch. Full outer scan/sort/reinsert initialization and assembly remain separate.

- `Machine/BinaryAddressOffsetRepeatBlock.lean`: Fixed runtime-width source-block copying, scratch rewinding and repeated block output with exact complete-block preservation and charged controls.

- `Machine/BinaryAddressOffsetRepeatPass.lean`: Actual counted traversal of all base offset rows repeats each row over the trailing spectator dimension, erases block scratch and restores counted workspace.

- `Machine/BinaryAddressOffsetRepeatLoop.lean`: Physically repeats the expanded table over preceding coordinates, paying table rewinds and all outer countdown operations.

- `Machine/BinaryAddressOffsetRepeat.lean`: Complete fixed eleven-tape offset repetition: actual nested loops, block/source erasure, output rewind and all four private marker cleanups. Original width/count descriptors retained; zero block width supported.

- `Machine/BinaryAddressOffsetRepeatBudget.lean`: Full physical repetition budget at most250*K*N*L*(W+1) for positive row/repetition counts, charging every copy, rewind, clock and cleanup.

- `Machine/BinaryAddressOffsetRepeatValue.lean`: Exact expanded row lookup and integer offset values through trailing and preceding repetitions, with no free duplicated table.

- `Machine/BinaryAddressOffsetRepeatAlphabet.lean`: Lifts the initialized repetition machine to any larger alphabet with unchanged runtime and literal output words.

- `Machine/BinaryAddressOffsetRepeatPlaced.lean`: Shares six caller ports and appends five blank private tapes for actual repetition, retaining every complementary caller tape and clearing all private storage.

- `Machine/BinaryAddressOffsetPlaced.lean`: Complete original-header parity-offset producer shares caller q/b/n/output slots, preserves all complementary storage and restores26 appended private tapes.

- `Machine/BinaryAddressOffsetRepeatHeaders.lean`: Physically synthesizes W=n*b,N=2^(n*q),K=P*H*2^(n*b) from original q/b/n/P/H/L, retaining originals and erasing all intermediate arithmetic/power scratch.

- `Machine/BinaryAddressOffsetRepeatConstruct.lean`: Fixed forty-nine-tape repeated parity-offset constructor from only six original canonical headers. Builds/consumes the regular base table, runs all physical repetitions and erases every generated descriptor/work tape; only output and originals remain.

- `Machine/BinaryAddressOffsetRepeatConstructBudget.lean`: All original-header setup, table generation, repetition and erasure costs are absorbed into the full payload volume under the explicit sufficient record-width allowance.

- `Machine/BinaryAddressOffsetRepeatCoordinates.lean`: Exact actual fiber row equation includes prefix, dirty back, preceding/source/trailing spectator coordinates. The repeated offset equals precisely the packed parity of its source coordinate, independent of dirty back and other spectators.

- `Machine/BinaryAddressOffsetRepeatConstructAlphabet.lean`: Lifts the complete original-input repeated parity constructor to the interchange alphabet with literal output and identical runtime.

- `Machine/BinaryAddressOffsetRepeatConstructPlaced.lean`: Complete arbitrary seven-port caller placement of the repeated parity constructor, appending/restoring42 private tapes and preserving every spectator. Actual source/dirty-back alignment and explicit volume absorption are proved; deriving upstream gadget geometry remains separate.

- `Machine/CompactGadgetReservationCapacity.lean`: Exact existing front2H/backH ceiling-chunk capacities, bounded slack and complete dirty-field allocation; no compact field is inserted into the row index.

- `Machine/CompactGadgetReservationShape.lean`: Concrete row/front-temporary/front-control/active/back/payload bit geometry, disjoint reserved slots, bit-count conservation and exact temp/control rectangular factorizations including slack.

- `Machine/CompactGadgetReservationData.lean`: Identifies each actual padded role word with the complete binary rectangle used by compact loads, preserving every unused bit and suffix coordinate.

- `Machine/CompactGadgetReservationRun.lean`: Actual original-header swap/rotation/swap on concrete temporary/back or control/back reserved slots. Exact per-coordinate load semantics preserve prefix, gap, dirty back, slack and payload.

- `Machine/CompactGadgetReservationBudget.lean`: Actual reserved-slot load runtime is bounded by role volume times max(1,n*G)^tau; complete movement costs are charged with no K factor.

- `Machine/CompactGadgetReservationPlacement.lean`: Shares the selected physical role tape with the native reserved-load machine, retains five supplied original shape/offset tapes and frames every other role and row header.

- `Machine/CompactGadgetReservationEndpoint.lean`: Exact selected-role physical load endpoint, with original shape/offset headers retained, all native workspace erased and complementary role words unchanged. A generic paid reserve/load sequencing helper is available; synthesizing shape/offset inputs and unconditional complete assembly remain separate.

- `Machine/BinarySelectedOffsetRepeatData.lean`: Literal selected-mask-shift row expansion repeats original-control offsets over trailing spectators and preceding prefix/dirty-back coordinates, with exact row counts and widths.

- `Machine/BinarySelectedOffsetRepeatConstruct.lean`: Fixed fifty-tape selected-offset constructor from six original b/q/n/P/H/L descriptors and one original control word. Physically synthesizes W=n*q,N=2^(n*b),K=P*H*2^(n*q), produces all base selected offsets, repeats/consumes them and erases every derived descriptor and private tape.

- `Machine/BinarySelectedOffsetRepeatBudget.lean`: Complete selected repetition cost, including original-control retention and all metadata/table/copy/cleanup costs, is absorbed into full payload volume under the explicit record-width allowance.

- `Machine/BinarySelectedOffsetRepeatCoordinates.lean`: Exact fiber lookup over prefix/dirty-back/source/trailing spectators returns the packed2*z*w offset from the original control and actual temporary source coordinate, independent of dirty back/slack.

- `Machine/BinarySelectedOffsetRepeatAlphabet.lean`: Complete selected-offset repetition on any larger alphabet, with unchanged physical runtime, retained originals/control and literal expanded output.

- `Machine/BinarySelectedOffsetRepeatPlaced.lean`: Eight caller ports carry original b/q/n/P/H/L, control and output; the complete selected repetition appends/restores42 private tapes while preserving every complementary caller tape/head. Output coordinate semantics and explicit volume bound are proved; upstream geometry and full packed-gadget assembly remain separate.

- `Machine/CountedRepairScanMetadata.lean`: Fixed twelve-tape runtime metadata constructor reads original q/b/n, derives nq/nb, and physically fills the actual unary sort selector and zero rank counter. Original descriptors are retained; generated widths and private work are erased.

- `Machine/CountedRepairScanMetadataRun.lean`: Proves the complete selector/counter construction and cleanup with cost1000*(n+1)*(q+b+1), including zero digit counts and no supplied derived width words.

- `Machine/CountedRepairScanSeed.lean`: Physically writes actual repair-stage marked sentinels and the initial counter separator into blank storage, with exact tape endpoints and a fixed paid cost.

- `Machine/CountedRepairScanPrepare.lean`: Places physical seed and runtime metadata construction into the actual forty-two-tape repair bank. Produces exactly the scan bank from original source/control/q/b/n within1004*(n+1)*(q+b+1).

- `Machine/CountedTapeRepairBank.lean`: Literal original-input and full repair-stage output banks, including the exact ideal stream on output10 and retained key scratch. Defines paid preparation plus scan/sort/strip/reinsert costs. Stage streams, selectors and sentinels remain explicit at the endpoint.

- `Machine/CountedTapeRepairRun.lean`: One fixed forty-two-tape machine physically prepares scan metadata, invokes the fixed runtime-driven repair key and executes actual scan, radix sort, prefix stripping and reinsertion. The exact output is the ideal early permutation, with all preparation and execution charged. Uniform record-volume/density budgeting and reusable final stage cleanup remain separate.

- `Machine/BinaryCorrectionOffsetRow.lean`: Copies exactly one runtime-width row from both operands, invokes the actual subtraction rule with fresh zero borrow, and erases both row scratch words. Exact modular difference and cost15W+14*headerLength+46 are proved; borrows never cross row boundaries.

- `Machine/BinaryCorrectionOffsetLoop.lean`: Fixed nested row traversal executes the physical subtraction independently for each address row, with exact output concatenation, restored row scratch and all counted-loop transitions charged.

- `Machine/BinaryCorrectionOffsetSubtract.lean`: Complete nine-tape per-row subtraction from two literal packed operand tables and original canonical width/count. Physically initializes and clears clocks, erases both full operand tables, rewinds output and restores all private storage; cost at most160*N*(W+1) for positive N. Original-address operand construction remains separate.

- `Machine/CompactGadgetReservationHeadersData.lean`: Runtime descriptor values for concrete reserved temp/control geometry: products, rounded capacities, nonnegative gaps and fixed-base powers from seven original K/d/G/n/activeAxes/roleRows/payloadWidth inputs.

- `Machine/CompactGadgetReservationHeadersCore.lean`: A fixed canonical-bank compiler physically executes products, differences, rounding, powers, constants and erasure through one fifteen-tape shared private bank. Static slot commands do not encode runtime values in finite control.

- `Machine/CompactGadgetReservationHeadersPowerRound.lean`: Paid fixed-base power and rounded-multiple commands construct actual canonical descriptor words and retain original source descriptors with private cleanup.

- `Machine/CompactGadgetReservationHeadersWords.lean`: Literal forty-tape bank words identify original inputs, the four surviving P/G/B/w outputs, erased intermediate descriptors and blank shared scratch.

- `Machine/CompactGadgetReservationHeadersOps.lean`: Physical original-input command rules discharge exact tape readiness, output words, source retention and cost for every arithmetic/erasure command in the reservation schedule.

- `Machine/CompactGadgetReservationHeadersSchedule.lean`: One fixed thirty-two-command forty-tape schedule physically computes all concrete reserved-slot P/G/B/w headers from seven canonical originals, clears fourteen intermediate descriptors and all fifteen shared scratch tapes, and proves its full paid runtime. RoleRows is a supplied original child-boundary descriptor; synthesis from original R/static role count remains separate.

- `Machine/CompactGadgetReservationHeadersEndpoint.lean`: The generated P/G/B/w tapes satisfy the actual original-header load Sources contract with canonical words and exact geometry values. Original seven descriptors remain unchanged, fourteen intermediates and fifteen private tapes are blank. Upstream role-row synthesis and whole reserve/load sequencing remain separate.

- `Machine/BinaryCorrectionOffsetData.lean`: Literal selected/control operand streams and independently reset modular subtraction rows for early correction offsets; specifies exact lengths and per-address words.

- `Machine/BinaryCorrectionOffsetGather.lean`: Executes the original-header control gather over the physically generated address source, with exact consumed-prefix lengths and retained source/control words.

- `Machine/BinaryCorrectionOffsetRewind.lean`: Physically rewinds exactly the source prefix read by control gather while retaining its unread tail, with all return transitions charged.

- `Machine/BinaryCorrectionOffsetPrepare.lean`: Places actual gathers and runtime nq synthesis into the shared correction bank from canonical original b/q/n and retained original control, preserving literal operand words for independent row subtraction.

- `Machine/BinaryCorrectionOffsetValue.lean`: Each correction row is the packed original control minus packed two-times-control-times-source digits modulo the target power of two. Uses the actual rowwise subtraction output; no borrow crosses address boundaries.

- `Machine/BinaryCorrectionOffsetFinish.lean`: Physically erases every remaining descriptor and generated source/control word, including the unread source suffix, and restores original heads after correction subtraction.

- `Machine/BinaryCorrectionOffset.lean`: Complete fixed thirty-one-tape early-correction constructor from original b/q/n and control. Output14 holds every address correction; all other twenty-six generated/private slots are blank. Cost at most(selectedBaseConstant+1000)*2^(n*b)*(n+1)*(q+b+1). Full repetition and action composition remain separate.

- `Machine/BinaryCorrectionOffsetPlaced.lean`: Places the complete original-input correction producer on five caller ports with twenty-six appended private tapes, preserving arbitrary larger-alphabet spectators and literal output words with identical paid runtime.

- `Machine/BinaryCorrectionOffsetRepeatData.lean`: Literal repeated independently subtracted correction rows, with spectators and dirty-back coordinates repeating the source-address word.

- `Machine/BinaryCorrectionOffsetRepeatConstruct.lean`: Fixed fifty-tape constructor synthesizes nq,2^nb and P*H*2^nq from original descriptors, builds the actual correction table, physically repeats it, and erases generated metadata while retaining original control.

- `Machine/BinaryCorrectionOffsetRepeatBudget.lean`: Pays all correction table construction, repetition and erasure in actual full rotation volume, with constant selectedRepeatConstant+1000 and an explicit record-width allowance.

- `Machine/BinaryCorrectionOffsetRepeatCoordinates.lean`: Exact physical row alignment for every source address, spectator and dirty-back value. Signed field value is packed z*(1-2*w) modulo2^nq; full output length and exact modular row value are proved.

- `Machine/BinaryCorrectionOffsetRepeatAlphabet.lean`: Lifts the complete repeated correction constructor to arbitrary larger alphabets with literal output, retained original inputs and identical runtime.

- `Machine/BinaryCorrectionOffsetRepeatPlaced.lean`: Eight shared caller ports for b/q/n/P/H/L/control/output, with forty-two private tapes appended and returned blank. Proves exact signed correction words, spectator retention and paid volume bound.

- `Machine/BinaryPackedOffsetOriginalPlaced.lean`: Places the actual original-header packed action on six arbitrary caller tapes with blank appended workspace. Executes count preparation, both physical interchanges, payload rotation and cleanup internally; exact output and every spectator head/tape are retained.

- `Machine/BinaryParityOffsetLoad.lean`: One fixed shared-bank machine physically generates repeated parity offsets from original q/b/n/P/H/L, executes the real swap/rotate/swap with the supplied physical action shape headers, and erases the generated offset word. No offset word or action Hoare premise is supplied. Exact payload permutation, restored original inputs and all private storage blank are proved; upstream reservation shape synthesis remains separate.

- `Machine/BinarySelectedOffsetLoad.lean`: One fixed shared-bank machine physically generates selected offsets from original b/q/n/P/H/L and retained control, invokes the actual original-header packed action and erases its offsets. Exact selected front-field permutation and clean private endpoint include zero digits; supplied physical action shape headers are explicit, and upstream reservation wiring remains separate.

- `Machine/BinaryCorrectionOffsetLoad.lean`: One fixed shared-bank machine generates actual repeated early-correction offsets from original descriptors and control, executes the real original-header packed action, and erases its offsets. Exact correction permutation, unchanged caller originals and blank private endpoint are proved without a supplied offset/action oracle; reservation routing remains separate.

- `Machine/BinaryRepeatedOffsetLoadBudget.lean`: Complete parity/selected/correction/negative parity-XOR production-action-erasure cost preserves the certified interchange width exponent. Physically generated table costs and full offset erasure are absorbed into actual payload volume when the explicit producer allowance fits suffix width; every join and cleanup is charged.

- `Machine/CompactGadgetReservationHeadersDivision.lean`: Physical fixed divisor command computes the canonical role quotient on the shared descriptor bank, preserves its sources and clears its fifteen-tape private work. Divisor is the static role count.

- `Machine/CompactGadgetReservationHeadersRows.lean`: Actual original-R to paddedRows(R,c)/c synthesis on arbitrary permanent caller ports. Initializes staticc, roundsR, divides, erasesc and roundedR, preserves originalR and all caller frame, and returns fifteen private tapes blank. Full cost at most(RecursiveRowsQuotient.constant c+4106)*(c+1)*R for positive original rows.

- `Machine/CompactGadgetReservationHeadersAssembled.lean`: Actual reservation followed by the real selected-role load, with load source/offset contracts proved internally from literal canonical supplied originals; no hload Hoare callback. Synthesized role-count/header placement into this reservation caller remains separate.

- `Machine/BinaryParityXorOffsetRow.lean`: Physically copies one runtime-width source row into blank scratch, executes real two-complement negation from fresh state, erases row scratch and preserves the exact modular negative value. No state or carry crosses row boundaries.

- `Machine/BinaryParityXorOffsetLoop.lean`: Fixed counted traversal independently negates every packed offset row, with exact concatenated outputs, consumed source advancement and reusable row scratch; all joins and countdown transitions are charged.

- `Machine/BinaryParityXorOffsetNegate.lean`: Complete fixed seven-tape row-negation constructor from original canonical width/count and literal packed input. Physically initializes/clears clocks, erases consumed input, rewinds output and restores all private storage; bound120*N*(W+1) for positive count. Original-address parity-XOR operand construction and repetition remain separate.

- `Machine/BinaryParityXorOffsetData.lean`: Literal per-address parity-XOR rows and independently negated output words, specifying the fourth early-source correction with exact widths and total lengths.

- `Machine/BinaryParityXorOffsetPositive.lean`: Proves original-address parity-XOR row semantics with retained original control, identifying the positive packed parity/control XOR operand before physical negation.

- `Machine/BinaryParityXorOffsetValue.lean`: Exact fourth-offset integer value is negative packed parity-XOR modulo2^(n*b); bridges actual independent row negation to the required modular arithmetic.

- `Machine/BinaryParityXorOffsetGather.lean`: Actual original-header parity-XOR gather consumes the generated address source and original-control repetitions, with exact resulting words and paid runtime.

- `Machine/BinaryParityXorOffsetPrepare.lean`: Physically constructs and gathers original-input operands, synthesizes runtime target width and positions source/output heads for counted per-row negation.

- `Machine/BinaryParityXorOffsetFinish.lean`: Physically clears all generated address/control words and metadata, including complete source tails, while retaining original headers/control and the negative offset output.

- `Machine/BinaryParityXorOffset.lean`: Complete fixed thirty-one-tape fourth-offset constructor from original q/b/n and control. Output14 holds exact negative packed parity-XOR offsets; all twenty-six private tapes are blank. Paid cost at most(selectedBaseConstant+1000)*2^(n*q)*(n+1)*(q+b+1).

- `Machine/BinaryParityXorOffsetPlaced.lean`: Five arbitrary larger-alphabet caller ports q/b/n/control/output with twenty-six blank private tapes appended and restored. Exact output word and every caller spectator/head are preserved.

- `Machine/BinaryParityXorOffsetRepeatData.lean`: Literal negative parity-XOR rows, spectator expansion and repetition preserve the actual source-address order.

- `Machine/BinaryParityXorOffsetRepeatConstruct.lean`: Fixed fifty-tape constructor synthesizes nb,2^nq and P*H*2^nb from original inputs, builds actual negative parity-XOR offsets, repeats them and erases generated metadata while retaining control.

- `Machine/BinaryParityXorOffsetRepeatBudget.lean`: Complete fourth-offset table construction, repetition and cleanup fit actual payload volume with an explicit suffix-width allowance; all physical setup and joins are charged.

- `Machine/BinaryParityXorOffsetRepeatCoordinates.lean`: Exact negative packed parity-XOR at every selected source address, repeated independently of spectators and dirty-back coordinates. The physical row ordering and literal full word length are proved.

- `Machine/BinaryParityXorOffsetRepeatAlphabet.lean`: Complete fourth-offset repetition on arbitrary larger alphabets, retaining literal outputs and original inputs with unchanged paid runtime.

- `Machine/BinaryParityXorOffsetRepeatPlaced.lean`: Eight shared caller ports q/b/n/P/H/L/control/output and forty-two appended private tapes restored blank. Exact negative-offset field semantics and volume bound are proved.

- `Machine/CountedTapeRepairCleanupWord.lean`: Actual marked/unmarked word erasure and physical return primitives remove sentinels as well as data, with literal endpoints and paid transition counts.

- `Machine/CountedTapeRepairCleanupAt.lean`: Places physical erase/return operations on selected repair-stage tapes, preserving complementary tapes and restoring erased heads.

- `Machine/CountedTapeRepairCleanup.lean`: Fixed fourteen-slot final cleanup schedule erases stage/key/counter words and sentinels while returning preserved source/output heads to origin.

- `Machine/CountedTapeRepairCleanupRun.lean`: Concrete cleanup of actual early scan/sort/reinsert endpoint leaves ideal output10 and source11 at origin, every other first-fourteen tape blank, and retained twenty-eight key scratch tapes.

- `Machine/CountedTapeRepairBudget.lean`: Uniform record-width and exceptional-count bound for the complete early repair execution including all final cleanup; exact full cost is at most base+badCount*coefficient.

- `Machine/CountedTapeRepairDensity.lean`: Actual early exceptional count is bounded by rho*M with rho=n/2^b+8*n*2^b/2^q; the paid full repair cost obeys the corresponding density bound.

- `Machine/CountedTapeRepairEndpoint.lean`: One fixed forty-two-tape original-input early repair plus final cleanup has exact ideal output and retained original source at origin, blank stage/key/counter work and unchanged key scratch. Later-gadget repair remains separate.

- `Machine/CountedTapeRepairLinear.lean`: Absorbs early exceptional density into full record volume under explicit record-width/setup/density inequalities, paying all preparation, key scans, sorting, reinsertion and cleanup. Later-gadget inverse/guard/key/pipeline execution remains unproved.

- `Machine/CompactGadgetReservationHeadersRouting.lean`: Fixed routing shares the actual fifteen-tape header workspace across original-R row synthesis and header construction, while retaining arbitrary caller spectators.

- `Machine/CompactGadgetReservationHeadersCaller.lean`: One fixed machine derives padded roleRows from originalR, synthesizes P/G/B/w, and executes the actual packed load on arbitrary retained spectators. No supplied derived shape words or action Hoare premise; the offset word remains a physical input.

- `Machine/CompactGadgetReservationHeadersReserved.lean`: Specializes synthesized-header execution to the actual reservation endpoint, reading retained originalR and acting on the actual selected role tape. Other roles and originals are retained; payload contract is discharged internally.

- `Machine/CompactGadgetReservationHeadersCost.lean`: Uniform physical header opcode/list cost charges arithmetic and descriptor erasure to a bound on actual stored values and canonical word lengths.

- `Machine/CompactGadgetReservationHeadersVolume.lean`: All thirty-two header commands are proved to stay within actual role volume. Complete header preparation costs at most32*(4196+fixedBasePowerConstant2)*roleVolume.

- `Machine/CompactGadgetReservationHeadersBudget.lean`: Entire original-R row synthesis, reservation shape preparation and actual load preserve the certified width exponent with constant depending only static role count; no extra chunk-size factor. Width is n*globalGuard; distinct narrower packed widths and generated-offset reservation routing remain separate.

- `Machine/CountedLateRepairInverse.lean`: Fixed twenty-eight-tape reverse eight-stage later packed arithmetic machine reads original runtime headers/control, restores an unconditional true packedLate preimage and erases parity/arithmetic/header scratch. Unrestricted word/value semantics and cost7000*(n+1)*(q+b+1) are proved; later guard, destination key and full repair pipeline remain separate.

- `Machine/CompactGadgetReservationHeadersCarvedData.lean`: General carved-width geometry keeps one fixed globalShape/H/layout while selecting n*packingFactor front/back bits; unused interval bits remain literal spectators. Simultaneous n*b/n*q capacities and disjoint slots are proved.

- `Machine/CompactGadgetReservationHeadersCarvedSchedule.lean`: One fixed actual header schedule physically reads original n/packingFactor, constructs width n*packingFactor and exact P/G/B descriptors inside the unchanged global reservation, with generated intermediate cleanup.

- `Machine/CompactGadgetReservationHeadersCarvedRouting.lean`: Shared-bank placement of narrow-width construction and original-R role-count synthesis retains all original global descriptors and caller spectators.

- `Machine/CompactGadgetReservationHeadersCarvedCaller.lean`: Fixed original-R and original packing-factor caller derives actual roleRows/width/P/G/B and invokes the real packed load. Same finite program for b and q; no derived shape words or action callback supplied.

- `Machine/CompactGadgetReservationHeadersCarvedReserved.lean`: Actual selected-role load from the physical reservation endpoint supports both narrower packed widths inside the same global layout; retains unused bits and every other role. Physical offset word remains explicit; producer alignment and whole reservation-stage composition remain separate.

- `Machine/CompactGadgetReservationHeadersCarvedVolume.lean`: All real row/header/width setup values and products are bounded within actual role volume, including n*packingFactor product preparation.

- `Machine/CompactGadgetReservationHeadersCarvedBudget.lean`: Full actual carved-width row synthesis, header setup, load and cleanup preserve the certified width exponent with C(staticRoleCount)*roleVolume and no extra chunk factor. Source-prefix/gap offset-generator wiring remains separate.

- `Machine/BinaryParityXorOffsetLoad.lean`: Complete fixed shared-bank fourth-offset generation, actual original-header swap/rotate/swap and physical offset erasure, with exact negative parity-XOR destination semantics and blank private return. Physical action shape inputs are explicit; final source-prefix placement into the common early reservation remains separate.

- `Machine/PackedPrefixRepeatHeaders.lean`: Physically derives L=2^(d*globalGuard-n*q)*2^(n*b)*actualGap from canonical original d/globalGuard/n/q/b and paid upstream gap/role-row words, retaining K=roleRows. Fixed fifteen-command forty-tape schedule clears every intermediate and private tape; actual post-use L erasure restores the original bank. Full exact setup/cleanup costs are proved; placement and volume absorption into the final prefix repeat remain separate.

- `Machine/CompactPackedSourceGeometry.lean`: Exact serialized source extraction and actual rotation-row alignment for source fields in either gap or prefix. Generic physically repeated words select precisely that source address while all dirty-back, prefix-tail and gap spectators survive; no free coordinate move or tape execution is asserted.

- `Machine/BinaryPackedEarlyData.lean`: Actual selected/parity/signed-correction/negative row-word translations compose in current-source order to packedEarly. On good addresses, the target is the ideal toggle and temporary value restores, with arbitrary spectators unchanged. Physical common-bank execution remains separate.

- `Machine/BinaryPackedEarlyLayout.lean`: Serializes the mixed n*q/n*b target/temp fields, all unused fixed-H tails, active/slack fields, full dirty back and payload into exactly rows*globalShape.recordWidth. Establishes one unchanged common early address layout; machine assembly remains separate.

- `Machine/BinaryPackedEarlyPrefixHeaders.lean`: Physically derives prefix-source repeat width and source range from original q/b/n with paid setup and complete metadata erasure. The upstream L/K ports retain their literal marked words.

- `Machine/BinaryPackedEarlyPrefixNegative.lean`: Fixed fifty-tape prefix-source negative parity-XOR constructor runs the actual base offset producer, inner/outer repetition and full cleanup. Exact output keeps the original q/b/n/L/K/control words; source spectators retain their real row order.

- `Machine/BinaryPackedEarlyPrefixParity.lean`: Fixed fifty-tape prefix-source parity constructor composes physical base generation, actual repetition and erasure, restoring all private storage while retaining original descriptors.

- `Machine/BinaryPackedEarlyPrefixBudget.lean`: All prefix-source base production, nested repetition and cleanup costs are absorbed into explicit full payload volume with a sufficient suffix record-width allowance. No repetition or setup cost is omitted.

- `Machine/BinaryPackedEarlyPrefixAction.lean`: Both physically repeated prefix-source offset words select the correct current source address in actual rotation-row order. Parity and negative parity-XOR entries preserve the dirty back, prefix tail and gap spectators.

- `Machine/BinaryPackedEarlyPrefixAlphabet.lean`: Lifts both complete prefix-source constructors to larger alphabets with identical costs and literal clean output banks.

- `Machine/BinaryPackedEarlyPrefixPlaced.lean`: Actual arbitrary seven-port caller placement retains q/b/n/L/K/control and returns the generated parity or negative parity-XOR offset word with all forty-three appended private tapes blank. Actual payload actions and post-use offset erasure remain separate.

- `Machine/PackedPrefixRepeatHeadersPlaced.lean`: Places the paid repetition-factor construction and actual L erasure on eight arbitrary caller ports. Preserves all caller spectators and the seven original descriptors, retains K on its upstream port and restores all forty native workspace tapes. Volume absorption and composition into the full load remain separate.

- `Machine/CompactGadgetReservationHeadersCarvedReservationRouting.lean`: Routes the actual original-array pad/split/erase endpoint directly into synthesized carved-width reserved load setup. Retains original descriptors and every reservation spectator without assuming a supplied reservation-final bank.

- `Machine/CompactGadgetReservationHeadersCarvedEndToEnd.lean`: Actual original-array padding, role splitting, carved-header setup and reserved load have exact payload semantics and a certified width-exponent bound including every join and cleanup. Only the explicit physical offset word remains to be connected to its generator; derived role/load headers remain retained for reuse.

- `Machine/BinaryPackedEarlyGeometry.lean`: Both carved temp/control rectangle ordinals equal one unchanged serialized reservation index, including arbitrary dirty-back splits and every unused field. These are array geometry lemmas; physical sequence assembly remains separate.

- `Machine/BinaryPackedEarlyAddress.lean`: The common mixed-width address serialization is bijective onto the full role volume, covering every dirty back, slack, active and payload cell without a free permutation.

- `Machine/BinaryPackedEarlyArray.lean`: The four literal actual packed-offset result functions compose in current-source order on one unchanged global layout. Exact array entries agree with the four-stage state update; physical sequencing remains separate.

- `Machine/BinaryPackedEarlyCorrect.lean`: Every serialized array cell satisfies packedEarly semantics, and good addresses have the ideal selected target toggle with temporary/spectator restoration. These full-array correctness lemmas do not assert execution of the complete physical sequence.

- `Machine/BinaryPackedEarlyPrefixParityLoad.lean`: One fixed child machine constructs prefix-source parity offsets, executes the actual original-header swap/rotate/swap and erases the entire offset word. Original q/b/n/L/K, action headers and all spectators are retained with private storage blank; upstream header wiring remains separate.

- `Machine/BinaryPackedEarlyPrefixNegativeLoad.lean`: One fixed child machine constructs prefix-source negative parity-XOR offsets, executes the actual original-header field action and physically erases the offsets. Original controls/descriptors and all spectator tapes survive; complete shared-sequence wiring remains separate.

- `Machine/BinaryPackedEarlyPrefixLoadBudget.lean`: Both prefix-source generation/action/erasure machines preserve the certified width exponent with actual payload volume and an explicit sufficient suffix-width allowance. Every preparation, join and cleanup cost is charged.

- `Machine/PackedPrefixRepeatHeadersBudget.lean`: The actual fifteen-command repetition-factor setup and physical final erasure have linear containing-volume bounds. All intermediate powers/products are charged and bounded by the actual repetition factor.

- `Machine/PackedPrefixRepeatHeadersReserved.lean`: Discharges the repetition-factor volume inequalities from the actual unchanged reservation geometry and carved control gap. Arbitrary-caller construction and real cleanup have uniform full-role-volume costs without supplied cost bounds.

- `Machine/PackedEarlyRepeatHeaders.lean`: One fixed forty-tape fourteen-command schedule constructs both gap-source preceding and prefix-source repetition factors from original d/globalGuard/n/q/b and paid control-gap/row words, then erases every other intermediate. The actual two-factor cleanup restores the original bank; exact gap factorization connects both source orders without moving cells.

- `Machine/PackedEarlyRepeatHeadersPlaced.lean`: Both physically generated early repetition factors share nine arbitrary caller ports with the seven retained original descriptors. Real construction and post-use two-word erasure preserve all caller spectators and restore every native workspace tape; final reservation caller placement remains separate.

- `Machine/PackedEarlyRepeatHeadersBudget.lean`: Shared two-factor construction and physical cleanup cost at most14 and2 header coefficients times the actual complete reserved role volume. All powers and products fit by the actual geometry and carved-width capacities; no setup-cost premise or supplied repetition factor is assumed.

- `Machine/BinaryPackedEarlyRunBank.lean`: Fixed eighteen-port caller bank with both actual shape header sets, original q/b/n/control/rows and repeated-source factors. All four child loads share one blank fixed workspace and preserve the unchanged serialized reservation.

- `Machine/BinaryPackedEarlyRunGap.lean`: Both gap-source early loads physically execute their original-input selected/correction producers, actual packed actions and offset erasure on the same caller bank. Literal casts identify the common array word without a data move.

- `Machine/BinaryPackedEarlyRunPrefix.lean`: Both prefix-source early loads physically execute their original-input parity/negative producers, actual packed actions and offset erasure on the same caller bank with all spectators retained.

- `Machine/BinaryPackedEarlyRun.lean`: One actual fixed four-load sequence executes the complete early packed array permutation on the unchanged reserved word, retaining original descriptors/control and restoring all private workspace. Exact output is BinaryPackedEarlyArray.run, with all four child costs and three joins paid. Shape/repetition words are still explicit upstream interfaces.

- `Machine/BinaryPackedEarlyRunBudget.lean`: The actual four-load sequence preserves the certified width exponent with full reserved role volume and explicit sufficient record-width allowances for both suffixes. No child setup, cleanup or sequencing charge is omitted.

- `Machine/PackedEarlyRepeatHeadersCaller.lean`: Original row and packing descriptors physically construct the carved control gap and role-row count, then feed both early repetition factors on their actual caller ports. Exact combined execution and charged setup bound need no supplied gap/row/repetition word; placement into the final four-load sequence remains separate.

- `Machine/CountedLateRankBank.lean`: Native thirteen-tape short-rank splitter bank keeps the actual counter, original q/b/n and arbitrary destination exteriors, using blank-backed zero extension rather than a supplied padded counter.

- `Machine/CountedLateRankRun.lean`: Actual fixed-control split extracts target V of width n*q and both W/U source fields of width n*b, restores heads and erases split scratch with a fully charged runtime.

- `Machine/CountedLateRankEndpoint.lean`: Clean original-header later rank splitter has exact V/W/U words and a uniform600-times-full-stride bound, preserving original counter and destination spectators.

- `Machine/CountedLateRepairFlag.lean`: Physical later exceptional comparisons on original V/W and V/U words produce exact individual flags and erase all comparison scratch.

- `Machine/CountedLateRepairGuard.lean`: Fixed thirty-tape later exceptional guard physically ORs both flags, erases the second flag and decides exactly the lateGood complement within2004 times full stride.

- `Machine/CountedLateRepairPrefix.lean`: Actual original-input later guard and unrestricted packed inverse compose with exact retained flag/recovered V/W/U words and paid9005-times-full-stride cost.

- `Machine/CountedLateRepairToggle.lean`: Fixed thirty-one-tape ideal toggle uses the actual recovered target/control and preserves the original exceptional flag and dirty source words with paid533-times-full-stride cost.

- `Machine/CountedLateRepairConcat.lean`: Actual W/U destination concatenation returns the exact combined source word and restores all heads within3 times the combined lengths plus10.

- `Machine/CountedLateRepairKeyBank.lean`: Fixed thirty-four-tape later key bank and physical placements for actual rank splitting, guard/inverse/toggle and W/U concatenation.

- `Machine/CountedLateRepairKeyPrefix.lean`: Original-input later guard, inverse, toggle and source concatenation compose with exact full-bank endpoints and all joins paid.

- `Machine/CountedLateRepairKeyWrite.lean`: Actual conditional later key writer emits the exceptional flag and, only when flagged, the exact recovered/toggled destination words, with all source/key rewinds charged.

- `Machine/CountedLateRepairKeyCleanup.lean`: Physically erases all six generated later key words and restores complete scratch while retaining original counter/control/headers and the written key.

- `Machine/CountedLateRepairKeyRun.lean`: One fixed thirty-four-tape later key machine executes genuine short-rank splitting through conditional key writing and full cleanup from original runtime descriptors within10300 times full stride.

- `Machine/CountedLateRepairKeyValue.lean`: Actual later key flag and literal destination bits equal the later compact instance rankFlag/rankKey for every short scan counter.

- `Machine/CountedLateRepairScanBank.lean`: Physical placement of the actual thirty-four-tape later key inside the forty-six-tape repair scan bank, preserving every non-key scan tape.

- `Machine/CountedLateRepairScan.lean`: The real later key machine satisfies the full RepairScan.KeyContract with exact exceptional flags/destination keys, retained originals and reusable blank scratch.

- `Machine/CountedLateRepairMetadata.lean`: Actual original n*q/n*b products and counted replay construct the later selector/counter width n*q+2*n*b, erasing every generated product and clock.

- `Machine/CountedLateRepairPrepare.lean`: Fixed forty-six-tape later preparation physically creates all scan sentinels/selectors/counters from original q/b/n/control and blank workspace within2004 times full stride.

- `Machine/CountedLateTapeRepairBank.lean`: Literal original-input later repair bank and exact actual/ideal stream definitions, with distinct source/output and retained original key scratch.

- `Machine/CountedLateTapeRepairCleanupAt.lean`: Physical later repair head positioning and framed erasures preserve the source/output tapes and original key scratch.

- `Machine/CountedLateTapeRepairCleanup.lean`: Actual fourteen-stage later final cleanup erases every stage marker/work word and restores all stage heads.

- `Machine/CountedLateTapeRepairCleanupRun.lean`: Complete later physical cleanup returns only the ideal output and retained source at origin; all other stage tapes blank and original scratch retained.

- `Machine/CountedLateTapeRepairRun.lean`: Actual fixed original-input later preparation, keyed scan, radix sort, stripping and reinsertion produce the exact ideal stream with all stages and joins charged.

- `Machine/CountedLateTapeRepairBudget.lean`: Every later setup/key/sort/strip/reinsert/final-cleanup transition enters a complete runtime bound linear in volume plus exceptional count times the paid repair coefficient.

- `Machine/CountedLateTapeRepairDensity.lean`: Actual later exceptional-address count is bounded by the proved density and absorbed into the complete paid tape runtime expression.

- `Machine/CountedLateTapeRepairEndpoint.lean`: One reusable fixed forty-six-tape later repair machine executes the full initialized pipeline and final cleanup, returning the exact ideal output/source at head zero and restoring all workspace.

- `Machine/CountedLateTapeRepairLinear.lean`: Density absorption proves an actual Hoare execution bound(12304*C+228)*lateMi*(recordWidth+2), under explicit key-width, stride and small-density conditions. Together with the earlier endpoint, both repair pipelines now have full physical correctness and charged bounds.

- `Machine/CompactGadgetReservationHeadersCarvedPlaced.lean`: The actual carved-header schedule shares eleven arbitrary caller ports without copying original descriptors, preserves every spectator and restores forty private tapes. Exact P/G/B synthesis and full-volume setup cost hold for any compact carved width within the fixed reservation.

- `Machine/CompactGadgetReservationHeadersCarvedPlacedWidth.lean`: Physically multiplies original n and packing-factor words through three arbitrary caller ports with one shared forty-tape workspace, preserving originals and returning exact canonical width with full paid cost.

- `Machine/CompactGadgetReservationHeadersCarvedPlacedRun.lean`: Actual original packing factor and seven original shape descriptors generate width/P/G/B on distinct caller outputs with complete workspace restoration. Setup cost is at most(31*headerCoefficient+82)*roleVolume; compact-width capacity remains explicit.

- `Machine/CompactGadgetReservationHeadersCarvedPlacedCleanup.lean`: Four actual shape descriptors are physically erased after use, preserving every other caller tape/head. Exact cost2 times all descriptor lengths plus19 is bounded by35*roleVolume from the carved geometry.

- `Machine/BinaryDescriptorCopyPlaced.lean`: Actual marked descriptor duplication reads caller source at head one and blank destination at head zero, returns both words at head one and frames every other caller tape/head. No supplied duplicate word or workspace copy is assumed; cost2*length+5.

- `Machine/BinaryPackedEarlyRunPlaced.lean`: The complete certified front-target early kernel executes on eighteen arbitrary caller ports and changes only the payload, retaining every descriptor/control/spectator and restoring all native workspace. This retains the existing explicit target-width capacity and fixed-source-control premises; it is not the active-target algorithm assembly.

- `Machine/PackedEarlyHeaderCleanup.lean`: Actual twelve-descriptor sequential cleanup restores the exact initial bank and frames all originals at paid108 times containing volume. The explicit derived-word family is the existing front-target kernel header family; applying it to selected-algorithm metadata remains separate.

- `Machine/ActiveTargetRotation.lean`: A direct actual caller-owned active-target rotation retains original prefix/suffix/width descriptors, packed offsets and all spectators with twelve private tapes blank. Full destination semantics and a uniform linear-volume bound hold for every target width, without target interchanges or front-capacity premises. Offset production remains an explicit physical stage input.

- `Machine/BinaryPackedLateData.lean`: Actual late row-word arithmetic composes early, dirty-control load, early and unload with exact unrestricted packedLate values and unconditional dirty-control restoration. Guarded ideal toggling and arbitrary spectator preservation are proved; varying-prefix offset tables and active-target physical assembly remain separate.

- `Machine/CompactActiveTargetLayout.lean`: Exact full-volume address bijection places the wide target inside active coordinates, with compact U/T fields, all dirty tails, active spectators, back and payload independent. Only compact width fits H; no target-capacity premise or target move is assumed.

- `Machine/CompactActiveTargetGeometry.lean`: Literal active-target rotation fibers and both compact interchange rectangles equal the original unchanged array ordinal. Carved descriptor shapes, real source-prefix factors and the common back-rotation prefix are proved; physical varying-offset production and whole schedule remain separate.

- `Machine/SelectedSourceBitsData.lean`: Least-significant-first source-bit selection has exact length and testBit semantics at rho+i*q, including zero selected digits and the source-span bounds.

- `Machine/SelectedSourceBitsCore.lean`: Actual source-bit copy and runtime-q counted head movement retain arbitrary source cells and append exactly one physical selected bit with charged cost.

- `Machine/SelectedSourceBitsBank.lean`: Three independent countdown clocks are physically initialized and erased on the exact original-header source/output bank, retaining originals and restoring all clock cells and heads.

- `Machine/SelectedSourceBitsScan.lean`: Actual runtime-rho positioning followed by the runtime-n sampling loop returns the exact selected source word, preserving complete source cells without requiring interior blanks.

- `Machine/SelectedSourceBitsRewind.lean`: Physical source and selected-output rewinds restore both heads from actual scan endpoints, retaining full words and exterior cells with charged source-span cost.

- `Machine/SelectedSourceBitsRun.lean`: One fixed extraction machine reads the full f*q-bit original source and q/n/rho/f descriptors, returns exactly n selected source bits, retains originals and restores every private clock. Actual cost at most400 times original source length includes all positioning, scans, rewinds and cleanup.

- `Machine/SelectedSourceBitsPlaced.lean`: Complete extraction on six injective caller ports preserves all complementary tapes and heads and restores nine appended private tapes. Output controls are physically derived from the full source address, with exact testBit semantics and400-times-source-length cost.

- `Machine/BinaryVaryingSelectedOffsetGather.lean`: One fixed mask-shift gather reads a literal source-digit stream and independently varying controls using sole original q/b/count descriptors. Actual derived-header construction, scan and cleanup restore fourteen private tapes; output length and full320-times-stride cost are proved. Source/control stream generation and final head returns remain separate.

- `Machine/BinaryVaryingSelectedOffsetData.lean`: Each physically gathered offset row equals mask-shift arithmetic applied to that row’s current source digits and controls. Arbitrary varying rows have exact widths and order; there is no fixed-control repetition hypothesis.

- `Machine/ActiveTargetSubsegmentAddress.lean`: Early/later guarded packed kernels lift to the actual full active-target Address, changing only target while restoring both dirty compact fields and every other source, spectator, back and payload coordinate. This is a mathematical destination bridge; physical stage and repair assembly remain separate.

- `Machine/SelectedSourceBitsStreamData.lean`: Literal per-source-row selected controls have exact P*n length and full-stream testBit positions r*(f*q)+rho+i*q, with all selected positions proved inside the source stream.

- `Machine/SelectedSourceBitsStreamCore.lean`: Physical runtime-rho backward positioning retains arbitrary stream cells and provides exact paid head movements for advancing between full source rows.

- `Machine/SelectedSourceBitsStreamBank.lean`: Four independent original-header countdown clocks are physically initialized and erased, retaining q/n/rho/f/P and restoring all private cells and heads.

- `Machine/SelectedSourceBitsStreamRow.lean`: One actual row positions by rho, samples n selected bits with runtime-q movements and reaches the next full f*q-row boundary. Complete stream contents are retained, with no temporary row copy or supplied selected controls.

- `Machine/SelectedSourceBitsStreamRun.lean`: One fixed batch extractor physically enumerates all P original source rows, returns P*n exact selected controls at origin and restores source/head/originals and every private clock. Cost400*(sourceStream.length+1) includes empty batches, scans, all head returns and cleanup.

- `Machine/SelectedSourceBitsStreamPlaced.lean`: Complete batch extraction on seven arbitrary caller ports retains source/original descriptors and every spectator, restores eleven appended private tapes and returns the literal varying control stream at origin with400-times-stream-plus-one cost.

- `Machine/BinaryVaryingControlOffsetGather.lean`: A fixed original-q/b/count machine physically builds stride-q control offsets from independently varying controls, retaining source/control words and all originals. Fourteen private tapes are constructed and erased; complete cost320 times full stride and exact output length hold. Full control-stream generation and final head returns remain separate.

- `Machine/BinaryVaryingControlOffsetData.lean`: Each physical control-offset row equals its own stride-q toggle mask and has exact packed control value. These varying masks and selected offsets supply the existing rowwise correction subtraction without any whole-stream fixed-source premise.

- `Machine/BinaryPrefixFieldTableData.lean`: Literal runtime field projection from every full-width address has exact row-major order, lengths and individual fields, including zero-width addresses/fields.

- `Machine/BinaryPrefixFieldTablePrimitives.lean`: Actual generated range/count, zero descriptor, descriptor duplication, address table and dummy-control fill share a framed original-header bank with charged execution.

- `Machine/BinaryPrefixFieldTableSetup.lean`: From sole W/start/d originals, physically generates the complete prefix-address table, 2^W dummy controls and every required derived descriptor; all individual setup costs are charged.

- `Machine/BinaryPrefixFieldTableGather.lean`: The runtime counted gather physically projects each original address field in order and restores all internal gather metadata; exact projected word is proved.

- `Machine/BinaryPrefixFieldTableCleanup.lean`: Physically erases generated address/control tables and count/zero/copy descriptors, rewinds projected output and retains all three originals with paid cost.

- `Machine/BinaryPrefixFieldTableRun.lean`: One fixed original-input field-table producer generates and erases all intermediate streams and returns exact projected fields at origin. Full cost at most(powerConstant+addressTableConstant+1000)*2^W*(W+1), including W/d zero.

- `Machine/BinaryPrefixFieldTableAlphabet.lean`: Checked literal field-table construction is encoded on arbitrary larger alphabets without changing runtime, source order, restored originals or blank native workspace.

- `Machine/BinaryPrefixFieldTablePlaced.lean`: Actual projected-field table generation on four arbitrary caller ports requires only canonical W/start/d and blank output, retains every spectator and restores twenty-four private tapes. Exact row words and full linear table cost are proved.

- `Machine/BinaryVaryingParityOffsetGather.lean`: Actual parity-XOR gather reads current target digits and independently varying controls with only original q/b/count descriptors. Exact positive fourth-load word, preserved original streams and blank fourteen private tapes have full320-times-stride cost; rowwise negative residues and complete load assembly remain separate.

- `Machine/BinaryVaryingOffsetGatherPlaced.lean`: All selected/control-mask/parity-XOR runtime gathers execute on six arbitrary caller ports, preserving all original header/stream contents and every complementary tape. Exact source/control/output heads and literal output follow the actual native machine; twenty private tapes are restored with unchanged320-times-stride bound.

- `Machine/ActivePrefixSelectedOffsetData.lean`: Physically projected full-source rows and batch-extracted controls agree with selected testBits of each original prefix address. The varying selected gather therefore uses each current temporary/source field in the unchanged prefix, with exact offsets and row order; physical producer assembly remains separate.

- `Machine/ActivePrefixOffsetHeadersData.lean`: Original W/q/b/n/f descriptors have explicit source/destination port maps for P,f*q,n*b,n*P,n*q, with exact generated value families and full source/temp fit premises.

- `Machine/ActivePrefixOffsetHeadersRun.lean`: One real power and four physical products synthesize all five varying-offset descriptors on arbitrary caller ports, retaining originals/spectators and restoring fifteen shared private tapes. No supplied derived descriptor is assumed.

- `Machine/ActivePrefixOffsetHeadersBudget.lean`: Every actual header-setup transition is bounded by(powerConstant+328)*2^W*(W+1) under source/temp fit and n+1=f. Applies to the actual caller machine, not a semantic arithmetic cost.

- `Machine/ActivePrefixOffsetHeadersCleanup.lean`: Five generated prefix-offset descriptors are physically erased on arbitrary caller ports, preserving all original tapes and restoring output heads. Complete cleanup is paid by44*2^W*(W+1).

- `Machine/ActiveTargetHighestRun.lean`: A fixed tracked physical coefficient-one shift executes the highest selected one-bit toggle from an earlier source-address bit, retaining six supplied canonical descriptors and returning the exact array at origin. All private and tracking tapes are blank; complete cost137575*volume, with no offset table or target front-capacity premise.

- `Machine/ActiveTargetHighestValue.lean`: Exact full-array transport of the actual highest-bit machine is target XOR with the real earlier prefix bit, preserving all preceding/intervening/suffix coordinates. The combined realizes theorem includes actual execution, cleanup and linear bound; source-layout/header synthesis and later-source placement remain separate.

- `Machine/VaryingControlRepairFiber.lean`: Dependent source-address families of actual/ideal permutations retain their current source and every spectator through inverse and repair destinations. Full rank arithmetic is explicit; a separate original-layout bridge identifies physical ranks.

- `Machine/VaryingControlRepairPacked.lean`: Existing exact early/later packed permutations and repaired endpoints lift uniformly to controls Z(x) computed for each retained source address, with no one-fixed-control-word assumption across the stream.

- `Machine/VaryingControlRepairDensity.lean`: Explicit finite fiber sums bound total bad addresses and normalized exceptional density uniformly across varying source controls, including empty source and spectator ranges.

- `Machine/VaryingControlRepairKeys.lean`: Full varying-source flags and destination keys include source/local/spectator ranks. Arbitrary supplied physical-index equivalences preserve exact destination/key identities; actual runtime full-rank extraction and key assembly remain separate.

- `Machine/VaryingControlRepairLayoutRank.lean`: Actual unchanged active-layout ranks recover V/T/U and active-before/after coordinates exactly, including arbitrary payload suffix. Explicit source-slot offsets yield exact source-word/value recovery from genuine short counter values; no padded-counter input or physical rank parser is assumed.

- `Machine/ActivePrefixOffsetStreamsCleanup.lean`: Fixed thirteen-state caller-placed cleanup physically erases the temporary, full-source and varying-control streams and rewinds the retained offset output. Exact stream-length cost, empty cases and the complete complementary frame are proved; no private workspace is appended.

- `Machine/ActivePrefixSelectedOffsetBank.lean`: Defines the original eight-descriptor bank and shared prefix-field, source-extraction and selected-gather placements. Exact physical gathered output equals the canonical varying first-offset stream; original descriptors and complementary bank are retained.

- `Machine/ActivePrefixSelectedOffsetRun.lean`: One fixed forty-one-tape producer physically synthesizes all five derived headers, projects temporary and full-source fields from every prefix address, extracts current source controls and emits selected offsets. Every stage has actual tape semantics and charged runtime; cleanup is provided separately.

- `Machine/ActivePrefixSelectedOffsetCleanup.lean`: Physically erases all generated source/control streams and five derived descriptors after the selected gather. Exact final bank retains only the original eight descriptors and offset output at origin, with all twenty-four private tapes blank and every head restored.

- `Machine/ActivePrefixSelectedOffset.lean`: Complete fixed first-offset producer reads only eight original canonical descriptors, generates the exact varying-source offsets and clears all derived tables, headers and workspace. A uniform constant times two-to-W times W-plus-one bound includes every stage and cleanup. Arbitrary caller placement, repetition over original rows and active rotation composition remain separate.

- `Machine/ActiveRepairRankFieldsPosition.lean`: Fixed caller-placed runtime seek and restore operations traverse address fields from original canonical offsets, retaining all tape contents and erasing countdown scratch with exact charged costs.

- `Machine/ActiveRepairRankFieldsField.lean`: Physical runtime field extraction reads a genuine short rank word with zero fill beyond its blank tail, produces exactly the requested fixed-width address field, restores the rank and descriptors and clears private storage.

- `Machine/ActiveRepairRankFieldsPlaced.lean`: Places the actual short-rank field extractor on arbitrary caller ports, preserving the complementary frame and restoring all private tapes with the original exact cost.

- `Machine/ActiveRepairRankFieldsBank.lean`: Shared twenty-seven-tape repair parser bank retains the genuine short record counter, eight field descriptors and q/n/rho/f, while separately storing V/T/U, full source and selected source bits.

- `Machine/ActiveRepairRankFieldsRun.lean`: One fixed physical parser extracts V/T/U and the full source from the actual short rank, then runs actual source-bit selection. All originals and heads are retained, nine private tapes erased and cost bounded by1200 times address width plus one, plus four. Derived offset/width descriptor synthesis remains separate.

- `Machine/ActiveRepairRankFieldsGeometry.lean`: Recovers exact active-layout V/T/U and before/after source words from the original record ordinal, with payload width one for address ranks. Field geometry includes source/back/spectator bits without introducing a free physical reorder.

- `Machine/ActiveRepairRankFieldsEndpoint.lean`: Actual before/after-source repair parsing returns exact layout V/T/U, full source and selected controls from a genuine short original-rank counter. Supplied original canonical field offsets/widths are retained, private storage erased and the linear address-width bound is paid. Descriptor synthesis, inverse/guard calculation and full destination-key writing remain open.

- `Machine/ActivePrefixSelectedOffsetPlaced.lean`: Actual clean first-offset producer on arbitrary nine caller ports reads only the eight original canonical descriptors and blank output. Exact varying offsets at origin, all retained original/spectator tapes and forty-one blank private tapes are proved with unchanged linear prefix-table cost. Original-row repetition and direct active rotation composition remain separate.

- `Machine/ActivePrefixOffsetRepeatRun.lean`: One fixed four-tape machine physically repeats a generated base offset word using the original canonical row descriptor. An actual empty-source branch avoids per-row overhead for empty words. Exact repeated output, retained source/descriptor, erased clock and cost54 times repeated volume plus one include arbitrary rows, zero rows and empty input.

- `Machine/ActivePrefixOffsetRepeatAlphabet.lean`: Lifts the actual fixed row-repetition machine to any larger alphabet, preserving literal binary words, canonical descriptor, full workspace cleanup and the same runtime bound.

- `Machine/ActivePrefixOffsetRepeatPlaced.lean`: Clean repetition on arbitrary rows/base/output caller ports returns exactly the flattened original-row copies, retaining all original descriptors, source and spectators and erasing four private tapes. No power-of-two row assumption or supplied repetition table is needed.

- `Machine/ActiveRepairDestinationPatchOverwrite.lean`: Fixed five-tape runtime seek/copy/rewind physically overwrites one selected address field while retaining the replacement word, original offset/width descriptors, heads and every exterior bit. Exact charged time and a linear address-width bound are proved.

- `Machine/ActiveRepairDestinationPatchData.lean`: Literal same-width field replacement preserves every outside bit, installs the exact selected interval and commutes for disjoint intervals. Connects the actual overwrite tape to the resulting finite address word.

- `Machine/ActiveRepairDestinationPatchPlaced.lean`: Actual field overwrite on arbitrary caller replacement/destination/offset/width ports preserves the complementary bank and erases all nine shared private tapes, with exact physical runtime.

- `Machine/ActiveRepairDestinationPatchRun.lean`: One fixed twenty-one-tape machine zero-extends a genuine short rank counter to the runtime full address width, then physically replaces V/T/U at three runtime offsets. Original rank, replacement words, seven descriptors and all heads survive; nine private tapes are erased. Exact output and cost800 times address width plus one, plus three are proved.

- `Machine/ActiveRepairDestinationPatchGeometry.lean`: Encodes the unchanged active-layout rank including arbitrary rows, source/spectator bits, front slack, U/T tails and dirty back. With payload one and rows below the explicit row-bit capacity, the generated three-patch word is exactly the original physical index with V/T/U replaced.

- `Machine/ActiveRepairDestinationPatchEndpoint.lean`: Instantiates the actual fixed twenty-one-tape rank reconstruction at active target/T/U offsets and proves output equals the full fixed-width destination rank, retaining every spectator. Canonical runtime offsets/widths are supplied; physical synthesis of these headers, guard/inverse/toggle computation and conditional full-key composition remain open.

- `Machine/ActivePrefixControlOffsetData.lean`: The complete generated control-mask stream uses selected source bits of each actual prefix rank. Exact length and per-prefix toggleMask identity are proved; the auxiliary width-n projected source is only a paid physical clock.

- `Machine/ActivePrefixControlOffsetBank.lean`: Original eight-descriptor caller bank generates a width-n clock projection, full source projection and current source controls. Exact gathered bank equals the canonical control-mask offsets, retaining all original descriptors.

- `Machine/ActivePrefixControlOffsetRun.lean`: One fixed forty-one-tape machine physically constructs derived headers, both prefix projections, all varying controls and control-mask offsets from sole original descriptors. Every setup/extraction/gather stage has an actual charged contract.

- `Machine/ActivePrefixControlOffsetCleanup.lean`: Physically erases clock/source/control streams and all five generated descriptors after the control-mask gather, leaving only original descriptors and exact offsets at origin with all private tapes blank.

- `Machine/ActivePrefixControlOffset.lean`: Complete fixed varying control-mask producer, including actual source-address extraction and full metadata/stream cleanup, has a uniform constant times2^W*(W+1) bound. This supplies B for the B-minus-A correction; subtraction and payload rotation are separate.

- `Machine/ActivePrefixControlOffsetPlaced.lean`: Actual control-mask production on arbitrary original-eight-plus-output caller ports retains every descriptor and spectator and restores forty-one private tapes, with unchanged certified linear prefix-table runtime.

- `Machine/GatherStreamData.lean`: Generic Boolean gathers preserve uniform source/control row boundaries for independently varying rows. Exact per-row semantics and reconstruction from fixed-width fields include zero-width rows; no repeated-control premise is needed.

- `Machine/ActivePrefixParityOffsetData.lean`: Exact parity-XOR offsets use the current target field and source controls of each original prefix rank. Per-row identity, uniform width n*b, row count2^W and flatten equality connect the physical output to rowwise modular negation.

- `Machine/ActivePrefixParityOffsetBank.lean`: Original eight-descriptor bank physically projects the current n*q-bit target and full source fields, extracts varying controls and gathers positive parity-XOR offsets. Exact bank identity retains every original descriptor.

- `Machine/ActivePrefixParityOffsetRun.lean`: One fixed forty-one-tape producer shares actual original-header synthesis, target/source projections, source-bit extraction and parity-XOR gather, with complete charged stage contracts.

- `Machine/ActivePrefixParityOffsetCleanup.lean`: Physically erases projected target/source/control words and every derived descriptor after parity-XOR emission. Only original descriptors and output survive at origin, with all private storage blank and heads restored.

- `Machine/ActivePrefixParityOffset.lean`: Complete fixed positive parity-XOR producer runs from eight original canonical descriptors and erases all generated metadata and streams within a uniform constant times2^W*(W+1) bound. The actual negative compact load additionally requires rowwise modular negation and rotation.

- `Machine/ActivePrefixParityOffsetPlaced.lean`: Clean positive parity-XOR production on arbitrary nine caller ports preserves all original descriptors and spectators, restores forty-one private tapes and retains the complete linear prefix-table runtime.

- `Machine/ActivePrefixCorrectionOffsetData.lean`: Exact current-prefix correction rows subtract the physically selected temporary/source offset A from that address’s source-control mask B modulo2^(n*q). Uniform row length, output length and independent row semantics include n=0.

- `Machine/ActivePrefixCorrectionOffsetSubtract.lean`: Actual modular row-subtraction machine lifted to arbitrary alphabets and caller operand/output/width/count ports. It consumes and erases both complete operand tables, retains original descriptors and restores nine private tapes with a linear row-volume bound.

- `Machine/ActivePrefixCorrectionOffsetBank.lean`: Shared original-eight-descriptor correction caller stores only generated selected/control operands, five derived headers and final output. Exact stage-bank identities connect the two real producers, header construction, subtraction and cleanup.

- `Machine/ActivePrefixCorrectionOffsetRun.lean`: One fixed original-input sequence physically generates both varying operand tables, synthesizes count2^W and width n*q, subtracts each row and erases operands plus every derived header. Originals survive and forty-one shared private tapes return blank.

- `Machine/ActivePrefixCorrectionOffset.lean`: Complete fixed original-descriptor B-minus-A correction producer has exact current-prefix output and a uniform constant times2^W*(W+1) bound including both operand producers, rowwise subtraction and cleanup. Actual active-target rotation composition remains separate.

- `Machine/ActivePrefixCorrectionOffsetPlaced.lean`: Clean correction producer on arbitrary original-eight-plus-output caller ports returns exact correction offsets at origin, retains every original/spectator and erases all fifty-seven private tapes. Zero-width rows are included.

- `Machine/ActiveTargetHighestLaterValue.lean`: Exact rectangular later-source target XOR is swap–earlier-XOR–swap, preserving arbitrary prefix, gap and suffix coordinates. Native-array geometry and full-volume casts identify the conjugated mathematical action.

- `Machine/ActiveTargetHighestLaterClean.lean`: Earlier highest-bit physical output is exactly its original native input bank with only the array transformed. Every supplied descriptor and private/tracking tape is retained or erased literally, allowing actual repeated machine composition.

- `Machine/ActiveTargetHighestLaterAlphabet.lean`: Executes the actual earlier-source highest machine in the prime interchange alphabet with exact literal array input/output, retained original headers, blank workspace and unchanged137575-times-full-volume runtime.

- `Machine/ActiveTargetHighestLaterBank.lean`: Full native highest-bit bank plus four supplied swap descriptors has an exact payload-only update bridge to binary interchange, including the non-definitional full-volume cast and unchanged complementary bank.

- `Machine/ActiveTargetHighestLaterRun.lean`: Actual fixed swap–earlier-toggle–swap-back sequence realizes later-source highest-bit XOR on the full array, retains all ten supplied canonical descriptors and clears all scratch. Exact charged costs and one uniform linear full-volume bound are proved. Descriptor synthesis and final compact-caller placement remain separate.

- `Machine/BinaryVaryingParityOnlyGather.lean`: Actual fixed runtime-header gather uses the pure source-parity operation and ignores control values logically. Source/control words and original q/b/count survive; every derived descriptor/clock is generated and erased with a uniform stride bound.

- `Machine/BinaryVaryingParityOnlyPlaced.lean`: Own clean six-port placement of the physical pure-parity gather preserves every complementary caller tape and restores its twenty native private tapes. Exact output, retained originals and charged runtime are proved.

- `Machine/ActivePrefixParityOnlyData.lean`: Per-prefix pure-parity rows are exactly each current target digit’s low bit followed by compact padding. Full row/stream identity, original prefix testBit semantics and output length2^W*(n*b) include zero digits.

- `Machine/ActivePrefixParityOnlyBank.lean`: Original eight-descriptor pure-parity bank physically projects current target/full-source fields, extracts controls and runs an actual source-only parity gather. Every control row may vary, but none enters the offset value.

- `Machine/ActivePrefixParityOnlyRun.lean`: One fixed forty-one-tape original-input sequence generates all headers, prefix fields and source controls before actual pure-parity gathering, charging every stage.

- `Machine/ActivePrefixParityOnlyCleanup.lean`: Physically erases projected target/source/control tables and every derived header after pure-parity emission. Originals and exact output remain at origin; all private storage and heads are restored.

- `Machine/ActivePrefixParityOnly.lean`: Complete fixed pure-parity offset producer has exact current-prefix semantics and full cleanup with a uniform constant times2^W*(W+1) bound, including zero digits. Compact swap/rotation composition remains separate.

- `Machine/ActivePrefixParityOnlyPlaced.lean`: Clean original-eight-plus-output caller placement produces exact pure-parity offsets, retains all original descriptors and spectators and restores forty-one private tapes with unchanged runtime.

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
  arithmetic is a program parameter; the concrete legacy instance still depends
  on runtime dimensions in finite control, so uniform key compilation remains open.
- `Compact/PowerTwoDigits.lean`: bit words as packed integers in a
  power-of-two radix: a word of `n·q` bits is the packed integer whose
  base-`2^q` digits are its `q`-bit block values, the gather gadget's word is
  the packing of its digit words, and the per-digit forms of the compact
  control arithmetic, a masked shifted block, a block's parity, a toggled
  parity, have their stated values.
- `Compact/PackedArithValue.lean`: the forward packed program on tapes
  computes `packedEarly` in the radices `2^q` and `2^b`: each gathered offset
  word packs as the corresponding integer offset (masked shifted blocks,
  controls, parities, toggled parities), each modular transduction is the
  corresponding modular update, and the signed third line is the difference
  of two packings; the final words are exactly the packed program's output
  integers.
- `Compact/PackedInverseValue.lean`: the inverse packed program on tapes
  computes the packed permutation's inverse: `packedEarly` applied to the
  integers of its recovered words returns the integers of its input words,
  each forward line cancelling the corresponding inverse line modulo the
  radix power, so by injectivity the recovered address is the preimage.
- `Compact/ToggleValue.lean`: the ideal selected-parity toggle on bit words
  is exclusive or with the control mask, the control bits at stride `q`
  (which is the controls gather); it flips the lowest bit of each block
  exactly when its control is set and packs as `toggleList` of the block
  digits.
- `Compact/GuardValue.lean`: the guard test on tapes decides membership in
  the exceptional set: with the constants `2B`, `L - 2B - 1` and `B - 2` as
  words of the block widths, some flag is set exactly when the address fails
  `earlyGood` in the radices `2^q` and `2^b`, the upper bits of a block
  being its digit halved.
- `Compact/KeyValue.lean`: the key routine's words are the repair scan's
  key data for the concrete early instance with ranks in lexicographic
  order: the fixed-width counter's word at rank `j` has value `j` and splits
  into the address words, the guard flags are the membership flag of the
  rank's address, the inverse program's words are the packed permutation's
  preimage, the exclusive or with the control mask is the ideal map, and the
  appended words are the binary expansion of the destination rank.
- `Compact/KeyInstance.lean`: the key routine placed into the repair scan's
  bank (key at slot twelve, counter at thirteen, scratch from fourteen) meets
  the scan's key contract for the concrete early instance: the scan's counter
  tape is the counter word over the separator, the active bank is the
  routine's input, and the replaced bank is the scan bank with the key word
  written. With it, `repair_instance` is the complete repair machine: scan
  with the key routine, sort, strip and reinsert, carrying the unflagged
  actual stream to the ideal stream within the pipeline's bound. Its placed key
  still depends on q, b and the control count in finite control; replacing it
  with one runtime-driven machine remains open.
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

- `Compact/LatePowerTwoRank.lean`: Exact short-counter modular splitting matches the later address order U followed by V/W, without a counter-length assumption.

- `Compact/LatePowerTwoWords.lean`: Literal split words encode every later address, including unrestricted dirty source/temporary digits and physical blank-tail padding.

- `Compact/LatePowerTwoBridges.lean`: Actual late inverse words, ideal toggle and destination key bits agree with the later permutation inverse and exact destination rank encoding.

- `Compact/ActiveTargetSubsegmentValue.lean`: Lifts actual early/later packed kernels on good addresses to the full containing target slot, with exact low/high spectator reconstruction and restoration of all dirty companions. No target front-capacity premise or unguarded full-slot equality is assumed.

- `Compact/ActiveTargetSubsegmentWords.lean`: Guarded packed toggles equal the literal stride-q selected XOR mask inside the full target slot, with exact spectator intervals. The omitted highest selected toggle acts separately on the first retained high bit; the combined full-selected mask and full slot width are proved. Physical highest-toggle execution remains separate.

## Networks

- `Networks/AffineFieldBijective.lean`: Legal finite field programs are bijections, including reflected subtraction and literal coordinate interchange, validating original inverse-function address semantics.


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

- `Networks/AffineFieldSegments.lean`: Splits field programs into nonrecursive runs separated by explicit recursive interchange boundaries. Exact flattening and run semantics, original membership and nonrecursive hypotheses for each run, exact recursive-call count, and number of runs are proved. Enables segment compilation without concealing recursive-call obligations.

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

- `Networks/FramedControlSchedule.lean`: Role-preserving zipper attaches field programs to framed edges while retaining every scalar gate and original instruction order, with exact execution under edge realization.

- `Networks/FramedControlShape.lean`: Exact shape forgets only frame operators, retaining edge roles and scalar gates; equal shapes imply identical attached controls, including restriction and renaming.

- `Networks/DAGFramedShape.lean`: Frame-independent instruction shape for forward and complementary DAG schedules, including finite-bank restriction.

- `Networks/Shared50OrderedControl.lean`: Actual Shared50 interleaved rational control with exact routed transpose semantics, original scalar program, exact recursive-call count and certified nonrecursive segments.

- `Networks/Shared50FramedShape.lean`: All actual Shared50 role names, edges and scalar-gate positions are independent of frame realization, proved symbolically without evaluating the huge circuit.

- `Networks/Shared50FixedControl.lean`: One literal rational control list for all runtime widths. Exact schedule equality preserves role names, scalar-gate order, routed transpose semantics and the improved recursive-call count.

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
- `NLogN/NeumannHalved.lean`: the manuscript's Neumann evaluation with no
  clamp. Under `α²θ ≥ 1`, `‖E‖ ≤ 2.01 e^(−π/2) ≤ 0.46`
  (`opNorm_offDiagCLM_le_unit`); halving and rounding the input first keeps
  every rounded Horner iterate in the unit disk when the scaled error of `Ẽ`
  is at most `2^p/25` (`hornerNeumannR_err_unit`, `inverse_approx_unit`), so
  `J̃'` (`resampJNumH`) approximates `J(v/2)` and `B̃₀ = D̃' J̃' C`
  (`resampB₀NumH`) approximates `B₀` with error `24m + 27`, stays in the unit
  disk, and with the window `⌊√p⌋ + 1` has error below `p²` for `p ≥ 13`
  (`approxMap_resampB₀NumH_sqrt`, `errB₀H_sqrt_lt_sq`). This is the form the
  tape machines implement.
- `NLogN/ResamplingManuscript.lean`: Lemma 7.1 with the manuscript's
  numerical maps and no clamps. For `α ≥ 2`, `‖A‖ ≤ 3/4`
  (`opNorm_resampA_le_three_quarters`), so any approximation with scaled
  error at most `2^p/4` stays in the unit disk (`ball_of_approx`);
  `permuted_numeric_manuscript` gives the permutation-left identity with the
  unclamped window sums `Ã` and the clamp-free `B̃₀`, errors below `p²`, and
  both maps sending the unit disk to itself.
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

## Resampling

- `Resampling/RowSelect.lean`: the row-selecting map `C` of the resampling
  interface on tapes. With the addend `2s`, modulus `2t` and initial counter
  `2t - s - 1`, the selection machine copies exactly the records at the indices
  `[tj/s] = rowIndexNat s t j`, `0 ≤ j < s`, in increasing order
  (`crossing_iff`, `rowIndexNat_eq`, `selected_eq`); `rowSelect_hoare` is the
  exact tape contract with cost the input volume plus `O(log t)` per record and
  no numerical error.

- `Resampling/WindowSum.lean`: the window sums of the machine are the
  numerical map `Ã`: rounding toward zero of a dyadic rational is the
  truncated division (`rho0_div_pow`), one fixed-point term has the
  truncated products as parts (`term_parts`), the truncated window reindexes
  to a range (`sum_Icc_eq_range`, `floor_centre`), and `accumulators_eq`
  shows `resampANum s t m (resampTermNum p s t α) u k` has parts
  `signed accR / 2^(p+1)` and `signed accI / 2^(p+1)` when the weight words
  hold `ρ(2^p·w)` and the input words the numerators of `u`, cyclically
  extended by `m` records.

- `Resampling/OffDiagSum.lean`: the same machine computes the off-diagonal
  map `Ẽ` of the Neumann iteration. With stride one (`s` outputs over `s`
  inputs, `centre_self`) and a zero weight word at each window centre, the
  excluded term `h = 0` contributes nothing (`offDiag_sum_range`), each
  rounded term has the machine's truncated products as parts
  (`round_term_parts`, `term_eq`), and `accumulators_eq` shows
  `offDiagNum m (offDiagTermNum p s t α) u ℓ` has parts `signed accR / 2^p`
  and `signed accI / 2^p`. The line machine now only needs `s ≤ t`.

- `Machine/RecordRewind.lean`: rewinding or erasing a tape of
  blank-separated records. One tape, five states: step left, scan left until
  two adjacent blanks (the blank run left of the first record), return to the
  origin; with the erase flag every visited cell is blanked (`wipe`).
  `rewind_hoare` is the contract on any tape with no adjacent blanks in the
  scanned range; `flat_adj` shows flattened records have none, so
  `rewind_records` returns any head on a record tape to the origin in
  `x + 4` steps and `erase_records` blanks the whole tape from its end.

- `Machine/RecordCopy.lean`: walking over blank-separated records. One
  three-tape machine (source, destination, ruler) moves the source head over
  whole records, copying them to the destination when `cp`, and stops at a
  record origin when the source reads blank (`ct = false`) or after one record
  per ruler cell (`ct = true`); `walk_hoare` is the exact contract, cost the
  volume walked, covering copy-all, copy-`n`, skip-all and skip-`n`.

- `Machine/SubPass.lean`: the subtraction pass of the Neumann evaluation.
  Five tapes (accumulator records, start records, output, scratch, width
  ruler); per record a ruler copy takes the first `w` bits of the
  accumulator, `Negate` negates them, `CopyWord` copies the start word to the
  output and `SignExtendAdd` adds the negation onto it, then the scratch is
  erased and the heads advance to the next records. Generated by `subgen.py`
  on the generic `bankgen.py`; `pass_hoare` writes exactly the records
  `nextWords vs es w` (`yt`, `yt_step`) at `8w + W + 32` per record.

- `Machine/NeumannStepLemmas.lean`, `Machine/NeumannLoop.lean`: the Neumann
  evaluation of `J̃'` on tapes. One iteration builds the cyclic extension of
  the current iterate on the line machine's input tape by record walks (skip
  a suffix counted by a ruler, copy it, copy the iterate, copy a counted
  prefix; `ext_eq`, `ext_flat`), runs the Gaussian line machine with stride
  one (`gauss_run`), rewinds and erases its tapes (`RecordRewind`), and runs
  the subtraction pass against the start words (`sub_run`); twenty-seven
  tapes, generated by `neugen.py`. `step_hoare` takes the iterate from
  `iter K` to `iter (K + 1)` within `stepBound`, and `loop_hoare` runs `p`
  iterations counted by a ruler.

- `Machine/PairJoin.lean`: complex coordinates as single records. The join
  machine writes a separator over every other blank of a tape of word
  records, turning real/imaginary word pairs into records
  `re ++ separator :: im` (`pairs`); the split machine writes blanks over the
  separators. One tape each, `join_hoare` and `split_hoare` are exact with
  cost the tape volume; they let the record-selecting machine move complex
  coordinates.

- `Resampling/B0Words.lean`, `Resampling/B0Tape.lean`: the numerical
  `B̃₀ = D̃' J̃' C` on tapes. The input coordinates are joined into single
  records, the modular-counter machine selects the records at
  `rowIndexNat s t j` (`sel_eq`: the selected records are the pairs of
  `vsel`), they are split again, halved by one window-radius-zero Neumann step
  (weights `-2^(p-1)`, zero start words; `oneStep`), copied to the start tape,
  iterated `p` times by the Neumann loop, and multiplied by `D̃'` with one more
  window-radius-zero step. Forty-two tapes, generated by `b0gen.py`;
  `b0_hoare` is the exact contract.

- `Resampling/B0Value.lean`: the words written by the `B̃₀` machine are the
  numerators of the manuscript's clamp-free `B̃₀`. A window-radius-zero step
  with zero start words gives minus the truncated products
  (`oneStep_signed`); the selected words represent `C w` (`sel_vec`); weights
  `-2^(p-1)` give the rounded halving `rdV p (v/2)` (`half_vec`); weights
  `-ρ(2^p d')` give `D̃'` (`diag_vec`); with `resampJNumH_eq_iter`,
  `b0_value` identifies the output with `resampB₀NumH p (⌊√p⌋+1) s t α w`.

- `Resampling/TabledMaps.lean`: the numerical maps with supplied weight
  tables. Exact rounding of an exponential cannot be computed in a provable
  time, so the machines use integer tables within two units of `2^p` times
  the weights; each term keeps its error (`termW_err`, `offTermW_err`,
  `diagW_err`), and `permuted_numeric_tabled` gives Lemma 7.1 for `Ã` and
  the clamp-free `B̃₀` built from any such tables (`resampB₀NumW`), errors
  below `p²` and the unit disk preserved. `accumulators_eq_W` and
  `B0Value.b0_value_W` connect the tape machines fed integer tables to these
  maps.

- `Resampling/PiApprox.lean`, `Resampling/ExpApprox.lean`: certified integer
  approximations for the weight tables. `piApprox q K` sums Machin's series
  with exact floored terms `⌊2^q/((2k+1) m^(2k+1))⌋` and is within
  `20K + 40·2^q·5^-(2K+1)` of `2^q π` (`piApprox_err`, from
  `arctan_tail` and Mathlib's `four_mul_arctan_inv_5_sub_arctan_inv_239`).
  `expApprox X q N` sums Taylor terms each obtained by one multiplication and
  one truncated division, within `N e^|x| + 2^q |x|^N/N! e^|x|` of
  `2^q e^x`, `x = X/2^q` (`expTerm_err`, `exp_tail`, `expApprox_err`).

- `Resampling/WeightTable.lean`: the integer weight tables. `expPi` computes
  `2^p exp (∓π a/b)` from `piQ ≈ 2^(5p) π`, `Y = ⌊P a / b⌋`, a `7p`-term
  Taylor sum and a `4p`-bit shift, with a shortcut to zero when the negative
  exponent is below `-p`; it is within `3/2` (`expPi_neg_err`,
  `expPi_pos_err`, `p ≥ 13`). `tableA`, `tableE`, `tableD` (with `rr`, the
  integer form of `s β`) are within two units of `2^p` times the Gaussian,
  off-diagonal and `D'` weights, and `tableD ∈ [0, 2^p]` (`tables_ok`, for
  natural `α ≥ 2`, `α² ≤ p`).

- `Resampling/WeightNat.lean`: the weight routine in natural numbers, as the
  tape machines compute it. The Taylor terms are `±M_n` with
  `M_{n+1} = ⌊M_n Y/(2^q (n+1))⌋` (`expTerm_neg`, `expTerm_pos`); below the
  shortcut the alternating sum stays positive (`E_close`, `odd_le_even`), so
  `expPi` equals the natural `expPiNat` (even minus odd partial sums, shifted)
  and the three tables equal `tableANat`, `tableENat`, `tableDNat`.

- `Machine/Registers.lean`: natural-number registers on tapes. A register of
  `n` is the canonical binary word `canon n` at origin zero; canonical words
  are unique for their value (`canonical_unique`), and the trim machine
  (scan, step left, erase high zeros, return; `Trim.trim_hoare`) turns any
  word into the register of its value (`norm_hoare`).

- `Machine/RegOps.lean`: arithmetic macros on natural-number registers,
  generated by `regops.py`: `RegAdd` (`y := x + y`), `RegSub` (`y := y - x`),
  `RegCopy`, `RegClear`, `RegMul` (the product lands at origin zero by
  advancing the accumulator head along the multiplier first), `RegDiv`
  (quotient and remainder registers, positioned the same way), `RegCmp`
  (the bit `x < y`). Each runs the binary machine, returns the heads, trims
  the result, and has an explicit cost bound in the word lengths.

- `Machine/RegConst.lean`: the register of a constant, written bit by bit by a
  machine whose state counts the bits, then returned to the origin
  (`const_hoare`).

- `Resampling/PiNat.lean`: Machin's sums in natural numbers, as the tape
  machine computes them: iterated quotients `dSeq` (`⌊2^q/m^(2k+1)⌋`),
  nonincreasing terms, even and odd partial sums whose difference is
  nonnegative (`od_le_ev`), and `piN p = 16 A₅ - 4 A₂₃₉` (`piN_eq`).

- `Resampling/PiTape.lean`: `piN p ≈ 2^(5p) π` on natural-number registers,
  generated by `pigen.py` on `regprog.py`: `2^(5p)` by a doubling loop, then
  for `m = 5, 239` a loop of `5p` iterations dividing by `2k + 1` and by
  `m²`, accumulating even and odd terms by a parity branch
  (`atanMid*_hoare`), and finally `16 A₅ − 4 A₂₃₉`; `pi_hoare` takes the
  register of `p` to the register of `piN p`.

- `Resampling/ExpTape.lean`: the weight routine `expPiNat` on registers,
  generated by `expgen.py`: `Y = ⌊piN·a/b⌋`, the shortcut comparison with
  `p 2^(5p)` (a branch), the `7p`-term Taylor loop updating
  `M := ⌊⌊M Y/2^(5p)⌋/(n+1)⌋` and accumulating even and odd terms by a parity
  branch, and the final `4p`-bit division; `expNeg_hoare` and `expPos_hoare`
  write the register of `expPiNat true/false p a b`.

- `Machine/RegWord.lean`: registers as fixed-width words. A ruler copy of
  `w` cells from a register yields its canonical word padded with zeros
  (`cells_reg`, `padTo`), whose signed value is the register's value below
  `2^(w-1)` (`signed_padTo`).
- `Resampling/TableIdx.lean`: sign-free formulas for the table numerators:
  `(sk − tj)²` with `j = ⌊sk/t⌋ − m + i` splits at `i = m` (`gauss_num`), and
  `rr x = s β(x)` is the centered residue of `t x mod s` (`rr_eq`) with square
  `min(u, s − u)²` (`rr_sq`).

- `Resampling/TabATape.lean`: the Gaussian weight table on tapes
  (`tableA_hoare`, 43 tapes, generated by `tabagen.py`). From registers
  holding `s, t, m, α, p` and a width ruler it computes `piN p`, `2^(5p)` and
  `2^(4p)`, then for each entry `e = k(2m+1) + i` the exponent numerator
  `xv` (branching at `i = m`), runs `expNeg`, divides by `α` and appends the
  `w`-bit word; the output tape ends as the records of `tabA`, whose entry
  `e` is `wA = tableANat` at `(k, ⌊sk/t⌋ − m + i)` (`wA_eq`).

- `Resampling/TabETape.lean`: the off-diagonal weight table on tapes
  (`tableE_hoare`, 38 tapes, generated by `tabegen.py`). Sign-free residues:
  `u = tx mod s`, carry `cc` with `rr x = u − s·cc` (`rr_nat`) and magnitude
  `bb` with `rr² = bb²` (`rr_sq_bb`); `rr` is `s`-periodic (`rr_period`). Each
  entry `e = ℓ(2n+1) + j` branches three ways on `j` vs `n`; the nonzero
  offsets compute `An`/`Ap` and a representative of `ℓ + h`, then one shared
  weight routine runs `expNeg` on `α²(A² − bb²)` over `s²` (`wE_neg`,
  `wE_pos`, `wE_zero`). Generic output words `tabF`/`ytF`.

- `Resampling/TabDTape.lean`: the diagonal and halving weight tables on
  tapes (`tableD_hoare`, 41 tapes, generated by `tabdgen.py`). Doubling loops
  give `2^(4p)`, `2^(2α²)`, `2^w`, `2^(p−1)`; each entry runs `expPos` on
  `α² bb(ℓ)²` over `s²` and shifts by `2α²` (`tabD`), then writes the
  negated word `negv w v = (2^w − v) mod 2^w`, whose signed value is `−v`
  (`signed_negv`); a second output receives `s` copies of `negv w 2^(p−1)`.

- `Resampling/TableValue.lean`: the table machines' words read back. Every
  word has width `w` and magnitude at most `2^p` (`expNeg_le`: the E
  exponent is at least one once `s ≤ α²(t − s)`); A and E words have signed
  value the table entry (`tabA_ok`, `tabE_ok`), D and halving words the
  negated entry (`tabD_ok`). `a_tables` and `b0_tables` instantiate
  `accumulators_eq_W` and `b0_value_W` with `tableA`, `tableE`, `tableD`.

- `Resampling/LineApply.lean`: `Ã` applied line by line (29 tapes, generated
  by `lalgen.py`). Each step copies line `ℓ` (`2s` words) off the array tape,
  builds its cyclic extension, runs the line machine with `t` windows
  (`gaussA_run`), appends the `2t` accumulator words to the output and cleans
  up; `loop_hoare` runs `L` lines, leaving `outs wt arr s t m p w W L`, in
  time `L (lineBound + 2)`.
- `Resampling/LineValue.lean`: `outs_getD` locates line `ℓ`'s words, and
  `line_value` identifies them with the `Ã` numerators of that line for the
  A-table words.

- `Resampling/NeumannWords.lean`: the Neumann evaluation of `J̃'` on words.
  An iterate is `2s` signed words; one step extends it cyclically by `m`
  records (`ext`, `cycIdx`), takes the stride-one window sums of the line
  machine (`outWords`), truncates each accumulator to the word width
  (`signed_take`), negates it and adds the start words (`nextWords`,
  `sub_entry`). Because the rounded Horner iterates stay in the unit disk and
  on the grid (`rhoC_grid`), every word is exact: `iter_spec` identifies the
  word iterates with the numerators of the Horner iterates, and
  `resampJNumH_eq_iter` gives `J̃' v` from `p` iterates of the halved input
  with the window `⌊√p⌋ + 1`.

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

- `ExactRecoveryOutput.lean`: Turns the actual recovered coefficients into exactly twice the input length in bits by proving that excess leading padding is zero. Covers nondivisible chunk widths, directly instantiates `ExactRecovery.exact_product`, and identifies the literal machine output contract once the word is installed. Carry compilation, physical installation and runtime are separate obligations.

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
