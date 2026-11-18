# Cover machine: paper audit (2026-11-09)

Question from the [M9/M10 audit](../M9/DESIGN.md): can a class-indexed cover run on this
machine, so that PR589 (and later the M10 word) has cheap routes?

Sources read at upstream `da637c87`: `notes/three-stage-cover-{bit,rows,assembly}.tex` and the
`PROOF.md` of `research/selected-bit-stream-routes`, `-fast-primitives`, `-recursive-caller` and
`-recursive-closure`. Here: [M8 design](../M8/DESIGN.md) and the
[PR589 hole note](../../../docs/pr589-hole/pr589-hole.tex). Upstream's Python checkers, JSON
receipts and `selected-bit-local-ring-sweeps` were not read or run. Upstream presents all of it as
written argument without a fixed-tape compiler or formal proof.

## Verdict

Go on paper. No step of the cover machine is priced as a product of the payload width and the
atom width, which is what closed the fixed-role route in the hole note. Three components are new
and intrinsic, and they carry most of the work: weights, coefficients computed from labels, and
the bad-class fallback.

| Piece | Status here |
| --- | --- |
| Stopped recursion, atoms `(Z/q^w)^f`, variable-rank reversed children, `F L F` wrapper | Exists (M8 stage 2) |
| Recurrence with linear and leaf tolls, extra fallback children | Exists: `StoppedRecurrence.stopped_closed` takes any child list |
| Leaf interchange at width `w` with prefix, gap and suffix | Exists: `BinaryInterchangeBudget.uniform_bound` |
| Label covariance, weighted contract, weighted leaf | Proved in [`Weighted.lean`](Weighted.lean) |
| Good normal form over the atom ring | Proved in [`GoodForm.lean`](GoodForm.lean) |
| Label routes | New, from existing primitives (section 3) |
| Row stock per level, label layout, good/bad split, directory | New (section 4) |
| Coefficients and weights computed from labels on tape | New, largest item (section 5) |
| Unit-pivot fallback on bad classes | New (section 6) |
| PR589 as a cover network, moment certificate, retune | New (section 7) |

## 1. What the cover is

Every role stream gets a label `g`, an invertible `m × m` matrix over the atom ring
`R_w = Z/q^w`. The stream at label `g` is stored in the frames `g U g⁻¹`.

- The full reversed interchange is the same at every label, so one sweep over all labels
  completes every role (`revExchangeOf_one_conj`).
- A route `σ` changes the label to `g σ` and the local projector to `σ⁻¹ M σ` and keeps the frame
  (`label_route`). A gate between two wires with different routes is a permutation of one wire's
  labels, a pointwise XOR, and the inverse permutation. No payload address digit moves.
- Helpers that share a family sit at different labels, so the cover also replaces the five host
  classes of hole A.

The price is that every frame, adapter and pivot now depends on the label, which is an address
field. That forces the three new components.

## 2. Why the cost closes

Per node of `n` atoms and volume `V`:

| Work | Cost | Reason |
| --- | --- | --- |
| Atom adapters | `O(V n)` | One ordered pass per atom; as in M8 stage 2. |
| Routes | `O(V w^(1-a_leaf))` | They move label atoms of width `w`, through the leaf interchange. Independent of `n`. |
| Splits, XORs, parking | `O(V)` | Unchanged. |

So `T(n, w) ≤ Σ c_r T(r⌊n/m⌋, w) + C n + C w^(1-a_leaf)`, the shape `stopped_closed` already
proves, with the fallback children as extra entries of weight `ε`. With `μ_1 < 1` and
`μ_(1-c) < 1`, and `w = ⌈e^c⌉`, the ordinary saving is `c(1-c) + c·a_leaf`.

For PR589 upstream certifies `c = 17/10000` (`μ_1 < 199/200`, `μ_(1-c) < 9999/10000`). With this
repository's leaf (`a_leaf = 1.2388e-4`) that is `a_b ≈ 1.6973e-3`. The atom exponent rises from
`1/1000` to `c`, which the wrapper needs anyway.

## 3. Label routes

Upstream writes `g = g0 + qG`, keeps the low class `g0 ∈ GL_m(F_q)` as one index and the `m²`
high fields as a box, and updates the high fields with carries read from the low class. The low
classes are permuted through one tape per class.

A simpler layout works here. Take the label box to be all of `M_m(R_w)`: `m²` label atoms of `w`
digits. Right multiplication by `σ` is then the same linear map on each of the `m` label rows,
with no carries and no class tapes:

- factor it as lower-triangular passes and transpositions (`Swap.LowerTriangular.factorization`);
- the passes are ordered-affine steps on label atoms, `O(V)` each;
- each transposition exchanges two label atoms with spectators between them: one leaf
  interchange at width `w`.

Singular labels hold zero padding. [`LabelPadding.transport`](LabelPadding.lean) proves
that an invertible route preserves this condition on the physical bit tape in both directions.
At every positive width, reduction to the residue field has equal-sized fibers, so
`LabelPadding.padding_count` bounds the padded fraction of the full label box by `m/q`. [`LabelMask.pad_exec`](LabelMask.lean) expands one selector per label record across its payload,
then spreads compact stock into the selected positions in physical order. It takes at most
`14 V + 10 R + 14` host steps for `R` records, given the record selectors and unary payload width.
[`LabelPadProgram.realizes`](LabelPadProgram.lean) generates the selectors and pads the stock
in one fixed host program from unary dimensions. Its cost is at most
`14 V + (16 + 10 m²) R + 18`. [`LabelCounts.high_exec`](LabelCounts.lean) builds the
high-part count from the retained unary atom width. [`LabelPadSetup.realizes`](LabelPadSetup.lean) composes counter setup, selector traversal,
and stock spreading from the six unary caller fields, the positive unary atom width,
and a length-one seed. It preserves the compact input, retains the expanded mask,
and prepends the padded data within `(194 + 10 m²) V` host steps. [`LabelDecode.realizes`](LabelDecode.lean) starts from the seven canonical binary words
on host registers, creates the seed, and completes padding within `(434 + 10 m²) V` host
steps. [LabelCallerHeaders](LabelCallerHeaders.lean) reads those words directly from the seven
caller tapes. If their left and right stacks contain a total of `L` symbols, including blanks,
loading adds at most `6 L + 51` host steps. [LabelSplit.realizes](LabelSplit.lean)
generates a residue-class mask from initialized traversal counters and stably partitions
the fixed-width records. The two gathers preserve the source and mask and together cost
at most `2 (R (16 W + 10) + 16)` steps for `R` records of payload width `W`. The stock is borrowed
and padded once at the outer wrapper, and the padding pass tests each label's low digits. The
density of invertible classes is above `1 - 2/q` per level, so the padded volume grows by at most
`e^(O(1/q))` over `O(log e)` levels. That exponent loss is below `10^-23` at `q > 2^80`; it must
be carried in the cost statement.

Upstream counts at most 3,520 leaf calls per data route and 1,664 per hosted route with its
carry scheme. In the box layout the count is at most `m - 1`. Lay the box out by columns, `m`
coordinates of `m` atoms: right multiplication mixes whole columns with scalar coefficients, so
with `σᵀ = E₁ Π E₂` a route is the ordered program of `E₂`, a column permutation and the ordered
program of `E₁` (`Route.route`, `Route.exists_route`), and the permutation is at most `m - 1`
exchanges of two columns (`Route.swaps_le`). Each exchange is one call of the existing
interchange supplier on a view of the caller's descriptor. The exchange list stores each pair
with its smaller index first, as required by the view. Given the view headers,
[`LabelExchange.realizes`](LabelExchange.lean) runs the supplier on the selected role at
`coreCost V c` for column width `c`. Its output satisfies `LabelView.swap_cols` on the caller's
volume. Given the parent dimensions and column counts on one descriptor bank,
[`LabelPrepare.prepares`](LabelPrepare.lean) computes the four changing view headers in at
most `34000 V` steps. The two row dimensions pass through unchanged. [`LabelPrepareClean.prepares`](LabelPrepareClean.lean) preserves all the input words
and clears the arithmetic tapes. Its output adds exactly the three new dimension words;
the width is already present. After use, `restores` erases the three words to recover the
input bank. [`LabelCall.runs`](LabelCall.lean) reads the two caller row headers and four
prepared slots directly, exchanges the columns on the selected role and preserves the
descriptor bank for release. [`LabelSwap.runs`](LabelSwap.lean) composes preparation, one supplier call and release on
a single bank, returning the staged dimensions and every other role unchanged. Its cost is
at most `3808274 V + coreCost V c`. [`LabelSchedule.permutation_schedule`](LabelSchedule.lean) writes and erases the
three counts for each exchange, then composes the exchanges on one common bank. Its
postcondition records the successive descriptor swaps. [`LabelPermutation.realizes`](LabelPermutation.lean) identifies the resulting
physical array with the column permutation on every packed matrix, spectator prefix and
payload index. This proves the permutation part of the route.

For one triangular pass, [`LabelPass.realizes`](LabelPass.lean) gives a clean tape program
fixed by the rational matrix. On a single contiguous label box with a trailing record of width
`W > 0`, it sends each label to its right product and preserves every record position, in time
linear in the box volume including the records. It uses the stage-1 prime and requires the
stage-1 coefficient certificates on the diagonal and strictly lower entries. For two selected atom positions,
[`LabelInstruction.runs`](LabelInstruction.lean) instead runs one stage-1 shift or scale
across the entire caller descriptor, including every outer prefix. It constructs the view
and restores the bank within a constant times the caller volume. For at least two atoms,
[`LabelProgram.pass_rational`](LabelProgram.lean) identifies the compiled list with the
original rational pass, and `LabelProgram.runs` executes the list with a coefficient times
the caller volume. [`LabelEntry.pass_runs`](LabelEntry.lean) gives the resulting right matrix product at every
spectator prefix and payload position on that same output tape. [`LabelBits.pass_runs`](LabelBits.lean) gives the same run on the supplier's bit tape:
every output cell is encoded because the matrix multiplier is a unit and the packed addresses
cover the caller's volume. The one-atom case needs a separate
scaling view.
[`LabelTransport.triangular`](LabelTransport.lean) proves that applying its compiled array
transform to every such prefix gives the right product on the caller addresses.
`LabelTransport.route` composes the two triangular transports with the permutation to give
the full right product by `σ`. [`LabelRoute.realizes`](LabelRoute.lean) executes this
composition on the shared bit tape for supported triangular factors with unit reductions
and at least two atoms. It chooses the exchange schedule before seeing the descriptor.
[`LabelWidth.lean`](LabelWidth.lean) converts the width header for the middle permutation
and restores it for the final triangular pass.
Given an invertible rational route, a factorization of its transpose, the stage-1
coefficient certificates and a denominator bound at the stage-1 prime,
[`LabelFactorization.realizes`](LabelFactorization.lean) supplies one machine and
one constant `C` for all positive widths. Its time is at most
`C V + (m-1) coreCost V (w*m)`. The factorization determines the permutation
before reduction at the runtime width.
[`LabelShift.shift_index`](LabelShift.lean) gives the individual shift's address in that
descriptor, and `LabelShift.realizes` runs it when the view headers are installed.

A fixed finite label group would make labels ordinary roles and remove sections 5 and 6. I did not
find one. With a shared basis on the common complement, two routes whose lines meet at 60° have
a principal cosine of `3/4` or `1/4`, so their product has infinite order. Other basis choices
were not settled.

## 4. Stock, layout and classes

- **Row divisor.** Each level consumes `W · A^(m²)` rows (`A = q^w`): the role index and the label
  box. The depth is `D(n) = 1 + D(r_max ⌊n/m⌋)`, at most `2 log₂ e` for PR589 (`r_max = 42`).
  `RecursiveRowDivisor` builds `roleCount^k`; it needs a second factor and a depth that follows the
  largest child.
- **Borrowing.** The stock is `k = O(m² w log e)` digits taken from the head chunk, as in
  upstream's wrapper. `k < e/2` holds for large `e` because `w = e^c`.
- **Frozen labels.** A child treats the labels of its ancestors as spectator prefixes and takes
  its own label from unused stock. Its weights may read ancestor labels and nothing else.
- **Good and bad classes.** The branch depends only on the low digits of the label. Split each
  role stream into a good and a bad stream by that predicate, run one child per stream, and merge.
  The split streams are not boxes, so each carries a directory: the list of label values of its
  prefixes. [LabelDirectory](LabelDirectory.lean) encodes the current matrix in `w m²` radix
  digits after the inherited prefix and proves that each full matrix coefficient can be read back.
  Given this input directory, the retained mask puts its entries in the same order as the child
  records. [LabelDirectoryLoop](LabelDirectoryLoop.lean) generates the current label words from a
  zero counter, restores the record count, and writes the labels in physical order. [LabelDirectoryJoin](LabelDirectoryJoin.lean) interleaves one inherited prefix per
  record with these words, restores the record count, and leaves the input suffixes intact.
  [LabelDirectoryInherit.directory_exec](LabelDirectoryInherit.lean) starts with one prefix per
  parent, repeats it across the child label box, and joins the expanded stream to the generated
  labels. Both input tapes finish at their original suffixes.
  [LabelDirectoryBuild.split_exec](LabelDirectoryBuild.lean) composes label generation, directory
  construction, and partition by the retained payload mask. Each complete box restores the zero
  counter, and the join consumes the generated labels so their scratch register is restored.
  [LabelDirectorySetup.build_from_mask](LabelDirectorySetup.lean) constructs the label width,
  zero counter, and box count from the unary atom width and a unit seed. The retained mask
  supplies one count symbol per child. [LabelDirectoryClasses.from_dimensions](LabelDirectoryClasses.lean)
  derives the parent count from the descriptor and uses the residue traversal to write this mask
  before building the directory. [LabelDirectoryCaller.realizes](LabelDirectoryCaller.lean) starts
  with empty traversal registers, initializes them from the unary atom width, builds the directory,
  adds the new label width to the inherited width, and partitions the complete entries by class.
  [LabelChildStreams.realizes](LabelChildStreams.lean) partitions the payload records by the
  same mask, preserving their alignment with the directory and retaining the unary record count
  for each child. [LabelChildMerge.children_exec](LabelChildMerge.lean) uses the retained mask
  to merge the two transformed child streams in physical order. It consumes one fixed-width
  record from the indicated child at each step and preserves both unread suffixes.
  [LabelChildDispatch.realizes](LabelChildDispatch.lean) composes the split, both host calls,
  and the merge. Its induction hypotheses specify each child's action on its own prefix of
  the directory and payload. The weighted recursive bodies must still establish these hypotheses. Upstream's `Δ = 1 + C H (h+1) f` symbols bounds it well below the payload.

## 5. Coefficients from labels

At label `g` the projector of a move is `g P g⁻¹`. Its northeast elimination has unit
lower-triangular adapters and pivots that are rational functions of the label. Three consequences:

- **Weights.** A pivot cannot be applied as a scaling: scaling an atom by a unit that depends on
  the prefix has no bounded streaming form. The pivots are passed to the child as weights. The
  child contract is `F_A (h, d) = (A C d, C A⁻¹ h)` (`weighted`, `weighted_eq`), and one move is
  conjugated adapters around one weighted child with weights `α δ` (`weighted_good_child`). Weights are
  paid at the stopped leaves, four leaf interchanges and three shears per atom pair (`leaf_word`).
- **Adapters.** A weighted adapter coefficient is `α_i L_ik α_k⁻¹`; it stays lower triangular
  (`lower_diag_conj`). The streaming pass is the existing ordered shift with an offset computed
  per prefix block.
- **Evaluator.** The machine must compute, from the label atoms of a prefix: `g⁻¹`, the projector,
  its elimination, and the product of one pivot per ancestor. That is modular arithmetic on
  `w`-digit numbers and elimination of a fixed-size matrix. The cost is polynomial in `w` and the
  depth per prefix block, and a block has at least `q^w` cells. In the fallback an expression reads
  two parent weights, so the cost is `2^depth` times a polynomial; `2^depth ≤ 8e²` and
  `e ≤ w^(1/c)` keep it polynomial in `w`.

The evaluator is the largest new machine component. `Machine/Binary{Add,Sub,Multiply,Divide}`
supply the arithmetic. The existing atom passes take fixed rational coefficients
(`Coordinates.CoeffSupported`); they need a variant whose offset comes from a tape.
For one control digit `x`, `Fallback.offset_exec` in `FallbackOffset.lean` computes the canonical bits of `c*x % M` from three preserved tape operands.
It costs at most `48L² + 154L + 70` steps at width `L`. Given those bits on the translation machine's descriptor tape,
`Fallback.fiber_hoare` proves that destination symbol `((y+c*x)%M)*B+j` equals source
symbol `j` of block `y`, with the recurring tape layout restored. `Fallback.fiberInput_exec` places the arithmetic output directly on translation tape
8 and proves that the host stacks represent the complete encoded input bank. This assumes
the caller supplies the empty descriptor with its left separator. `Fallback.fiberProgram_exec` runs the offset computation and the placed translation as
one host program. It returns the rotated payload with both heads advanced and preserves every
register outside the twelve translation tapes. It clears blank padding and restores the exact empty descriptor stacks
before returning. `Fallback.fiberStep_exec` then advances the control digit from `x` to `x+1`
in the same register and restores the coefficient, modulus, and arithmetic scratch for the
next call. `Fallback.fiberLoop_exec` executes all `M` iterations from the represented input bank,
with the control digit starting at zero and a separate count register of length `M`.
Both payload heads advance by `M²B`. The destination contains the concatenated rotated
fibers, and `Fallback.shear_entry` identifies each symbol at its modular destination.
The enclosing `Fallback.shear_exec` starts with empty count and digit registers. It builds
the unary count and the fixed-width zero digit from the binary modulus in at most
`6M + 15L + 10` additional steps. `Fallback.initializedShear_exec` initializes the translation bank and runs the shear
from the two raw canonical header words, blank metadata workspace, and represented
payload tapes. `Fallback.dimensionShear_exec` builds both headers from padded arithmetic registers
holding the modulus and block width, then executes the complete shear with initially
blank translation metadata. It takes at most `10(L+K)+24` additional host steps for
modulus and width registers of lengths `L` and `K`. For control and target fields packed in that order, `Fallback.shear_read` reads the
original symbol from the final destination stacks at the address given by
`(RowOp.shear i k hik c).apply v` over `ZMod M`. `Fallback.flatShear_exec` derives all fibers from one packed flat input array,
executes the shear, and reads the symbol at the updated row address directly from the
final stacks. For fields in their original order, `Fallback.earlierControl_exec` extracts a control
digit from the physical prefix using two tape divisions, preserving the prefix, stride
and modulus. `Fallback.prefixStep_exec` uses that digit to rotate one target fiber,
clears the digit, and increments the physical prefix counter. The other arithmetic
registers and caller stacks outside the translation bank are restored exactly.
`Fallback.prefixLoop_exec` runs the counted loop over all physical prefixes from
prepared registers and a represented payload bank. For the original row-major array,
`Fallback.prefixLoop_entry` identifies every output symbol at its updated coordinate
address. `Fallback.prefixPass_exec` takes a binary prefix count in the digit register,
constructs the unary countdown and zero prefix counter, then frees the digit register
before the first rotation. Its setup costs at most `6N + 17L + 12` steps for count
`N` of width `L`. `Fallback.prefixShear_exec` starts with unmarked translation metadata and a padded
block width in slot 5. It trims the width in place, copies and trims the modulus in slot 7,
installs the separators, and executes the original-order pass. `Fallback.rowShear_exec` specializes the original-order pass to an elimination row
operation on one flat array. For control `k < t`, it uses prefix count `M^t`, stride
`M^(t-1-k)`, and block width `M^(d-1-t)*W`. The final stacks return the input symbol
at every transformed row address. `Fallback.dimensionPower_exec` computes the common form `M^n*b` directly in binary
from the modulus and seed registers, clearing its temporary product after each multiplication.
The exponent is fixed by the selected row indices. Seeds 1 and W give the three required
dimensions, and `dimensionTime_le` bounds the construction polynomially in the bit widths
and exponent. `Fallback.scheduledShear_exec` places these three results directly into the caller's
extent, stride, and block-width registers and executes the row addition on the original
array. Its inputs include a binary modulus, suffix width, and coefficient. For a forward undo addition, `Fallback.productShear_exec` computes the coefficient in
the shear register from the pivot-swapped matrix entry and a supplied pivot reciprocal
using modular multiplication. Its destination theorem uses the same `Ring.inverse`
as the elimination step. For a unit pivot x modulo p^(w+1), `Fallback.pivotReciprocal_eq` proves that
starting at x^(p-2) and repeating y ↦ y(xy)^(p-1) exactly w times yields its ring
inverse. `Fallback.modularPower_exec` executes each fixed powering operation on
padded binary residues, restoring all scratch at the original operand width. `Fallback.reciprocalLoop_exec` executes the width-controlled loop using the
fixed factor x^(p-1) and accumulator update y ↦ y^p x^(p-1). It returns the exact
pivot inverse and restores every other register except the consumed countdown.
`Fallback.pivotInverse_exec` initializes the accumulator from the pivot and a padded one,
multiplies the accumulator by the pivot to obtain the fixed factor, and clears the factor
after the loop. `Fallback.pivotShear_exec` feeds the inverse directly into the product shear
and proves its action on every array entry. `Fallback.matrixRead_exec` reads any entry of a row-major binary
matrix while restoring the source, given a unary symbol offset and word width.
`Fallback.readColumnPair_exec` generates both offsets from the live width, copies the pivot
and the entry in the pivot-swapped row, and restores the matrix and scratch.
[`Fallback.matrixShear_exec`](FallbackMatrixShear.lean) composes both reads with the shear.
It takes the word width from the modulus register and proves the destination of every
payload symbol for one forward undo addition with a specified unit pivot.
[`Fallback.itineraryEntries_eq`](FallbackItineraryEntries.lean) identifies the live
matrix at every valid itinerary stage with an entrywise recurrence. The pivot row is
copied, and each other row subtracts a multiple of that pivot row after the exchange.
`Fallback.subtractProduct_exec` computes each nonpivot output entry from the source
entry, the row multiplier and the pivot-row entry, restoring its arithmetic scratch.
`Fallback.updateEntry_exec` reads both source entries from the packed matrix and
prepends the result to the output tape, preserving the row multiplier and restoring
all scratch. `Fallback.updateRow_exec` emits a full nonpivot row using one shared
multiplier, and `Fallback.copyMatrixRow_exec` copies the pivot row. Both preserve the
existing output suffix. `Fallback.eliminateRow_exec` computes each multiplier once using the
shared pivot reciprocal. [`Fallback.updateMatrix_exec`](FallbackUpdateMatrix.lean) emits
the entire next matrix in row-major order and restores all workspace. [`Fallback.itineraryColumn_exec`](FallbackColumn.lean)
reads the specified unit pivot from the packed matrix, computes its reciprocal, and
executes the complete column pass. It preserves the width counter and changes only the
output stack. [`Fallback.diagonalize_exec`](FallbackItineraryMachine.lean) executes every column
of a supplied valid pivot itinerary. The two matrix stacks alternate roles and retain
earlier stages as suffixes. After the last pass, the active stack begins with the
packed unit diagonal obtained by the specified elimination of the original matrix.
The total time is at most `d*(4*w+4+columnTime d p w H)+1`.

## 6. Fallback

On a bad class some leading minor is not a unit, and reduction modulo `q` proves nothing over
`R_w`. Upstream eliminates the full `2m × 2m` residual with unit pivots. Pivot choices depend only
on the low class.

[`Itinerary.pivotStages_spec`](ResiduePivots.lean) computes the schedule by scanning
each residue column for its first nonzero eligible row. [`Fallback.classDiagonalize_exec`](FallbackClassMachine.lean)
runs the same schedule on every packed lift of an invertible residue matrix. [`Fallback.pivotStream_writes`](FallbackPivotStream.lean) emits the pivot
schedules in physical record order from the residue table. `Fallback.liveColumn_exec`
reads one pivot from this stream and clears its column with at most `2*d` extra
host steps. [`Fallback.recordDiagonalize_exec`](FallbackStreamedItinerary.lean) consumes a full
forward pivot schedule. [Fallback.pivotRoundTrip_writes](FallbackPivotStream.lean) places the same pivots in reverse order immediately afterward, so the rewind can read them before advancing to the next label. The forward pass returns a packed unit
diagonal whose product agrees with the corresponding sign-stream bit. Its two matrix
stacks retain every intermediate stage in alternating order.
[`Fallback.undoItinerary_apply`](FallbackUndoItinerary.lean) gives the explicit reverse
word from those stages. Acting on the diagonalized coordinates restores the original
matrix action, with at most `d*(6*(d-1)+3)` children. [`Fallback.rewind_exec`](FallbackRewind.lean)
visits the archived stages in reverse order using the live modulus width. Each callback
receives the preceding matrix at the head of its source stack; the driver then discards
the newer matrix. The last step restores both original matrix stacks. [Fallback.recordWeights_exec](FallbackRecordWeights.lean)
copies the nonanchor diagonal entries to the weight stack. For every payload bank,
the signed diagonal action using these weights followed by the reverse word acts
by the original matrix on each vector. [Fallback.reverseMatrixShear_exec](FallbackReverseShear.lean)
executes one lower shear from the reverse pivot stream, copies the result to the original
payload tape and returns both heads to their origins.
[Fallback.reverseStages_exec](FallbackReverseStages.lean) executes all reverse columns, consuming
the reverse pivot schedule and restoring the original matrix stacks. Given a payload already
placed at the diagonalized addresses, it places each cell at its original matrix image.
[Fallback.forwardStages_exec](FallbackForwardStages.lean) constructs that alternating matrix
archive on the reverse loop’s physical tapes. [Fallback.pairScaling_exec](FallbackPairScaling.lean)
executes one reciprocal pair on the payload. It multiplies the earlier coordinate by the
inverse of the selected diagonal entry and the later coordinate by that entry.
[Fallback.diagonalRewind_exec](FallbackDiagonalRewind.lean) composes all pairs with the
reverse traversal. Starting with the anchor already signed and the two archives populated,
it realizes the original residual matrix on the payload and restores both matrix stacks.
[Fallback.residualRecord_exec](FallbackResidualRecord.lean) includes forward elimination,
reconstructs the units from the resulting matrix, and consumes one live label’s round-trip
pivot schedule. It realizes the residual action given a payload signed according to the
corresponding sign-stream bit. Connecting the anchor pass’s output tape to this signed
input layout and executing the complete record loop remain open.

- An upper addition is a lower addition between two exchanges; an exchange of two sub-fields of
  one bank is a reversed child between two reversals of the later field; a reversal is one
  reversed child on the two halves of a field.
- That gives fewer than `32 m²` children of at most `⌊n/m⌋` atoms (`fallback_children`).
- The bad fraction per request is at most `2 m³/q`, from the degree of the minors and the density
  of `GL_m(F_q)`. No union over requests is needed, since the moment averages each request.

New here: children at arbitrary sub-field positions inside one bank, and a
nonvanishing-polynomial count over `F_q`. `GenericBasis` proves the nonvanishing over `ℚ` by the
combinatorial Nullstellensatz; the counting form (Schwartz–Zippel) is a different statement.

Bad classes cannot be turned into padding. A gate pairs label `g` with `g σ`, so the padded set
would have to be closed under every route.

## 7. Build order

Each step ends in checked Lean. Steps 1–3 are algebra and independent of the machine.

| Step | Content | Size |
| --- | --- | --- |
| 1 | Covariance, weighted contract, pivots as child weights, leaf word, fallback count | done, [`Weighted.lean`](Weighted.lean) |
| 2 | Good normal form over a commutative ring: if `P` factors through `r` coordinates and its leading minors of sizes `1..r` are units, then `P C = L Δ Π_r R` with unit lower `L`, `R` (`good_form`), and the move is one weighted child (`good_move`) | done, [`GoodForm.lean`](GoodForm.lean) |
| 3a | Unit-pivot elimination over a local ring: `n (n-1)` row additions and `n` exchanges make an invertible matrix diagonal with unit entries (`fallback_form`) | done, [`Fallback.lean`](Fallback.lean) |
| 3b | Row operations as children (`add_conj`, `ordinary_of_reversed`); one itinerary per residue class (`itinerary_form`, `exists_itinerary`, `valid_congr`); the bad-class count (`bad_count`) | done, [`Fallback.lean`](Fallback.lean), [`Itinerary.lean`](Itinerary.lean), [`BadClass.lean`](BadClass.lean) |
| 4a | Route and label semantics: routes as atom programs on label columns (`route`, `exists_route`, `swaps_le`); `Z/q^w` local, branch and itinerary read only the class (`isLocalRing`, `good_congr`, `valid_res`); column exchange as a descriptor view (`swap_cols`); padding at most `m/q` of the box (`singular_count`) | done, [`Route.lean`](Route.lean), [`LabelRing.lean`](LabelRing.lean), [`LabelView.lean`](LabelView.lean), [`BadClass.lean`](BadClass.lean) |
| 4b | Machine: ordered passes on label columns (stage 1's viewed scalar actions with the payload as suffix), supplier call per column exchange, padded stock, split by class, directory | 8–15k |
| 5 | Machine: coefficient evaluator and offset-from-tape atom passes | 15–30k |
| 6 | Machine: weighted children and leaves, fallback schedule, node induction | 10–20k |
| 7 | PR589 as a cover network from the role-level node of `M6/Bit*`; histogram and moment certificate at `1 - c`; wrapper at atom exponent `c`; seam and retune | 5–10k |

The sizes are rough. The stage-2 machine that steps 4–6 extend (`M8/RevMachine`,
`M8/Stage2Machine`) is about 26k lines.

The algebra of steps 1–3 is checked. Left for the machine steps, where the layout fixes them:

- [LabelProjector.good_move_at](LabelProjector.lean) supplies the rank factorization for a
  reduced rational projector whose factorization denominators are below the prime. On every
  accepted live record it gives the weighted good-child identity. The finite branch table uses
  the rational projector reduced modulo the prime and works at every positive atom width.
- [FallbackDiagonal](FallbackDiagonal.lean) factors the final diagonal of a positive-dimensional
  residual of determinant ±1 into one reciprocal unit pair per non-anchor coordinate and a sign.
  Two ordinary exchanges realize each pair, and one unweighted reversed child reverses a field
  about its middle. [FallbackResidual](FallbackResidual.lean) identifies the weighted reversed
  projector exchange with its block matrix. The matrix squares to the identity, so its determinant
  is a sign over the odd prime-power label ring and the reciprocal-pair factorization applies.
- [FallbackWord](FallbackWord.lean) undoes `Elim` on field vectors using forward shears and
  exchanges. Starting from the diagonal output, the word computes the residual action. Charging
  three children per exchange and six per diagonal pair gives fewer than `32 m²` children.
  [FallbackFields](FallbackFields.lean) realizes the three-child exchange on a flat list of atoms.
  It reverses the later field before and after the reversed exchange, preserving the intervening
  gap and the rest of the bank. For a reciprocal diagonal pair, two reversed children suffice:
  a plain exchange followed by a uniformly weighted one restores both field orientations.
  The theorem `residual_word` composes the anchor sign, the ordered pairs and the row operations.
  It computes the weighted residual for every input with fewer than `24 m²` children at these
  charges. The tape implementation of these field operations remains open.

`bad_count` is stated against the whole label box, which is what the box layout needs: at most
`r (r+1) (m+1) / (2q)` of the labels are bad for one move.

Decision point: the remaining cost is machine work of known kind. If steps 4–6 are judged too large, the fallbacks are those of the hole note: a bit
word with a port-independent line, or another cover-free supplier.

## 8. Open questions

1. Settled: at most `m - 1` supplier calls per route (section 3).
2. Settled: the traversal tests low digits in physical record order. The directory and payload
   use the same mask, as proved in [LabelChildStreams](LabelChildStreams.lean).
3. The exact moment root for the PR589 histogram, in place of upstream's `c = 17/10000`.
4. Recompute `kappa` for cover + PR589 with full-width chunks (`Cost/CompactInterimParameters`).
   The hole note's `2^-10.8` and `2^-10.4` predate them.
5. The M10 word of PR 4359 has cover rank `2^6552928412`. Every statement in steps 2–6 must keep
   the rank a variable.
