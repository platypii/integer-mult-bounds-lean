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
  Key selection for subsequent radix passes and the full sorting controller
  remain open.

- `Machine/RadixSort.lean` and `Machine/PartitionSort.lean`: executable stable
  least-significant-bit sorting, with permutation, numeric sortedness, exact
  equal-key subsequence preservation, and a key-width-times-volume identity.
  The concrete partition's two outputs concatenate to precisely one such pass,
  with their total volume equal to its actual transition count. Full tape
  sorting still needs subsequent key selection, buffer reuse, and a controller;
  the list traversal volume is not claimed as that implementation's runtime.

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
