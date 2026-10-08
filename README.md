# Integer multiplication in Lean

**Work in progress. The end-to-end multiplication theorem is not proved.**

The target is an actual deterministic machine with a fixed finite alphabet and
a fixed number of one-dimensional tapes, correct on every positive input
length, with worst-case runtime
`O(n (max(ceil(log₂ n), 1))^(1 - 83/10^12))`.

`IntegerMultBounds/Machine.lean` defines the machine semantics and the target
proposition `IntegerMultBounds.Machine.EndToEnd`. This is a proposition to be
proved, not a theorem or an assumed interface. Its transition function only
sees the finite state and scanned symbols. Each step writes at most one cell
per tape and moves each head at most one cell. Constants and the machine are
chosen before quantifying over inputs.

## Sources

- [CrocSwap/integer-mult-bounds](https://github.com/CrocSwap/integer-mult-bounds),
  commit [`6e56487`](https://github.com/CrocSwap/integer-mult-bounds/tree/6e564879f51ae16f23d392e9e196c605f36d90df)
  (October 7, 2026).
- Its pinned OpenAI manuscript,
  [*Integer multiplication below n log n*](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026),
  in [openai/math](https://github.com/openai/math), commit `adc7f12`.
- [complexitylib](https://github.com/SamuelSchlesinger/complexitylib), commit
  [`3f4b5fe`](https://github.com/SamuelSchlesinger/complexitylib/tree/3f4b5fee8bbd49721a5b70473c81bf3db2e7500d),
  for the machine composition design (no code imported).
- [mathlib4](https://github.com/leanprover-community/mathlib4), v4.34.1.

The local `integer-mult-bounds/` checkout is reference material and is ignored
by this project's Git repository. The Lean project does not execute or trust
the source repository's Python certificates.

## Reproduce

Install the version of Lean in `lean-toolchain`, then run:

```sh
lake update
lake exe cache get
lake build
lake env lean AxiomAudit.lean
```

Lean and mathlib are pinned to v4.34.1; `lake-manifest.json` pins transitive
dependencies. No theorem in this project uses a custom axiom or an admitted
proof.

## Checked components

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
- `Compact/Ideal.lean` and `Compact/ExactRepair.lean`: a packed ideal toggle
  permutation, preservation of the actual guard predicate, and executable
  destination repair connected to both concrete packed programs. Correctness
  holds for every address, including saturated temporary digits and failed
  guards. These prove address semantics; extracting, sorting, and reinserting
  records on fixed tapes remain open.
- `Compact/Permutations.lean`: modular rotations as actual permutations,
  restoration of an arbitrary back field by swap/load/swap, and invertibility
  of both packed programs on every address, including bad addresses. The
  permutations are proved to agree with the integer implementations.
- `Networks/Scalar.lean`: the eight-step arbitrary-scratch cancellation
  schedule, three-stage signed exchange, bit and complex triple-intersection
  coefficients, the resulting complex bank identity at any finite ground size,
  and the common-frame linear-gate identity. Sparse network realization,
  residual bases, endpoint corrections, and tape compilation remain open.
- `Machine/Counter.lean`: executable fixed-width binary increment, its exact
  modular value, and an amortized bound of `2*n + width` bit flips from arbitrary
  initial contents.
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
- `Compact/RepairBounds.lean`: the uniform rational exceptional-density bound
  under the stated dyadic cutoff, and the inequality reducing the written
  repair-cost expression to three logical volumes. Bad-set cardinality and the
  sorting implementation still need proofs.
- `Asymptotics.lean`: logarithmic powers are little-o of every strictly larger
  real power, specialized to all seven assembly margins; a finite-depth,
  volume-normalized recurrence bound with explicit leaf and overhead costs.
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
- `Parameters.lean`: every stated rational parameter slack, all seven assembly
  margins, their attained minimum and strict absorption gap, the two dyadic
  comparisons, the complex motif counts, and the strict complex branching-ratio
  bound. The logarithm enclosure is proved from a finite exponential-series
  lower bound inside Lean. These do not establish the motif's circuit interface
  or the costs of an implementation.
- `Compact/DirtyControl.lean`: the four-update identity, restoration of an
  arbitrary dirty integer temporary, parity and guard invariance, the
  later-source identity, and guarded intermediate ranges. These are universal
  integer statements, used by the guarded packed modular refinement above.
- `Compact/Repair.lean`: for any two permutations agreeing outside an invariant
  exceptional set, the actual map preserves that set and destination repair
  gives exactly the ideal map. `ExactRepair.lean` now instantiates this result
  with both verified packed programs. Implementing repair within the tape cost
  remains necessary.
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

`AxiomAudit.lean` checks public and private project declarations, transitively,
allowing only Lean's standard `propext`, `Quot.sound`, and `Classical.choice`.
It rejects admitted proofs, custom axioms, and native-evaluation axioms. CI
builds the project and runs this audit.

## Remaining end-to-end obligations

The target still requires an explicit multiplication program and proofs of its
execution, stream primitives and counters, finite bit and complex networks,
recursive tape scheduling, modular compact controls and their repair costs,
synthetic transforms, Gaussian resampling, prime selection, exact coefficient
arithmetic, rounding, carry propagation, and the final uniform complexity bound.
The upstream proof also invokes an existing `O(n log n)` multiplier as a
subroutine; this must itself be implemented and verified or replaced with a
proved suitable subroutine. None of these algorithmic contracts may be assumed
to claim the requested end-to-end result.
