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

- CrocSwap/integer-mult-bounds, commit
  `6e564879f51ae16f23d392e9e196c605f36d90df` (October 7, 2026).
- Its pinned OpenAI manuscript, commit
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

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
  connected to this contract interface. The design draws on complexitylib's
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
  initial contents. This list-level counter is not yet compiled to tape steps.
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
