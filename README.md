# Integer multiplication in Lean

**Integer multiplication below `n log n` is proved in Lean on Mathlib's finite Turing machines.**

## Main result

`IntegerMultBounds.MathlibTM2.statement` is unconditional: one fixed
`Turing.FinTM2` machine multiplies every pair of natural numbers, with standard
binary input/output encodings, in worst-case time `O(n (log n)^(1-kappa))`.
The construction proves the positive saving
`kappa = 4222422970/2^46` (about `2^-14.02`), exposed by `MathlibTM2.mulInTime`, where `n` is the
total encoded input length. See [the completed plan](plan/C-mathlib-end-to-end.md).

The running multiplier combines linear direct CRT routing with compact controls
and full-width chunks above the root `⌈d/2⌉`. It uses rounded synthetic layers on the T16 node (73 slots, 14336 data
roles, 1,041,408 children, so `log_73 (F/NW) < 999/1000`). Its bit interchange uses
PR97 stage 2: the opposite-bank compiler on design-B frames, variable-rank children,
stopped recursion over atoms, and the F L F wrapper on the generic machine in
`MathlibTM2/M8`. The atom exponent is `1/1000`; the resulting ordinary bit exponent
is `tau = 1-123879734039/10^15` (`Stage2Machine.Bound.uniform_bound`). PR97's
rank-one construction remains the leaf supplier ([stage-one note](docs/pr97-stage1/pr97-stage1.pdf)).
The parameters are `epsilon = 31/64`, `lambda = 1-12387973/10^11` and
`lambda' = 1-12387972/10^11`. The public saving is the binding layer margin
`epsilon (1-lambda')`, just below the layout margin `epsilon (1-tau)`, rounded down to `2^-46`.
Complete input preparation, distribution, transforms,
output and cleanup are included in the fixed-machine proof. The public saving
is more than `2^46` times the historical M2 saving `2^-66`, as an exponent improvement.

This completed proof is the primary route. The [retention audit](docs/proof-retention.md)
lists its dependencies and legacy removal candidates; the retired native controller is preserved in Git history.

The next routing construction has completed R1 and R2: a concrete selective-update
program with exact repair on every address, fully priced metadata setup, keying,
routing, classification, sorting and cleanup, and restored borrowed registers.
R3 now compiles framed physical source coordinates and activity into all eleven
repair source profiles, composing classifiers, widths, headers, exact repair,
placement and cleanup with restored borrowed tapes. This composition now accepts
any geometry satisfying explicit guards and density bounds, allowing reservoir
spacing. Complete directional destination maps now compose bulk and terminal
rank permutations, with exact shear semantics and restored surrounding bits.
A fixed-register schedule now executes repeated exact-repair calls from supplied
raw configuration, including loading, cleanup and full input rewind. The full
generated/placed price is proved independent of record order, and one complete
generated/placed call now executes from a framed input bank with loading and
erasure charged, using one fixed program across geometries. Repeated generated-call
scheduling, matching-derived inputs, remaining setup production
and uniform amortization remain open.
The complete router and multiplication integration remain in R3–R4; this work
does not yet change the multiplication saving. See [the active plan](PLAN.md) and
[the R2 audit](IntegerMultBounds/MathlibTM2/Routing/R2-AUDIT.md).

## Historical native-machine target

The original, separate native-machine target is an actual deterministic machine with a fixed finite alphabet and
a fixed number of one-dimensional tapes, correct on every positive input
length, with worst-case runtime
`O(n (max(ceil(log₂ n), 1))^(1 - 83/10^12))`.

`IntegerMultBounds/Machine.lean` defines the machine semantics and the target
proposition `IntegerMultBounds.Machine.EndToEnd`. This is a proposition to be
proved, not a theorem or an assumed interface. Its exponent saving is smaller than the
current Mathlib result; this separate machine interface is not the active improvement route.
Its transition function only
sees the finite state and scanned symbols. Each step writes at most one cell
per tape and moves each head at most one cell. Constants and the machine are
chosen before quantifying over inputs.

## Mathlib statement

`IntegerMultBounds/MathlibTM2/Statement.lean` states the target with Mathlib definitions only:
`Turing.TM2ComputableInTime` with Mathlib's binary encodings `encodingProd` and
`encodingNatBool`, so an auditor of the final result reads only that statement and its axioms.
[The note](docs/mathlib-tm2/mathlib-tm2.pdf) explains the statement.

`IntegerMultBounds/MathlibTM2/Theorem.lean` proves `MathlibTM2.statement : MathlibTM2.Statement`:
a fixed `Turing.FinTM2` machine multiplies in worst-case time `O(n (log n)^(1-κ))` for an
explicit `κ > 0`. Read `Statement.lean` (its imports are Mathlib only). With the
required dependency artifacts available, run
`python3 scripts/check-lean-safe.py CompletedProofCheck.lean` to check the public
bound and audit its complete proof import closure. The audit permits only
`propext`, `Classical.choice` and `Quot.sound`; an unapproved axiom fails the check. [The note](docs/fast-mult/fast-mult.pdf) describes the
machine and the proof.

## Status

The end-to-end Mathlib proof is complete, with no remaining algorithmic or
runtime assumptions, at `kappa = 4222422970/2^46 ≈ 0.00006000424`.
The running supplier uses the fully checked design-B compiler and frame geometry,
including its actual cost histogram and reversed execution. This improves the
saving by about 27.97%, or 0.35576 bits, over the previous plain-frame result.

The long-term direction is an unconditional `kappa = 0.0023`, following the productive
helper jobs, finite mixed-to-uniform compiler, delayed BIT cover, and outer assembly of
[upstream PR 4359](https://github.com/CrocSwap/integer-mult-bounds/pull/4359).
That upstream construction is conditional, and the target is not proved here.
[PLAN.md](PLAN.md) keeps smaller checked improvements on the path, with design-B completed and explicit dependencies for the new construction.

The superseded native controller and its unused wrappers have been removed.
The [retirement record](docs/retired-compact-complex.md) lists the deleted
modules and how to recover them from Git history.

## Building and verification

Install the version of Lean in `lean-toolchain`, then use the guarded local
verification commands:

```sh
python3 scripts/build-lean-guarded.py IntegerMultBounds
python3 scripts/check-lean-safe.py AxiomAudit.lean
python3 scripts/check-lean-safe.py CompletedProofCheck.lean
```

For local component checks, use `python3 scripts/check-lean-safe.py FILE`.
This runner permits one check per workspace, uses one Lean thread and a
24576 MiB Lean memory limit, and stops the process group if its observed RSS
exceeds 28672 MiB or the check runs past twenty minutes. It also stops child
processes if monitoring fails or the check is interrupted. Dependencies must already have compiled artifacts;
it does not launch a broad build. The guarded build stops at 80 GiB combined
RSS or three hours. Both runners share one workspace-wide lock.

To locate memory growth within a file, use
`python3 scripts/profile-lean-prefixes.py FILE --through LINE1 LINE2 ...`,
choosing increasing line numbers immediately after complete declarations or
sections. Each check uses a fresh source copy ending in `#exit` and the same
guard and cached imports; the original file and production build artifacts are
untouched. Start with the imports, then section boundaries, then add boundaries
around declarations in the interval where the peak rises. Results and logs go
to a fresh directory under `.lake/profiling`. Use `--serialize` to measure
partial-module serialization too. Failed checks stop the sweep and are not
valid measurements. These are cumulative prefix peaks, not exclusive
allocations: earlier peaks can hide later costs, and allocator retention makes
subtracting peaks unsuitable for attributing exact memory to one theorem.
For a machine-readable single-file measurement, the guard also accepts
`--report-json PATH` before the file argument; elapsed time excludes lock waiting.

Lean and mathlib are pinned to v4.34.1; `lake-manifest.json` pins transitive
dependencies. No theorem in this project uses a custom axiom or an admitted
proof.

`AxiomAudit.lean` checks public and private project declarations, transitively,
allowing only Lean's standard `propext`, `Quot.sound`, and `Classical.choice`.
It rejects admitted proofs, custom axioms, and native-evaluation axioms. CI
builds the project and runs this audit.

## References

### Primary sources

- Douglas Colkitt, *A sharper exponent for integer multiplication*, research
  draft, [CrocSwap/integer-mult-bounds](https://github.com/CrocSwap/integer-mult-bounds),
  commit [`6e56487`](https://github.com/CrocSwap/integer-mult-bounds/tree/6e564879f51ae16f23d392e9e196c605f36d90df)
  (October 7, 2026).
- Its pinned OpenAI manuscript,
  [*Integer multiplication below n log n*](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026),
  in [openai/math](https://github.com/openai/math), commit `adc7f12`.
- David Harvey and Joris van der Hoeven,
  [*Integer multiplication in time O(n log n)*](https://doi.org/10.4007/annals.2021.193.2.4),
  Annals of Mathematics 193(2), 2021, 563–617. The upstream proof uses this
  multiplier as a subroutine. Lemma and section numbers in `NLogN/` refer to the
  [author-hosted manuscript](https://www.texmacs.org/joris/nlogn/nlogn.pdf).

### Classical results formalized here

- J. W. Cooley and J. W. Tukey, [*An algorithm for the machine calculation of
  complex Fourier series*](https://doi.org/10.1090/S0025-5718-1965-0178586-1),
  Mathematics of Computation 19(90), 1965, 297–301. (`NLogN/FFT.lean`)
- A. Schönhage and V. Strassen, [*Schnelle Multiplikation großer
  Zahlen*](https://doi.org/10.1007/BF02242355), Computing 7, 1971, 281–292.
  (`Schoenhage/`)
- L. I. Bluestein, [*A linear filtering approach to the computation of discrete
  Fourier transform*](https://doi.org/10.1109/TAU.1970.1162132), IEEE
  Transactions on Audio and Electroacoustics 18(4), 1970, 451–455.
  (`NLogN/Bluestein.lean`)
- R. C. Agarwal and J. W. Cooley, [*New algorithms for digital
  convolution*](https://doi.org/10.1109/TASSP.1977.1162981), IEEE Transactions
  on Acoustics, Speech, and Signal Processing 25(5), 1977, 392–410.
  (`NLogN/Multidim.lean`)

### Lean libraries

- [complexitylib](https://github.com/SamuelSchlesinger/complexitylib), commit
  [`3f4b5fe`](https://github.com/SamuelSchlesinger/complexitylib/tree/3f4b5fee8bbd49721a5b70473c81bf3db2e7500d),
  for the machine composition design (no code imported).
- [mathlib4](https://github.com/leanprover-community/mathlib4), v4.34.1.

The local `integer-mult-bounds/` checkout is reference material and is ignored
by this project's Git repository. The Lean project does not execute or trust
the source repository's Python certificates.

## License

[MIT](LICENSE).
