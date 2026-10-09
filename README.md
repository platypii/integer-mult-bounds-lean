# Integer multiplication in Lean

**Work in progress. The end-to-end multiplication theorem is not proved.**

## Main result

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

## Status

The machine model, the target statement, and a growing set of algorithmic and
analytic components are formalized and checked. See
[COMPONENTS.md](COMPONENTS.md) for a file-by-file summary of what each
component proves and what it leaves open, and [PLAN.md](PLAN.md) for a
detailed status of each row below, broken down by subcomponent.

Rows follow the sections of the OpenAI manuscript, plus the Harvey–van der
Hoeven `O(n log n)` multiplier it uses as a subroutine. *Mathematics* means the
statements the algorithm relies on are proved in Lean. *Tape* means a program in
the literal machine model is proved correct with a runtime bound.

| Part of the proof | Source | Mathematics | Tape | Main gaps |
| --- | --- | --- | --- | --- |
| Machine model and target statement | §2 | ✅ | ✅ | — |
| Composition, loops, frames, elementary streams | §2 | 🟡 | 🟡 | Fixed machines execute initialized mixed affine schedules and actual nonrecursive Shared50 segments from sole array and canonical b/W inputs. Exact output, retained headers, dimension synthesis and complete private-workspace cleanup are proved in linear-volume time; every private tape and tracker returns blank at head zero. Counted pointwise finite-symbol operations also have exact tape proofs, including encoded XOR. Cross-view composition and the full recursive call controller remain open. |
| Finite networks with a rank saving | §3 | ✅ | 🟡 | Optimized finite network algebra and rank certificates are proved. The actual local/global Shared50 scalar XOR lists now execute on fixed tapes with exact data exchange, dirty-scratch restoration and linear stream-time bounds. One width-independent interleaved control list now preserves every role, address operation and scalar gate, with exact recursive-call count and transpose semantics. Certified segment/gate tape machines and explicit call boundaries are available; recursive calls and full network tape assembly remain open. |
| Faster interchange of address chunks | §4 | ✅ | 🟡 | The main binary interchange theorem is proved: one fixed machine uses original five canonical headers, physically selects equal or adjacent widths, returns exact binary rectangular transpose, and restores all private storage. Its actual runtime, including comparisons and dispatch, has the certified exponent 1−296/10^11, including zero widths. The tape checklist is 125/126: only the broader generic rational-matrix compiler remains unfinished, and this fixed algorithm does not require it. Multiplication EndToEnd remains open. |
| Simultaneous butterfly layers with compact control | §5, §11, CrocSwap | ✅ | 🟡 | Packed-word correctness/density, fixed-control early/later repair pipelines and a complete front-target early permutation kernel are proved. Source inspection found that the algorithm keeps its wide target in active coordinates: the kernel premise n*q≤frontCapacity does not follow, and source controls vary with addresses. Direct active-target rotation now has full physical semantics and linear-volume cost for arbitrary width; compact shape synthesis/cleanup and original-array reservation are also proved. The full active-target address layout and physical selected-source extraction are now proved; a fixed linear-cost batch extractor now generates all varying source controls, and selected/control-mask offset arithmetic accepts those rows. Guarded full-slot toggling and both earlier/later-source highest-bit machines are proved, including actual later-source swap–toggle–swap-back and linear full-volume cost. Their supplied descriptor synthesis and compact-caller placement remain separate. Varying-source repair permutations, keys, density and original-rank recovery are proved mathematically; a fixed physical parser now extracts the current fields and controls from genuine short original ranks. A fixed physical destination writer now reconstructs the full rank and replaces V/T/U while retaining every source/back/spectator bit, with exact original-layout destination identity. A fixed early repair sequence now physically parses each original full rank, extracts its current controls and computes the exact guard/inverse/ideal fields with cleaned scratch and linear address-width cost. A fixed physical header producer now derives exact parser and destination-patch starts/widths from original geometry, retains originals and pays for workspace and post-use header erasure. The generated repair headers now have physical arbitrary-caller placement and paid post-use erasure; full-rank patch/key composition and the corresponding later repair integration remain open. Full prefix-field streams and all derived offset headers now generate on tapes with paid cleanup. The complete caller-placed first varying-offset producer now runs from eight original descriptors with all generated streams, headers and workspace erased and a linear prefix-table bound. Generated offsets can now be physically repeated over arbitrary original row counts, including zero rows and empty words, with exact output and linear repeated-volume cost. A complete varying control-mask producer now supplies the second operand for correction with all source/header cleanup paid. The positive parity-XOR producer also has exact current-prefix rows, cleanup and a linear bound. Complete current-prefix B-minus-A correction now also physically generates both operands and erases all arithmetic/header scratch with a linear bound. Pure parity offset production now also reads exact current target bits and restores all workspace with a linear bound. Negative parity-XOR production now composes real rowwise negation, count/width synthesis and complete cleanup. All four early-load offset types have clean original-descriptor producers and exact bridges to the unchanged target/back prefix coordinates, including compact T/back exchange; the complete first selected load now physically generates/repeats offsets, synthesizes all rotation descriptors, rotates and erases every auxiliary tape, with linear full-volume cost under explicit prefix-table absorption. The compact pure-parity payload load also executes from original descriptors with exact before/after layout semantics, caller placement and complete cleanup under explicit absorption. The complete correction load now physically generates the actual control-minus-selected rows, repeats, rotates the wide active target and cleans every auxiliary slot under explicit absorption. The negative parity-XOR compact payload load is also complete with caller placement, exact signed offset/layout semantics and full cleanup. All four individual early payload actions now execute from original descriptors under explicit prefix-table absorption and have clean arbitrary-caller placements for shared sequencing. Full physical swap sequencing, derivation of absorption from reservation geometry, address-dependent repair keys and final permutation/repair wiring remain open. The full multiplier EndToEnd theorem is still unproved. |
| Synthetic transforms and their tape layout | §6 | ✅ | ⬜ | Synthetic ring, principal roots, Bluestein, and the layout counts, round error accumulation, and cost bracket matching the cost table are proved; tape execution is open |
| Gaussian resampling | §7 | ✅ | 🟡 | The factorization `F_s = 2^γ B F_t A` with `‖A‖, ‖B‖ ≤ 1` is proved in one and `d` dimensions, with truncation and Neumann-series error bounds for its pieces; the numerical approximations of `A` and `B` have scaled error below `p²`; the permutation-left variant with its explicit numerical maps, in one and `d` dimensions, and its chirp and cancellation identities is proved; the line counts of the tensor interface match the cost table with negligible setup; on tapes, the row-selecting map `C` is realized by a modular-counter selection machine at linear cost with no numerical error, a signed fixed-point word layer (sign-extending accumulation, negation, truncating multiplication with a quadratic inner product) is in place, and the Gaussian window sums of `Ã` run on a fixed twenty-two-tape machine given the rounded weights, with its accumulators proved equal to the numerical map `Ã`; weight evaluation, `B̃` and the line machines remain open |
| `O(n log n)` subroutine | Harvey–van der Hoeven | 🟡 | ⬜ | The explicit numerical recursive step is proved exact with no external hypothesis, the moduli being built elementarily above a constant threshold; in the operation-count model a cost bounded by one full step with concrete small-product and weight-evaluation costs is proved `O(n log n)`; tape compilation is open |
| Exact multiplication, parameters, time bound | §8 | 🟡 | ⬜ | Parameter margins, asymptotics, prime existence, the size relations, the precision chain to exact recovery of the product, and the cost table rows assembled into `O(n (lg n)^(1-κ))` are proved; short-interval primes and the components' row costs remain open. Exact recovered output now has exactly twice the input length even for nondivisible chunk widths; physical carry propagation and installation remain open. |
| End-to-end theorem `EndToEnd` | — | 🟡 | 🟡 | The complete fixed ordinary multiplier is proved from original input through genuine halting and exact twice-length product output, with quadratic runtime including empty inputs. Fast-path assembly and the final sub-n-log-n bound remain open. |

✅ done · 🟡 partial · ⬜ not started

## Remaining obligations

The target still requires an explicit multiplication program and proofs of its
execution, stream primitives and counters, finite bit and complex networks,
recursive tape scheduling, modular compact controls and their repair costs,
synthetic transforms, Gaussian resampling, prime selection, exact coefficient
arithmetic, rounding, carry propagation, and the final uniform complexity bound.
The upstream proof also invokes an existing `O(n log n)` multiplier as a
subroutine. The `NLogN/` directory formalizes the mathematics of the
Harvey–van der Hoeven algorithm at the level of vectors and operators:
transforms, convolution theorems, fixed-point error propagation, Bluestein and
synthetic transforms, the Gaussian resampling identity with its norm bounds,
the parameter selection, the explicit numerical recursive step proved exact,
the final recurrence, and an operation-count model. What remains for the
subroutine is compiling the whole algorithm to tape steps with its bit cost;
the moduli are constructed elementarily, so no number-theoretic input beyond
Bertrand's postulate is used. None of these algorithmic
contracts may be assumed to claim the requested end-to-end result.

## Building and verification

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
- L. I. Bluestein, [*A linear filtering approach to the computation of discrete
  Fourier transform*](https://doi.org/10.1109/TAU.1970.1162132), IEEE
  Transactions on Audio and Electroacoustics 18(4), 1970, 451–455.
  (`NLogN/Bluestein.lean`)
- R. C. Agarwal and J. W. Cooley, [*New algorithms for digital
  convolution*](https://doi.org/10.1109/TASSP.1977.1162981), IEEE Transactions
  on Acoustics, Speech, and Signal Processing 25(5), 1977, 392–410.
  (`NLogN/Multidim.lean`, `NLogN/CRTMulti.lean`)

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
