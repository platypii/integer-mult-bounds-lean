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
| Simultaneous butterfly layers with compact control | §5, §11, CrocSwap | ✅ | 🟡 | The actual early four-load schedule now constructs consumer headers from original stage widths, executes all real offsets/swaps/rotations and cleans up with the certified width-exponent bound; its bit destinations now equal the packed early arithmetic on every address. Both varying-control full-rank key machines and both scan/sort/strip/reinsert endpoints now derive their own headers, markers and counters from original descriptors and finish with clean workspace and exact literal output. Both complete repair runtimes now have linear payload-volume bounds under explicit width and sparse-hole hypotheses. Both repair endpoints now identify the ideal permutation on address-indexed record streams, and global density pays the sparse-hole bound under explicit dyadic parameter inequalities. Connecting those records to the wide physical array, the later-source payload schedule, reservation/packing-parameter wiring and final butterfly assembly remain open. Multiplication EndToEnd is still unproved. |
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
