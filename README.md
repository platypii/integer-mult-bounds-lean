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
| Simultaneous butterfly layers with compact control | §5, §11, CrocSwap | ✅ | 🟡 | One fixed original-input stage machine handles every positive width and source order with exact selected XOR, complete cleanup, paid reversal and the certified width exponent. Literal lists physically regenerate and restore pair headers; their original address semantics equal binary basis changes. Actual complex25 edges supply all residual witnesses and their words, including the original signed phase identities. Actual multiplier scalars and once-padded descendant rows give a uniform complete-list machine bound without supplied repair allowances or branch decisions. The actual individual-axis cutoff now has the required quantitative saving relative to the certified dimension exponent. One fixed forward small-dimension fallback now physically synthesizes D*K, sparse selected positions rho+i*K, polynomial multiplicity and an independent precision reservation from original headers, executes every selected axis and erases generated controls; exact sparse Walsh semantics and the actual certified fallback cost are proved for positive D. Its initial native words already have the explicitly enlarged signed width; actual sparse inverse execution and a physical forward/inverse roundtrip now recover exact decoded values at precision q+2D, retaining D*K binary coordinates and polynomial spectators with both passes and cleanup paid under the certified cutoff allowance. one fixed forward or inverse nonfallback reservation controller now physically derives low-back and high-row/front counts from original geometry, runs both sparse intervals, switches and erases generated controls, with exact signed Walsh semantics and decoded roundtrip at precision q plus twice the reserved count. The actual fixed reservation executable and roundtrip now have real paid cost witnesses satisfying uniform native-volume and certified asymptotic bounds, including both header/control lifecycles. These use original full-address native serialization; A fixed paid single-axis machine now retains arbitrary outer rows and polynomial spectators, with literal row-major representation and immutable descendant global-bit placement. Complete sparse scheduling, recursive row-view assembly and D zero identity remain open. Existing uniform-bit row padding still requires valid native zero records before recursive coefficient use. An actual signed dyadic butterfly arithmetic kernel now has exact coefficient semantics, clean private storage and linear word-width runtime with a guard derived from normalized input and prefix depth. Physical delimited record readers now fill its four input controls with linear width cost; A fixed counted record loop now produces both complete butterfly streams with clean arithmetic workspace and linear serialized-volume cost from an original retained count header and blank controls; physical source erasure and all stream-head rewinds are also paid with linear volume cost; one fixed native coefficient machine now composes selected-axis split, full arithmetic, paid cleanup and merge with linear volume cost; its axis descriptors are now physically synthesized, installed and cleaned from original D/t/R/p with a linear-volume bound; one fixed original-header body and counted multi-axis schedule now execute complete native coefficient streams with all generated headers erased and linear-volume-times-axis-count cost; every counted prefix now has derived grid, precision and guard, and actual decoded output equals successive true complex butterfly axes from normalized input; fixed-machine correctness now identifies this native execution with the existing BinaryWalsh kernelRun in the common coordinate layout; fixed original-header inverse schedules now execute the actual negative-phase Walsh kernels with paid split/arithmetic/swapped-merge and cleanup; one fixed forward/inverse machine now physically derives and restores a two-pass reservation, consumes the forward pass grid in its inverse pass and proves exact decoded roundtrip values without renormalization or intermediate resizing; recursive network assembly remains open. Paid three-bit encoding and decoding now preserve exact native coefficient words with linear cost; the actual all-width Boolean stage transports contiguous native symbol codes and arbitrary payload spectators exactly. Standalone destructive converters now physically restore both heads and erase obsolete source words with linear cost; the converters now execute at arbitrary caller slots in the stage alphabet while framing all other tapes. The complete physical stage now returns an explicitly derived valid whole-array native encoding with arbitrary spectators; for payload capacity a multiple of three, converter output and stage input are now literally the same full-address row-major tape, and actual stage output is the decoder source word. One fixed native-symbol stage now composes paid encoding, the actual all-width Boolean stage and paid decoding, erases obsolete words and restores heads/private storage; its complete runtime retains the certified stage exponent under the explicit multiple-of-three payload condition. Actual multiplier choices now select an aligned payload satisfying the existing allowance with fixed-factor overhead and derive all native-stage readiness/packed costs for eventual nonfallback nodes. The same fixed machine now handles the actual stored signed field width including arithmetic guard bits; exact literal complex serialization fixes capacity and derives the converter nonblank condition, and every linearly bounded stored width retains fixed-factor payload overhead. The actual native-stage cost row now restores the exact descendant role divisor and bounds the single global padding by two, preserving the certified exponent against original polynomial volume. The actual native machine now reads and returns the native word at original caller tape65, with its Boolean source and all larger compiled-stage workspace appended and blank at both endpoints; caller/controller framing remains explicit. Recursive coefficient-network assembly remains open. A fixed runtime unit-phase multiplier also has exact signed coefficient semantics and linear width cost; A physical weighted control scanner now feeds the phase kernel with proved original signed phase semantics; Residual control words are now physically extracted from runtime address words, with original phase readout and extraction cost paid by actual payload capacity; A fixed machine now extracts these controls and applies the exact signed phase without supplied controls or phase flags; A live runtime address counter and its original-width initialization are now proved, including record/global-row phase semantics; sparse phase stride/count/offset descriptors are now physically synthesized from original node headers with cost paid by payload capacity; original sparse headers now feed the actual unit-phase caller, and physical record IO plus numerator/control/flag/header cleanup are proved; a fixed original-header counted loop now executes the full live-address/read/phase/emit/reset traversal with exact next clean callers and a uniform linear-record budget; original geometric headers now physically initialize the address counter and derive the full address count as rows times two to address width; one fixed traversal processes a literal array with one coefficient per address, with exact pointwise ordered-phase output and linear serialized-volume cost, including genuine final EOF. Zero residual dimension is an exact tape-preserving identity, and phase negation guards follow from the existing bounded-grid invariant. The one-coefficient-per-address phase machine now erases final live-counter/address storage and physically rewinds source and result streams to zero, with exact native words and all normalization cost paid. A real shared-phase polynomial loop now applies one computed phase to the literal polynomial coefficients, retains nonstream metadata and pays read/arithmetic/emit/reset/count transitions. Its multiplicity is physically derived from an immutable original ell scalar; exact polynomial input/output serialization, EOF positions, stored widths and final control erasure are proved. Original stage metadata and an immutable external current-axis ordinal now have physical setup/copy/final-erasure machines returning the exact original numeric bank, with uniform linear-volume bounds. For supplied phase-kernel parameters m and ws, the prepared-stage outer loop now derives both full-address and polynomial counts, executes the actual inner coefficient loop once per address and erases every count/address control. Uniform physical selection of the actual fixed-network phase kernels, literal whole-array contexts, mathematical phase equivalence, final result normalization/overwrite, caller placement and recursive-network assembly remain open. Actual active-axis power pieces and child-slot paths now derive recursive node geometry; one fixed original-input machine now generates the threshold and computes the exact recursive stop flag with linear scalar cost, and physical child-header production, scalar leaves and exact parent-header restoration are proved; physical exponent descent/ascent and occurrence-specific return-stack primitives are proved; a fixed original-header machine now emits the actual low-to-high base-digit root queue with native tapes framed; paid queue reading and per-digit boundary/clock primitives now match actual root Visit occurrences; actual root queue generation, rewind, descriptor seeding and EOF-controlled outer piece enumeration now execute from the original active header, with exact Visit boundaries and all control costs paid; the callback remains an explicit execution premise, and persistent recursive stacks are supported outside the native private workspace. paid outer cleanup now erases the generated root queue and every numeric descriptor, restoring the exact original fresh controller. Native subroutines and appended descriptor stacks preserve the entire controller/queue/storage frame. physical appended return-address push/pop dispatch, child-header erasure/parent restoration and live controller exponent descent/ascent now preserve the full native/persistent frame. the actual internal-child prefix now composes parent save, literal return-site push, exponent descent and selected-child header installation, and the actual return continuation restores parent descriptors/stack/exponent while retaining the computed payload. Actual stop-test setup, runtime flag selection and cleanup now reach the selected finite continuation with all stop workspace restored and every transition paid. Concrete leaf/internal continuations, recursive execution and role-network return dispatch remain open, together with connecting computed phases to coefficient streams, coefficient record split/merge and guard propagation, complete layer execution and recursive network assembly. Multiplication EndToEnd is unproved. |
| Synthetic transforms and their tape layout | §6 | ✅ | ⬜ | Synthetic ring, principal roots, Bluestein, and the layout counts, round error accumulation, and cost bracket matching the cost table are proved; tape execution is open |
| Gaussian resampling | §7 | ✅ | 🟡 | The factorization `F_s = 2^γ B F_t A` with `‖A‖, ‖B‖ ≤ 1` is proved in one and `d` dimensions, with truncation and Neumann-series error bounds for its pieces; the numerical approximations of `A` and `B` have scaled error below `p²`; the permutation-left variant with its explicit numerical maps, in one and `d` dimensions, and its chirp and cancellation identities is proved; the line counts of the tensor interface match the cost table with negligible setup; on tapes, the row-selecting map `C` is realized by a modular-counter selection machine at linear cost with no numerical error, a signed fixed-point word layer (sign-extending accumulation, negation, truncating multiplication with a quadratic inner product) is in place, and the Gaussian window sums of `Ã` run on a fixed twenty-two-tape machine given the rounded weights, with its accumulators proved equal to the numerical map `Ã`; weight evaluation, `B̃` and the line machines remain open |
| Fast multiplication subroutine | Schönhage–Strassen | 🟡 | ⬜ | The packed products need a multiplier within `m log m (log log m)^c`, whose extra logarithmic overhead is formally absorbed by the certified packed-product margin; the twisted-transform convolution theorem and one Schönhage–Strassen level modulo `2^n + 1` are proved; the recursion, its cost and the tape machines are open |
| Exact multiplication, parameters, time bound | §8 | 🟡 | ⬜ | Parameter margins, asymptotics, prime existence, the size relations, the precision chain to exact recovery of the product, and the cost table rows assembled into `O(n (lg n)^(1-κ))` are proved; short-interval primes and the components' row costs remain open. Exact recovered output now has exactly twice the input length even for nondivisible chunk widths; physical carry propagation and installation remain open. |
| End-to-end theorem `EndToEnd` | — | 🟡 | 🟡 | The complete fixed ordinary multiplier is proved from original input through genuine halting and exact twice-length product output, with quadratic runtime including empty inputs. Fast-path assembly and the final sub-n-log-n bound remain open. |

✅ done · 🟡 partial · ⬜ not started

## Remaining obligations

The target still requires an explicit multiplication program and proofs of its
execution, stream primitives and counters, finite bit and complex networks,
recursive tape scheduling, modular compact controls and their repair costs,
synthetic transforms, Gaussian resampling, prime selection, exact coefficient
arithmetic, rounding, carry propagation, and the final uniform complexity bound.
The upstream proof also invokes an existing fast multiplier as a subroutine,
citing Harvey and van der Hoeven's `O(n log n)` algorithm. Any multiplier within
`m log m (log log m)^c` suffices, since the cost table absorbs the extra factor,
so the `Schoenhage/` directory formalizes Schönhage–Strassen instead: its
transform, one level modulo `2^n + 1`, and (in progress) the recursion and its
tape machines. The `NLogN/` directory keeps the transform, fixed-point,
Kronecker and Gaussian resampling mathematics that the main proof uses. The Harvey–van der Hoeven recursion itself is not needed: the main proof's packed products only require a multiplier within `m log m (log log m)^c`, which the cost table absorbs, so Schönhage–Strassen (`Schoenhage/`) replaces it. Its 28 recursion-only files (step contract, recurrence, cost model, moduli, power-of-two transforms) were removed; restore them with `git checkout 834ad45 -- IntegerMultBounds/NLogN/CRTMulti.lean IntegerMultBounds/NLogN/Capstone.lean IntegerMultBounds/NLogN/Contract.lean IntegerMultBounds/NLogN/ContractFinal.lean IntegerMultBounds/NLogN/ContractPrep.lean IntegerMultBounds/NLogN/ContractSqrt.lean IntegerMultBounds/NLogN/CostBound.lean IntegerMultBounds/NLogN/CostFinal.lean IntegerMultBounds/NLogN/CostModel.lean IntegerMultBounds/NLogN/ExpCostBound.lean IntegerMultBounds/NLogN/ExpEval.lean IntegerMultBounds/NLogN/JointRecurrence.lean IntegerMultBounds/NLogN/MainParams.lean IntegerMultBounds/NLogN/MainRecurrence.lean IntegerMultBounds/NLogN/MainStep.lean IntegerMultBounds/NLogN/MainTransform.lean IntegerMultBounds/NLogN/ModuliConstruction.lean IntegerMultBounds/NLogN/PowerOfTwoContract.lean IntegerMultBounds/NLogN/PowerOfTwoExact.lean IntegerMultBounds/NLogN/PowerOfTwoExactD.lean IntegerMultBounds/NLogN/PowerOfTwoNumeric.lean IntegerMultBounds/NLogN/PowerOfTwoNumericD.lean IntegerMultBounds/NLogN/PrecisionCheck.lean IntegerMultBounds/NLogN/PrimeSelection.lean IntegerMultBounds/NLogN/Recurrence.lean IntegerMultBounds/NLogN/RecurrenceParams.lean IntegerMultBounds/NLogN/ResamplingOps.lean IntegerMultBounds/NLogN/SmallMultiplierCost.lean` and re-add their imports to `IntegerMultBounds.lean`.
None of these algorithmic contracts may be assumed to claim the requested
end-to-end result.

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
