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
| Simultaneous butterfly layers with compact control | §5, §11, CrocSwap | ✅ | 🟡 | Actual compact-control interchanges, repair, reservation, padding and phase execution have literal tape semantics, clean workspace and certified component costs. Complete named scalar-array sequences now have the original complex-circuit semantics, with every intermediate guard derived from the actual dependency Path and retained-width reserve, eventually paid by the original chunk choice. Actual named scalar sequences execute complete polynomial arrays, replace source streams, restore heads and private tapes, and physically increment a common live denominator once per completed row. A complete actual stopped-call roundtrip now selects and saves its target, enters and executes the original-codec child, pops the real return PC and restores parent geometry and target stacks with full paid cost. Old live7 and generated target8 remain available for the shared-grid handoff. Leaf and nonleaf return policies, physical target-word construction and actual runtime stopping-test selection are proved, with full workspace cleanup and preserved controller stacks. Literal spectator numerator promotion now proves common child-return precision and the advanced sibling budget from actual dependency Paths; fixed all-spectator promotion now physically synthesizes each gap from live/target headers and preserves the selected role and controller frame. Actual role serialization identifies its physical endpoint with these shared-grid arrays; stream-volume headers now physically derive from retained raw geometry and are fully erased after promotion, with uniform actual native/role-volume setup and cleanup bounds. Actual scalar streams now share their named permanent role tapes and storage7 live denominator, preserving the remaining controller frame and reclaiming all private work. Original count-header production is now proved from retained native geometry with complete cleanup; its setup and final header-erasure costs have uniform original-native-volume bounds. The actual root-bank producer now supplies scalar Ready directly from retained geometry and literal native role streams while preserving live7 and all stacks. The complete actual scalar lifecycle now composes original count setup, named role execution and final count erasure, with literal output, advanced live denominator, all private storage blank and a uniform fixed-block linear volume bound. The scalar lifecycle now exposes the dependency-derived numerical output grid; contiguous scalar prefixes share one full-network growth allowance. Actual grouped vertices now derive their named scalar blocks and full-network boundaries internally, with paid physical execution preserving the node budget. Each group now retains the exact next original scalar-prefix grid, enabling successive groups to share the single growth allowance. One combined actual group-step theorem now supplies its literal next native caller, retained widths, tighter numerical grid, physical live header and upper ledger with the full paid runtime. Their literal outputs are now identified with the genuine native polynomial rows consumed by subsequent physical events, retaining dimensions and field widths without conversion. Complete scalar output reconstructs the literal next raw caller bank, preserving all descriptors and stacks while advancing live7 and restoring blank count storage. The fixed promotion/commit sequence now installs the common live denominator after all spectators are physically aligned, with full cleanup and paid joins. The dependency Path now derives target capacity and absorbs promotion/commit header costs into actual role volume, with physical live-progress now propagated through actual scalar lifecycles, genuine child entry and complete stopped aligned returns; every completed event prefix now also has an exact true-denominator formula and counted upper ledger. Instantiating those local endpoint contracts in full unstopped induction remains open. The complete stopped call now composes its ledger roundtrip with a second paid parent codec lifecycle, generated-volume spectator handoff and live installation, restoring the literal parent bank and all private workspace. The complete root enumeration lifecycle now separates the actual callback runtime sum from a controller overhead proved linear in original native/serialized volume, including queue and numeric cleanup. Exact fixed-role precision contraction now has literal tape endpoints and paid runtime, with coarser-grid membership proving exact signed division; the actual controller-bank nonleaf adapter now generates length metadata, contracts all role fields, cleans up and commits the genuine target. The complete all-role contraction, generated metadata cleanup and live commit now have uniform native/role-volume runtime bounds derived from the Path and true live ledger. The actual interleaved schedule now has exact named scalar/call counts and its completed local denominator endpoints derive the lower ledger covering the real nonleaf target. A finite node compiler now uses actual named scalar lifecycle programs and local child machines on one unchanged common caller bank, charging all local costs and joins and restoring private workspace. It remains a local composition theorem; fixed cyclic recursive closure and the child contracts are still open. Completed-network correctness and construction of the local child executions in a fixed cyclic dispatcher remain recursive induction obligations. The fixed cyclic return controller now preserves the literal full scalar/native/role caller bank through actual PC decoding and genuine root halting; the same actual caller return flow now includes a fixed blank workspace suffix for the arithmetic subroutines. Four disjoint fixed entry/stopped/nonleaf/return PCs are now reserved without changing the original saved-return encoding, on that full caller and workspace bank. The original schedule now has unique child/scalar occurrences and exact child-return event successors with injective fixed event PCs. Actual saved call PCs now decode in the common address space with their literal original saved bits unchanged and event-entry disjointness proved. The actual fixed-event path assembly now requires local proofs only at reachable caller prefixes, sums all local costs and connects to genuine root halting. Physical nonleaf payload entry now parks the retained master and spectators with separate generated counts, moves the selected source and restores the literal raw headers, with a uniform native-volume runtime bound paying both header lifecycles and every join. Child splitting, denominator handoff, reverse restoration, physical event paths and recursive execution remain open. The fixed cyclic table now contains the original decoded returns, four controls and actual event schedule, with exact successor edges and code independent of runtime depth; local programme execution still must instantiate those blocks. Completed child semantics now derive the normalized nonleaf return grid while preserving the exact parent scalar-prefix budget and advancing only its returned-volume ledger; concrete address maps and recursive execution remain open. The complete stopped call now has a uniform original-volume-times-child-size runtime bound, including both codec lifecycles, generated headers, alignment, live commit and cleanup. Structural runtime budgets now sum every actual child occurrence, absorb quotient rounding and use the certified branching saving to bound width-dependent local costs, with separate stopped-leaf and internal terms. Actual scalar lifecycles and completed-return metadata now have derived aggregate volume bounds; true child target selection and denominator-stack save/restore are separately paid from changing Paths and live ledgers. Literal child-return codec, exact contraction, spectator promotion/live commit and target/PC restoration costs now have separate Path-derived volume bounds and actual-call sums. The node aggregation is still explicitly partial: nonleaf denominator readiness, selected-child splitting/semantics, actual return sequencing/joins and physical interchange execution must still instantiate the recurrence with child execution. Stopped arithmetic and spectator promotion now preserve the tighter original scalar-prefix grid, with guard capacity derived from the actual Path and exact reserved-role reconstruction; the unchanged complete stopped-call tape adapter now accepts current role arrays directly and returns the literal next caller with that exact prefix bound, retaining parent levels and paying all original costs. That stronger prefix adapter now also has the uniform original-volume-times-child-size runtime bound, with capacity derived from the genuine live prefix ledger. Remaining work includes inherited precision propagation, interleaved unstopped recursive execution, root callback discharge and the uniform physical recursive cost sum. |
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
