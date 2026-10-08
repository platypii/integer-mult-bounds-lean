# Plan and progress

A detailed breakdown of the [README](README.md) status table. Each section
matches one README row and splits it into subcomponents. *Mathematics* means
the statements the algorithm relies on are proved in Lean. *Tape* means a
program in the literal machine model is proved correct with a runtime bound.
See [COMPONENTS.md](COMPONENTS.md) for what each file proves.

✅ done · 🟡 partial · ⬜ not started · 🚧 drafted, not yet in the build

## Overview

| Part of the proof | Source | Mathematics | Tape |
| --- | --- | --- | --- |
| Machine model and target statement | §2 | ✅ | ✅ |
| Composition, loops, frames, elementary streams | §2 | ✅ | 🟡 |
| Finite networks with a rank saving | §3 | 🟡 | ⬜ |
| Faster interchange of address chunks | §4 | ⬜ | ⬜ |
| Simultaneous butterfly layers with compact control | §5, §11, CrocSwap | 🟡 | ⬜ |
| Synthetic transforms and their tape layout | §6 | 🟡 | ⬜ |
| Gaussian resampling | §7 | 🟡 | ⬜ |
| `O(n log n)` subroutine | Harvey–van der Hoeven | 🟡 | ⬜ |
| Exact multiplication, parameters, time bound | §8 | 🟡 | ⬜ |
| End-to-end theorem `EndToEnd` | — | ⬜ | ⬜ |

## 1. Machine model and target statement (§2)

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Multi-tape machine semantics | `Machine.lean` | ✅ | ✅ | Finite alphabet, fixed tapes, local transitions |
| Target proposition `EndToEnd` | `Machine.lean` | ✅ | ✅ | Stated, not proved |
| Axiom audit | `AxiomAudit.lean` | ✅ | — | Only `propext`, `Quot.sound`, `Classical.choice` |

## 2. Composition, loops, frames, elementary streams (§2)

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Sequential composition and Hoare contracts | `Composition`, `Hoare` | ✅ | ✅ | Exact one-transition join |
| While loops with potential-based costs | `Loop` | ✅ | ✅ | Clients supply invariants |
| Tape extension and reindexing | `Frame` | ✅ | ✅ | No random access to fields within a tape |
| Alphabet widening and protected regions | `Alphabet`, `Protected` | ✅ | ✅ | Foreign markers need a locality invariant |
| Scan, rewind, copy, move | `Execution`, `Rewind`, `WordTape`, `Copy` | ✅ | ✅ | One transition per symbol |
| Binary counters | `Counter`, `BitTape`, `CounterTape` | ✅ | ✅ | `8n + 2·width` for `n` increments |
| Leading-bit stable partition | `Partition`, `PartitionMarked` | ✅ | ✅ | Sentinel-marked variant composes |
| Concatenation and record reinsertion | `Concatenate`, `Reinsert` | ✅ | ✅ | Source positioning is a precondition |
| One complete radix pass | `PartitionPass` | ✅ | ✅ | Runtime `3·len + 8` |
| Radix sort (list level) | `RadixSort`, `PartitionSort` | ✅ | — | Stable LSB sort, volume identity |
| Key-bit selection for later passes | `KeySelectData` 🚧 | 🟡 | ⬜ | Data-level `keyAt` and flagged split only |
| Full tape radix sort | — | — | ⬜ | Needs key selection, buffer reuse, controller |
| Terminating stream scheduler | — | ⬜ | ⬜ | Counters prove finite-prefix execution only |

## 3. Finite networks with a rank saving (§3)

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Scalar cancellation schedule and bank identity | `Scalar` | ✅ | ⬜ | Eight-step dirty scratch, signed exchange |
| Executable linear circuits | `Circuit`, `CircuitRouting` | ✅ | ⬜ | Instruction counts, not wire counts |
| Complex (rational) motif matrices | `CircuitTriples` | ✅ | ⬜ | Gaussian-dyadic values open |
| Binary motif matrices over `ZMod 2` | `CircuitBits` | ✅ | ⬜ | Grouped-gate topology open |
| Neighbor and wire counts | `NeighborCounts`, `Wires` | ✅ | — | Matches manuscript totals at ground size 100 |
| Degree-one label spaces | `Labels` | ✅ | — | Rational form nondegenerate for size ≠ 9 |
| Tensor-cube label spaces | `TensorLabels` | ✅ | — | Nondegeneracy, dimension, terminal line/complement decomposition |
| Framed circuit compilation | `FramedCircuit` | ✅ | ⬜ | Full finite-circuit common-frame identity, including spectators; exact operators |
| Global circuit with per-invocation scratch | `GlobalCircuit` 🚧 | 🟡 | ⬜ | Embedding and single-invocation effect |
| Full labeled schedule | — | ⬜ | ⬜ | |
| Orthogonal residual and projection rank | `ProjectionRank` | ✅ | — | Nested nondegenerate labels give actual projection-difference rank |
| Residual rank saving | — | ⬜ | — | Nested gate labels, total saving |
| Phase interfaces and tape compilation | — | ⬜ | ⬜ | |

## 4. Faster interchange of address chunks (§4)

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Chunk interchange algorithm and cost | — | ⬜ | ⬜ | Not started |

## 5. Simultaneous butterfly layers with compact control (§5, §11, CrocSwap)

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Radix packing and signed packed additions | `Radix` | ✅ | ⬜ | |
| Dirty-temporary control identities | `DirtyControl` | ✅ | — | Universal integer statements |
| Packed control gadgets | `PackedControl` | ✅ | ⬜ | Slot embedding and tape costs open |
| Ideal toggle permutation and invertibility | `Ideal`, `Permutations` | ✅ | — | Every address, including bad ones |
| Exact destination repair | `Repair`, `ExactRepair` | ✅ | ⬜ | |
| Exceptional-address counts and density | `Counting`, `Density`, `RepairBounds` | ✅ | — | Bound `5 / (128 p³)` |
| Row layout and reservation capacities | `Layout` | ✅ | ⬜ | |
| Extract, sort, reinsert repair records | `Partition`, `Reinsert` | ✅ | 🟡 | Primitives done; key computation and sorting open |
| Assembled repair pipeline with cost | — | ⬜ | ⬜ | |

## 6. Synthetic transforms and their tape layout (§6)

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Principal roots and synthetic ring | `Synthetic`, `SynthConv` | ✅ | — | `ℂ[y]/(yʳ + 1)` |
| Synthetic FFT with shift twiddles | `SynthFFT`, `SynthMultiD` | ✅ | ⬜ | One and `d` dimensions, error `n ε` |
| Complex-to-synthetic embedding | `SynthEmbed` | ✅ | — | Twist is an isometry |
| Bluestein reduction | `Bluestein`, `BluesteinApprox` | ✅ | ⬜ | |
| Tape layout and costs | — | ⬜ | ⬜ | |

## 7. Gaussian resampling (§7)

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Gaussian sums and Poisson summation | `Gaussian` | ✅ | — | |
| Resampling identity (Thm 4.2) | `Resampling`, `ResamplingCLM` | ✅ | — | |
| Norm bound on `S` (Lemma 4.5) | `ResamplingNorm` | ✅ | — | `‖S‖ ≤ 1 + 1/α` |
| Inversion of `T` (Lemma 4.6, Prop 4.7(i)) | `ResamplingInverse`, `ResamplingAssembly`, `Neumann` | ✅ | — | `F_s = 2^γ B F_t A`, `‖A‖, ‖B‖ ≤ 1` |
| `d`-dimensional resampling (Thm 4.1) | `ResamplingMulti` | ✅ | — | |
| Truncation and Neumann errors (Lemmas 4.8–4.12) | `ResamplingApprox`, `OffDiagApprox`, `NeumannApprox` | ✅ | — | |
| Numerical `Ã`, `B̃` (Prop 4.7(ii)) | `ResamplingNumeric`, `ResamplingMultiNumeric` | 🟡 | ⬜ | Error below `p²` in one dimension, `d p²` in `d`; per-term Gaussian evaluations are hypotheses; clamping available via `Clamp` |
| Permutation-left variant | — | ⬜ | ⬜ | |

## 8. `O(n log n)` subroutine (Harvey–van der Hoeven)

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| DFT, convolution theorem, inversion | `DFT`, `Multidim`, `MultidimD`, `CRTMulti` | ✅ | — | |
| Radix-2 FFT and normalized FFT | `FFT`, `NormFFT` | ✅ | ⬜ | Ring-operation counts only |
| Fixed-point framework and error budget | `FixedPoint`, `FixedOps`, `Approx`, `ErrorBudget` | ✅ | — | |
| Tensor approximation lemma | `TensorApprox`, `TensorApproxD`, `TensorApproxV` | ✅ | — | Rectangular composition law open |
| Plain FFT multiplier | `Pipeline`, `Multiplier`, `Kronecker`, `Carry` | ✅ | ⬜ | Exact on bit strings |
| Negacyclic Kronecker substitution (Lemma 2.5) | `NegacyclicKronecker` | ✅ | ⬜ | Exact arithmetic; bit costs open |
| Power-of-two transforms (Thm 3.1) | `SynthEmbed`, `SynthMultiD`, `PowerOfTwoExact`, `PowerOfTwoExactD`, `PowerOfTwoNumeric`, `SynthConvApprox`, `SynthConvApproxD` | 🟡 | ⬜ | exact chain in every dimension; `d`-dimensional synthetic pipeline with error `3 log₂ T′ + 2`; full numerical transform for two coordinates with error `4 t log₂ t + 8 t + 4`; general `d` numerical assembly in progress |
| Steps 1–3 of the recursion (Props 5.2–5.4) | `MainReduction`, `MainStep`, `Section5Approx` | ✅ | ⬜ | |
| Parameter selection and precision | `MainParams`, `PrecisionCheck` | ✅ | — | |
| Final recurrence (Cor 5.5) | `MainRecurrence`, `Recurrence` | ✅ | — | Recursive inequality is a hypothesis |
| Prime selection | `Primes` | 🟡 | — | Bertrand only; short-interval primes open |
| Assembled numerical transform | `ResamplingMultiNumeric` | 🟡 | ⬜ | Numerical `⊗Ã_i`, `⊗B̃_i` with errors `d εA`, `d εB`; Proposition 5.2 assembly in progress |
| Operation counts | `CostModel` | ✅ | ⬜ | Word operations and delegated products; `(12 T/r) M(3rp) + 2880 n log₂ n` |
| Unit-ball clamping | `Clamp` | ✅ | — | Removes the ball side conditions of the composition lemmas |
| Bit costs and tape compilation | — | ⬜ | ⬜ | |

## 9. Exact multiplication, parameters, time bound (§8)

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Parameter slacks and assembly margins | `Parameters` | ✅ | — | Log enclosure proved in Lean |
| Asymptotics and finite-depth recurrence | `Asymptotics` | ✅ | — | |
| Prime existence | `Primes` | 🟡 | — | Short-interval primes open |
| Exact coefficient arithmetic, rounding, carries | `Carry`, `MainReduction` | 🟡 | ⬜ | List level only |
| Complete time bound | — | ⬜ | ⬜ | |

## 10. End-to-end theorem `EndToEnd`

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Explicit multiplication program | — | ⬜ | ⬜ | |
| Correctness on every input length | — | ⬜ | ⬜ | Requires sections 2–9 |
| Uniform runtime `O(n log^(1−83/10¹²) n)` | — | ⬜ | ⬜ | |

## Next steps

- Finish and import the drafted key-selection and global-circuit files.
- Construct sparse grouped gates and nested labels before assembling the residual-rank budget.
- Finish the `NegacyclicKronecker` subroutine component.
- Extend `PowerOfTwoExact` from two coordinates to `d`.
- Build the full tape radix sort from `PartitionPass` and key selection.
- Start §4, the faster interchange of address chunks.
