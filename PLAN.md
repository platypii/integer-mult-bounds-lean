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
| Faster interchange of address chunks | §4 | 🟡 | ⬜ |
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
| Key-bit selection for later passes | `KeySelectData`, `KeySelect` | ✅ | ✅ | Unary tape selects arbitrary valid index; exact runtime ≤ three input volumes |
| Flag removal and source erasure | `DropFlag` | ✅ | ✅ | Exact flagged volume; arbitrary records; restores empty marked source |
| Arbitrary-key flagged stable pass | `KeyPartition` | ✅ | ✅ | Six tapes, fifteen states; exact runtime ≤ eleven raw volumes plus twelve |
| Arbitrary-key raw stable pass | `KeyPass` | ✅ | ✅ | Seven tapes; output flags removed; exact runtime ≤ seventeen raw volumes plus nineteen |
| Reusable stable pass and cleanup | `Erase`, `KeyPassReuse` | ✅ | ✅ | Exact fresh physical bank restored; runtime ≤ twenty-six raw volumes plus forty-one |
| Full tape radix sort | `UnarySelector`, `TapeRadixSort` | ✅ | ✅ | Fixed eight-tape machine, exact sort, runtime ≤ 74 × width × volume; prepared width/markers are preconditions |
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
| Global circuit with per-invocation scratch | `GlobalCircuit`, `GlobalCircuitBits` | ✅ | ⬜ | Complete three-coordinate scalar schedule and restoration; grouped topology separate |
| Sparse grouped motif gates | `GroupedCircuit` | ✅ | ⬜ | Exact support, eight-row semantics and framed refinement; full grouped exchange separate |
| Binary orthonormalization | `BinaryOrthonormal` | ✅ | — | Nonalternating nondegenerate forms; concrete residual witnesses remain open |
| Local grouped inverse and exchange | `GroupedRouting` | ✅ | ⬜ | Bit/rational semantics and exact support transport; global grouped embedding separate |
| Neighbor residuals and binary units | `NeighborResidual` | ✅ | — | Actual pair-complement dimension and bases; coordinate witnesses for tensor-line complements |
| Global grouped schedule | `GlobalGrouped` | ✅ | ⬜ | Physical scratch per invocation, middle inverse, sparse support transport and counts |
| Embedded tensor subspaces | `TensorSubspace` | ✅ | — | Actual dimensions, nondegeneracy, orthogonality and sum/inclusion laws |
| Binary diagonal phase decomposition | `BinaryPhase` | ✅ | ⬜ | Rank-one residual and weight-mod-four factorization; Walsh conjugation separate |
| Binary tensor coordinate bridge | `TensorCoordinates`, `LabelTransport` | ✅ | — | Actual isometry to h³ bits; transports labels, residuals and projections |
| Local nested gate labels | `MotifLabels` | ✅ | — | Actual tensor subspaces and unique central decrease; future factor and scratch endpoints included |
| Projection-rank trace accounting | `RankTrace` | ✅ | — | Actual edge ranks telescope; concrete endpoint and loss enumeration separate |
| Binary one-column translation interface | `BinaryWalsh` | ✅ | ⬜ | Exact finite Walsh conjugation and residual-dimension kernel sequence |
| Full grouped frame compiler | `GroupedFrames` | ✅ | ⬜ | Scalar array identity and actual label history linked to projection-rank balance |
| Stage boundaries and terminal labels | `StageLabels` | ✅ | — | Actual isometries and all X/Y interstage and source/sink identities |
| Sparse physical motif incidences | `MotifSupport` | ✅ | — | Concrete nonzero coefficient/owner tests and central support |
| Binary multi-column interface | `BinaryColumns` | ✅ | ⬜ | Concrete slice operators and exact residual-dimension factor count; unit premise explicit |
| Full labeled schedule | — | 🟡 | ⬜ | Local table and all stage boundaries proved; attach to global physical group history |
| Orthogonal residual and projection rank | `ProjectionRank` | ✅ | — | Nested nondegenerate labels give actual projection-difference rank |
| Residual rank saving | — | ⬜ | — | Nested gate labels, total saving |
| Rational address-shear interface | `ProjectionRank`, `ShearFrame` | 🟡 | ⬜ | Projection ranks and exact endpoint/frame identities; finite-radix realization and total budget open |
| Phase interfaces and tape compilation | — | ⬜ | ⬜ | |

## 4. Faster interchange of address chunks (§4)

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Interchange recurrence and padding arithmetic | `Recurrence` | ✅ | — | `F k ≤ K (m^k)^τ` from `s/W ≤ m^τ`; digit pieces `O(e^τ)`; row, row-range, and radix padding bounds |
| Lower triangular factorization (Lemma 4.1) | — | ⬜ | — | `A = E₁ Π E₂`, `Π` with exactly `rank A` ones |
| Rational matrix shear (Lemma 4.2) | — | ⬜ | ⬜ | Pivot sequence, triangular ordered updates, specialization to `ℤ/q^b` |
| Power-width interchange (Prop 4.3) | — | ⬜ | ⬜ | Role streams, frame identity, recursive call count `s` |
| Arbitrary-width interchange (Lemma 4.4) | — | ⬜ | ⬜ | High-digit row field, digit pieces, radix padding |

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
| Extract, sort, reinsert repair records | `Partition`, `Reinsert` | ✅ | 🟡 | Extraction/sorting/reinsertion primitives done; repair key computation and composition open |
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
| Truncation and Neumann errors (Lemmas 4.8–4.12) | `ResamplingApprox`, `OffDiagApprox`, `OffDiagApproxSqrt`, `NeumannApprox` | ✅ | — | Square-root windows as in the paper |
| Numerical `Ã`, `B̃` (Prop 4.7(ii)) | `ResamplingNumeric`, `ResamplingMultiNumeric`, `ExplicitNumeric` | ✅ | ⬜ | Explicit maps with error below `p²` in one dimension and `d p²` in `d`, no side conditions |
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
| Power-of-two transforms (Thm 3.1) | `SynthEmbed`, `SynthMultiD`, `PowerOfTwoExact`, `PowerOfTwoExactD`, `PowerOfTwoNumeric`, `PowerOfTwoNumericD`, `SynthConvApprox`, `SynthConvApproxD` | ✅ | ⬜ | Exact chain and numerical error `T′ (3S + 2εa + 4) + εa + 2` in every dimension; packaging as the recursive step's `F̃_t` in progress |
| Steps 1–3 of the recursion (Props 5.2–5.4) | `MainReduction`, `MainStep`, `Section5Approx` | ✅ | ⬜ | |
| Parameter selection and precision | `MainParams`, `PrecisionCheck` | ✅ | — | |
| Final recurrence (Cor 5.5) | `MainRecurrence`, `Recurrence`, `RecurrenceParams` | ✅ | — | Parameter facts at `d = 1729` proved; the recursive inequality for an actual cost is a hypothesis |
| Prime selection (Lemma 5.1) | `Primes`, `PrimeSelection` | 🟡 | — | Moduli selected from the Rosser–Schoenfeld bound on `ϑ`, isolated as a hypothesis; that bound is not in mathlib |
| Assembled numerical transform (Prop 5.2) | `ResamplingMultiNumeric`, `MainTransform`, `ExplicitNumeric`, `ContractPrep`, `PowerOfTwoContract` | ✅ | ⬜ | `F̃_s = 2^γ B̃ F̃_t Ã` with error `2^(γ+4) T log₂ T`; the explicit power-of-two transform meets the `8 T log₂ T` bound |
| Headline recursive-step contract | `Contract`, `ContractSqrt`, `PrimeSelection` | ✅ | ⬜ | The explicit numerical step is exact with the paper's windows; moduli supplied under the Chebyshev-bound hypothesis, elementary construction in progress |
| Operation counts | `CostModel`, `CostBound`, `ResamplingOps` | ✅ | ⬜ | Word operations and delegated products for the pipelines and the resampling maps; a full step is `(12 T/r) M(3rp) + O(n log n)` given quasilinear weight evaluation; joint recurrence and exp evaluation in progress |
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

- Prepare sorting metadata and compute repair keys, then compose extraction, sorting and reinsertion.
- Attach nested labels to the global grouped exchange and assemble the residual-rank budget.
- Finish the `NegacyclicKronecker` subroutine component.
- Extend `PowerOfTwoExact` from two coordinates to `d`.
- Compile the finite network interfaces and their arithmetic to literal tape steps.
- Start §4, the faster interchange of address chunks.
