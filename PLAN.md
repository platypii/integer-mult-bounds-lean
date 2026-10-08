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
| Faster interchange of address chunks | §4 | ✅ | ⬜ |
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
| Literal binary addition | `BinaryAdd` | ✅ | ✅ | Three tapes and three states; exact sum in at most width plus one transitions; equally padded operands required |
| Literal binary subtraction | `BinarySub` | ✅ | ✅ | Three tapes and two states; exact width runtime, modular difference and final borrow; equally padded operands required |
| Binary operand padding | `BinaryPad` | ✅ | ✅ | Two tapes, one state, exact maximum-width runtime; values preserved; heads finish at common end |
| Addition with operand preparation | `BinaryArithmetic` | ✅ | ✅ | Raw unequal widths; physical padding, rewind and addition with both joins; runtime ≤ three times maximum width plus five |
| Literal fixed-radix modular addition and subtraction | `RadixDigits`, `RadixAdd`, `RadixSub` | ✅ | ✅ | Finite digit alphabet and two carry/borrow states, three tapes; exact width runtime and halt, canonical modular output and final carry/borrow, complete source preservation; equally padded operands required |
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
| Complex (rational) motif matrices | `CircuitTriples` | ✅ | ⬜ | Exact matrices; dyadic coefficient bounds in `GaussianCircuit` |
| Binary motif matrices over `ZMod 2` | `CircuitBits` | ✅ | ⬜ | Original motif; optimized h=50 replacement is separate |
| Neighbor and wire counts | `NeighborCounts`, `Wires` | ✅ | — | Matches manuscript totals at ground size 100 |
| Degree-one label spaces | `Labels` | ✅ | — | Rational form nondegenerate for size ≠ 9 |
| Tensor-cube label spaces | `TensorLabels` | ✅ | — | Nondegeneracy, dimension, terminal line/complement decomposition |
| Framed circuit compilation | `FramedCircuit` | ✅ | ⬜ | Full finite-circuit common-frame identity, including spectators; exact operators |
| Global circuit with per-invocation scratch | `GlobalCircuit`, `GlobalCircuitBits` | ✅ | ⬜ | Complete three-coordinate scalar schedule and restoration; grouped topology separate |
| Sparse grouped motif gates | `GroupedCircuit` | ✅ | ⬜ | Exact support, eight-row semantics and framed refinement; full grouped exchange separate |
| Binary orthonormalization | `BinaryOrthonormal` | ✅ | — | Nonalternating nondegenerate forms; local witnesses and full global edge coverage proved |
| Local grouped inverse and exchange | `GroupedRouting` | ✅ | ⬜ | Bit/rational semantics and exact support transport; globally embedded by `GlobalGrouped` |
| Neighbor residuals and binary units | `NeighborResidual` | ✅ | — | Actual pair-complement dimension and bases; coordinate witnesses for tensor-line complements |
| Global grouped schedule | `GlobalGrouped` | ✅ | ⬜ | Physical scratch per invocation, middle inverse, sparse support transport and counts |
| Embedded tensor subspaces | `TensorSubspace` | ✅ | — | Actual dimensions, nondegeneracy, orthogonality and sum/inclusion laws |
| Binary diagonal phase decomposition | `BinaryPhase` | ✅ | ⬜ | Rank-one residual and weight-mod-four factorization; Walsh conjugation separate |
| Binary tensor coordinate bridge | `TensorCoordinates`, `LabelTransport` | ✅ | — | Actual isometry to h³ bits; transports labels, residuals and projections |
| Local nested gate labels | `MotifLabels` | ✅ | — | Actual tensor subspaces and unique central decrease; future factor and scratch endpoints included |
| Projection-rank trace accounting | `RankTrace` | ✅ | — | Actual edge ranks telescope; global physical instantiation in `GlobalProjectionRank` |
| Binary one-column translation interface | `BinaryWalsh` | ✅ | ⬜ | Exact finite Walsh conjugation and residual-dimension kernel sequence |
| Full grouped frame compiler | `GroupedFrames` | ✅ | ⬜ | Scalar array identity and actual label history linked to projection-rank balance |
| Stage boundaries and terminal labels | `StageLabels` | ✅ | — | Actual isometries and all X/Y interstage and source/sink identities |
| Sparse physical motif incidences | `MotifSupport` | ✅ | — | Concrete nonzero coefficient/owner tests and central support |
| Binary multi-column interface | `BinaryColumns` | ✅ | ⬜ | Concrete slice operators and exact residual-dimension factor count; unit premise explicit |
| Local residual formulas and binary units | `MotifResiduals`, `BinaryMotifResiduals` | ✅ | — | Thirteen local comparisons plus future/sink at all three stages; physical sparse-history coverage in `GlobalBinaryResiduals` |
| Exact Gaussian-dyadic arithmetic | `GaussianDyadic`, `GaussianCircuit` | ✅ | ⬜ | Concrete motif coefficients, grouped updates, and both binary edge directions; denominator growth proved, numerator bounds in `GaussianPrecision`; tape costs open |
| Binary interface numerator bounds | `GaussianPrecision` | ✅ | ⬜ | Actual kernels and both projection-edge directions; explicit scale and integer numerator bounds |
| Physical local label histories and loss | `LabeledMotif` | ✅ | — | Forward/opposite sparse histories; comparable nondegenerate edges, loss ≤ central count × current dimension, including sinks |
| Rational negative-source correction | `SignedProjection` | ✅ | — | Exact extra source rank for arbitrary nested first label, including skipped vertices |
| Global physical label attachment | `GlobalLabels`, `GlobalLabelsNondegenerate` | ✅ | — | Exact schedule erasure, physical endpoints/stage boundaries, all vertex labels nondegenerate |
| Sparse skipped-edge binary units | `GlobalLabelsResiduals` | ✅ | — | Actual witnesses for xIn→full, yIn→yOut, bot→full, including future factor |
| Physical invocation rank loss | `GlobalRank` | ✅ | — | Actual embedded histories, comparable edges and loss bound; supports weaker input labels left by sparse predecessors |
| Full labeled trace assembly | `GlobalRankStages`, `ProjectionTrace`, `GlobalProjectionRank` | ✅ | ⬜ | Actual global comparable nondegenerate edges, loss bound and projection-rank balance, including terminal alignment |
| Terminal dimension and budget arithmetic | `NetworkBudget` | ✅ | — | Actual source/sink sums and h=25 role count; trace balance/loss premises discharged for h=25 by `ComplexRank25` |
| Orthogonal residual and projection rank | `ProjectionRank` | ✅ | — | Nested nondegenerate labels give actual projection-difference rank |
| Residual rank saving | `ComplexRank25`, `GlobalBinaryResiduals`, `ComplexPhaseBudget` | ✅ | — | Actual h=25 rank sum, full binary residual-factor coverage and uniform complex edge-factor budget proved; optimized h=50 rank bound is proved in Shared50GlobalShear |
| Improved h=50 bit network | `SharedPointMap`, `SharedPointKey`, `SharedPointIntern`, `DisjointCircuit`, `DisjointPruning`, `DisjointBuilder`, `ReversibleFanout` | ✅ | ⬜ | Exact shared-point map, compressed-key interning, output-preserving active-node pruning, DAG primitives and reversible fanout proved; full literal paired-exclusion recursion and concrete 49-vertex input/output semantics proved; the independent checked local witness has 9,813 additions and 1,176 outputs; global sharing counts and actual finite scalar execution are now certified; full global rank, signed physical shear and modular execution are proved for the selected tau; literal tape costs remain open |
| Exclusion-circuit building blocks | `DisjointBalanced`, `DisjointExclusion`, `DisjointPaired` | ✅ | ⬜ | Literal balanced totals, shared prefix/suffix leave-one-out sums and weighted base-case query batches; exact support/value preservation and node upper bounds, not the optimized certificate count |
| Paired-exclusion reconstruction | `PairedPartition`, `PairGrouping`, `PairedReconstruct` | ✅ | ⬜ | Literal pair grouping and recursive decrease; actual single/pair smart-add reconstruction with exact supports and node bounds; full recursive DAG assembly is proved in PairedBlockCorrect; optimized counts remain open |
| Literal paired recursion and query semantics | `PairedCircuit`, `PairedGraphSpec`, `PairedVectorCorrect`, `SupportInterpretation`, `PairedCoarseSupport`, `PairedCoarseCorrect`, `PairedQuerySupport`, `PairedCoarseQuery`, `PairedStripCorrect`, `PairedStripSupport`, `PairedCircuitCorrect`, `PairedReconstructionSupport`, `PairedReconstructionKeys`, `PairedBlockCorrect`, `PairedInitialGraph` | ✅ | ⬜ | Full literal recursion proved correct by strong induction; concrete 49-vertex graph has exact output sums and 1,176 inputs/outputs; active addition and global sharing counts remain separate |
| Interning invariants and certificate checking | `DisjointUnique`, `PairedUnique`, `DuplicateBudget`, `SharedPointMatching`, `MaskDAG`, `MaskSignature`, `MaskUnique`, `PairMask` | ✅ | — | Full recursive support uniqueness; matching-based sharing bound and sound bitmask/signature/uniqueness checkers; concrete local counts, signatures and all 40,256 global duplicate witnesses kernel-checked |
| Checked local 49-vertex witness | `Paired49Certificate`, `Certificates/Paired49/*` | ✅ | ⬜ | All pair-exclusion outputs, 9,813 additions, unique supports, exact endpoint signatures and at most 10,989 compiled scalar roles; independent certificate, not a proof of generator trace equality |
| Actual common-point support family | `SharedPointLift`, `SharedPointFamily` | ✅ | — | Exact local-to-global core/union formulas and 490,650 actual local additions across fifty copies; matching structural hypotheses and all 40,256 genuine duplicate witnesses proved |
| Actual globally interned circuit | `DAGReplay`, `DAGReplayBudget`, `SharedPointOutputMap`, `SharedPointReplay`, `SharedPointExecution`, `SharedPointOutputIndex`, `Shared50Certificate`, `Shared50Finite`, `BoundedCircuit`, `DAGFiniteCompile` | ✅ | ⬜ | Actual fifty-copy DAG and finite scalar program with 58,800 exact outputs, at most 450,394 additions, 509,194 roles and 959,588 XOR updates; every finite-count premise discharged |
| Reversible DAG role allocation | `DAGAllocator`, `DAGAllocatorCount`, `DAGAllocatorFrontier`, `DAGConsumers`, `DAGAllocatorRun`, `DAGCompileCorrect`, `DAGAllocatorBudget`, `DAGValueTransfer`, `DAGInstructionCount`, `Paired49Execution` | ✅ | ⬜ | Actual compiler has exact role and scalar-instruction counts, valid bounded shared-pivot layouts, executable reverse and proved output values from actual input initialization; forward support-frame nesting is proved; reverse/global assembly is proved; tape execution remains open |
| Shared-point source spans | `SharedPointLabels` | ✅ | — | Actual rational spans are positive definite and nested; no nondegeneracy hypothesis |
| Actual forward shared-point frames | `FanoutFrames`, `DAGSupportTrace`, `SharedPointOutputLabels`, `Shared50Frames`, `DAGFramedExecution` | ✅ | ⬜ | Actual interleaved frame/scalar execution on arbitrary module states; increasing nondegenerate support labels and zero forward loss, with exact orthogonal output spans; complementary reverse middle frames proved separately; full motif and global rank assembly proved separately |
| Actual complementary inverse frames | `DAGComplementTrace`, `DAGComplementExecution` | ✅ | ⬜ | Exact reversed-complement labels, increasing edges, zero loss and arbitrary-module inverse execution; actual sinks, full invocation and global assembly proved separately |
| Shared circuit stage frames and physical attachments | `DAGSourceRoles`, `Shared50InitialLabels`, `Shared50OutputRoles`, `Shared50ComplementFrames`, `Shared50StageFrames`, `Shared50FiniteTrace` | ✅ | ⬜ | Actual finite forward/reverse middle traces lift into stage tensor labels with exact endpoints, nondegeneracy and zero loss; input/output physical owners and attachment inclusions are proved; whole invocation and global rank assembly proved separately |
| Actual finite physical middle schedules | `BoundedFramedCircuit`, `Shared50FiniteFramed`, `Shared50FiniteReverseTrace` | ✅ | ⬜ | Physical forward and complementary inverse instructions on the certified finite bank preserve exact scalar erasure and arbitrary-module frame identities; full invocation/global physical assembly remains separate |
| Complete optimized local label histories | `Shared50LabeledInvocation`, `Shared50InvocationRank`, `Shared50OppositeLabels`, `Shared50OppositeRank` | ✅ | ⬜ | Actual forward/opposite finite middle traces plus all sparse-block boundary alignments; exact endpoints, nested nondegenerate edges and loss exactly 2,500 each, including common-input scratch. Exact physical-wrapper linkage is proved; global rank assembly remains separate |
| Complete optimized physical local wrappers | `FramedBlocks`, `FramedEdgeTrace`, `Shared50BlockFrames`, `Shared50FramedInvocation`, `Shared50PhysicalEdges`, `Shared50InvocationPhysicalEdges`, `Shared50OppositeBlockFrames`, `Shared50FramedOpposite` | ✅ | ⬜ | Literal forward/opposite physical programs have exact sparse scalar erasure, arbitrary-module frame identities and exactly the ordered edges of the local rank histories; global physical assembly and tape costs remain open |
| Actual optimized projector operators and global boundaries | `Shared50InvocationProjectionRank`, `Shared50GlobalTrace` | ✅ | ⬜ | Every local physical edge is certified by its genuine rational projector-difference matrix and actual range-rank balance; all reused global boundary attachments have exact endpoints, nondegeneracy and zero loss. Full global trace assembly is proved separately |
| Complete optimized global projection-rank trace | `Shared50GlobalTracePlacement`, `Shared50GlobalTraceNondegenerate`, `Shared50GlobalTraceStages`, `Shared50GlobalProjectionRank` | ✅ | ⬜ | Actual reused three-stage trace reaches the prescribed sinks with nested nondegenerate edges and exact total loss; genuine projector range ranks plus the source correction meet the exact improved rank budget and strict branching bound. Full signed physical interface is proved separately; tape realization remains open |
| Complete optimized signed physical shear | `Shared50GlobalFramed`, `Shared50SignedBoundary`, `Shared50ShearEndpoints`, `Shared50GlobalShear` | ✅ | ⬜ | Actual signed physical two-bank program has exact scalar erasure, uniform full rational address shear on arbitrary binary arrays including dirty scratch, and ordered genuine projector-matrix certificates. The exact total range-rank budget satisfies strict branching; finite-radix realization and tape costs remain open |
| Actual optimized modular edge schedule | `Shared50OperatorPairs`, `Shared50ModularOperators`, `ModularFrameSchedule`, `ModularProgramShape`, `Shared50ModularSchedule` | ✅ | ⬜ | Concrete basis and actual matrix pairs; one good prime works at every radix exponent, preserving routed endpoint identities and exact interchange budget. Each edge reduces one fixed rational program with exact field-operation count; full modular physical assembly is proved separately; tape costs remain open |
| Complete optimized modular physical execution | `Shared50SignedFramed`, `Shared50ModularExecution`, `Shared50ModularControl` | ✅ | ⬜ | One fixed prime, every radix exponent, arbitrary finite arrays including dirty scratch: exact routed full shear, actual ordered field programs and the certified interchange budget. Canonical controls reduce fixed rational instructions with exact field-operation counts and lower-triangular transforms; literal tape execution remains open |
| Actual optimized dirty invocation | `DirtyLinearCircuit`, `Shared50Dirty`, `Shared50Invocation`, `Shared50Exchange` | ✅ | ⬜ | The actual shared program plus fifty central sums executes the twelve-block identity shear, its inverse and local three-invocation exchange, restoring arbitrary scratch; global reused scalar schedule is proved separately; rank assembly is proved separately |
| Sparse optimized invocation | `SparseCircuit`, `Shared50SparseIO`, `Shared50SparseCentral`, `Shared50SparseInvocation` | ✅ | ⬜ | Actual source/readout/central XOR lists with exact incidences and dense-matrix equivalence; sparse twelve-block shear, inverse and local exchange restore dirty scratch; at most 5,209,540 scalar instructions per invocation, not tape steps |
| Optimized stage-reuse matching and labels | `TripleNeighborPermutation`, `Shared50ReuseLabels` | ✅ | ⬜ | Hall-selected actual neighbor bijection, nested nondegenerate stage boundary joins, zero join loss and exact 125,000 rank saving per joined role; reused scalar schedule proved in Shared50GlobalCircuit; global rank trace is proved in Shared50GlobalTraceStages |
| Optimized two-bank endpoint and numerical budgets | `Shared50GlobalBudget`, `Shared50Parameters` | ✅ | — | Actual padded two-bank world count and rational terminal dimension totals; strict branching inequality for the numerical rank budget. Actual trace balance and loss premises are discharged in Shared50GlobalProjectionRank |
| Actual optimized two-bank global program | `Shared50GlobalCircuit` | ✅ | ⬜ | Literal sparse three-coordinate schedule, exact first/third scratch reuse, injective per-stage placements, full data-bank exchange and arbitrary scratch restoration; exact scalar list counts. Physical projector-rank assembly is proved in Shared50GlobalShear; tape costs remain open |
| Rational address-shear interface | `ProjectionRank`, `ShearFrame` | ✅ | ⬜ | Projection ranks, full signed physical frames, finite-radix realization and actual total budget proved; tape realization remains open |
| Phase interfaces and tape compilation | `BinaryRankFactors`, `ComplexPhaseBudget`, `BinaryColumnFrame`, `GroupedModuleFrames`, `FramedFactorExecution`, `ComplexFramedExecution`, `TensorTerminalWeight`, `ComplexEndpoints` | 🟡 | ⬜ | Complete physically placed array-factor run with explicit character/phase corrections equals the full coordinate transform on data and dirty scratch, uniformly in columns; internal instruction count includes all scalar gates; correction costs, scalar-kernel expansion and literal tape costs remain open |

## 4. Faster interchange of address chunks (§4)

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Interchange recurrence and padding arithmetic | `Recurrence` | ✅ | — | `F k ≤ K (m^k)^τ` from `s/W ≤ m^τ`; digit pieces `O(e^τ)`; row, row-range, and radix padding bounds |
| Lower triangular factorization (Lemma 4.1) | `LowerTriangular`, `PivotRank` | ✅ | — | `A = E₁ Π E₂` with lower triangular two-sided inverses and a partial permutation `Π` with exactly `rank A` ones |
| Rational matrix shear (Lemma 4.2) | `Shear`, `Modular` | ✅ | ⬜ | Pivot programs, descending triangular updates, prime modulus beyond all denominators, shear modulo `q^b` with exactly `rank A` interchanges; tape cost of the linear operations open |
| Power-width interchange (Prop 4.3) | `Interchange` | ✅ | ⬜ | Three-step interchange, routed frame identity under the shear contract, edge schedule with `Σ rank` interchanges, recursion `O(V (m^k)^τ)`; role-stream split and fixed-tape schedule open |
| Arbitrary-width interchange (Lemma 4.4) | `Recurrence`, `ArbitraryWidth` | ✅ | ⬜ | Row-range digits, row padding, radix padding, and the total `O(u^τ)` per unit volume with an explicit constant; field-order bookkeeping open |

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
| Moduli selection (Lemma 5.1) | `Primes`, `PrimeSelection`, `ModuliConstruction` | ✅ | — | Elementary two-prime-power moduli via pigeonhole, no Chebyshev input; the Chebyshev-bound route is kept as an alternative |
| Assembled numerical transform (Prop 5.2) | `ResamplingMultiNumeric`, `MainTransform`, `ExplicitNumeric`, `ContractPrep`, `PowerOfTwoContract` | ✅ | ⬜ | `F̃_s = 2^γ B̃ F̃_t Ã` with error `2^(γ+4) T log₂ T`; the explicit power-of-two transform meets the `8 T log₂ T` bound |
| Headline recursive-step contract | `Contract`, `ContractSqrt`, `ContractFinal`, `PrimeSelection`, `ModuliConstruction`, `Capstone` | ✅ | ⬜ | The explicit numerical step with the paper's windows is exact with no hypothesis beyond the threshold `n ≥ 2^(2^(1000 d³))`; the capstone ties correctness and the `O(n log n)` operation count to one choice of grids and moduli |
| Operation counts | `CostModel`, `CostBound`, `ResamplingOps`, `SmallMultiplierCost`, `ExpEval`, `ExpCostBound`, `JointRecurrence`, `CostFinal` | ✅ | ⬜ | A full step is `(12 T/r) M(3rp) + O(n log n)` operations with the paper's windows; small products by the plain FFT multiplier, weights by binary splitting; the recurrence closes to `O(n log n)` above `2^(2^624)` |
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
- Compile the proved optimized h=50 modular physical network and its fixed rational control schedule to literal tape execution and prove its recursive time bound.
- Account for complex endpoint corrections in the tape implementation.
- Finish the `NegacyclicKronecker` subroutine component.
- Extend `PowerOfTwoExact` from two coordinates to `d`.
- Compile the finite network interfaces and their arithmetic to literal tape steps.
- Start the tape compilation of §4: ordered-affine field updates, the role-stream split, and the depth-first schedule.
