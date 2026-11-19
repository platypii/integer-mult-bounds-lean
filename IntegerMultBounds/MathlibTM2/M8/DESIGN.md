# M8: the PR97 bit supplier

M8 replaces the Shared50 recursion behind `Machine/BinaryInterchangeRun` with the two-stage
partial-swap word of PR97. The supplier needs no routes, charts, cover classes or helper hosting.
It runs on the existing recursive interchange machine model. Stage 1 uses rank-one children in the
existing uniform recursion. Stage 2 adds the opposite-bank compiler (variable-rank reversed
children over atom rings, stopped recurrence).

## 1. Numbers

`h = 23`, `v = C(23,3) = 1771`, `m = h² = 529`, `N = v² = 3136441`, `R = 28866` side roles per
invocation, `W = 2N + 2vR = 108516254`, `L = 2vh(h-1) = 1792252`, rank mass
`s = Wm − N + L = 57403754177`, deficit `Wm − s = N − L = 1344189`.

| bit supplier | `a_b` | κ with T16 (≈ 0.45·a_b) |
| --- | --- | --- |
| Shared50 | `2.96·10⁻⁹` | `2^-29.6` |
| stage 1: PR97, rank-one children | `3.734·10⁻⁶` | `2^-19.2` |
| stage 2: opposite bank, plain frames (section 5) | `9.69·10⁻⁵` | `2^-14.5` |
| stage 2: opposite bank, upstream's design-B frames | `1.2402·10⁻⁴` | `2^-14.1` |

The rank-one saving is `(1 − s/(Wm))/ln m` up to the certified grid point; stage 2 is
`(1 − θ)a* + θ·a_leaf` with `θ = 1/1000`, `a*` the whole-projector moment saving and `a_leaf`
the leaf interchange (Shared50 here).

## 2. Sources

Pinned in upstream at `463113d6`, `references/partial-gauge/pr97/` (hashes in its `SOURCE.json`):
- PR97, Zhihao Chen, `jacklightChen/integer-mult-bounds@e15350b6`: the literal ledger
  (`round7_literal_frame_ledger.py`) and `PROOF.md` (two-stage gauges, exits, connectors,
  reflected word, rank-one copy correction).
- Swapnil Jain's round-7 witness, `Swapnil-jain/integer-mult-kappa@741e7aa0`:
  `witness_23.json.gz` (the side DAG: 64042 nodes, 5313 outputs, 23 retained centres,
  38741 links, the flag matrix, lift indices, late copies), `deferred_23.json.gz` (the design-B
  schedule: 82983 ops, deferred readout frames, V-leaf frames), `check_frames.py`,
  `check_lifted.py`, `deferred.py`, `linalg.py`.
- icekylinx's #104 compiler: `notes/stopped-product-factorization.tex`,
  `notes/stopped-product-interface.tex`, `notes/partial-gauge-construction.tex`,
  `certificates/partial-gauge-bit-input.json`, `scripts/partial_gauge_bit.py`.

The ledger replays here unchanged: 1080616 events (856849 XORs, 223744 moves, 23 centre
copies), 90173 frame keys, complete forward and reflected F2 shear, `s = 57403754177`.

## 3. What the tree already has

- **Frames are free in the semantics.** `Networks/FramedCircuit`: any linear equivalences as
  frames; `common_frame_identity` makes the compiled run `encode output ∘ scalar ∘ decode input`,
  and `independent_of_intermediate_frames`. Correctness of a node is scalar correctness plus its
  endpoint frames; intermediate frames only change cost.
- **Field programs.** `AffineFieldProgram.Op`: in-group ordered affine steps, `addToD`,
  `subFromD`, and `interchange i j`, which swaps `H_i` with `D_j` for independent `i`, `j`. The
  tape runs the nonrecursive steps as `OrderedAffine` steps on the flat `H ++ D` vector
  (`AffineFieldCoordinates`) and each `interchange` as one child.
- **Factorization.** `Swap/LowerTriangular.factorization`: `A = E₁ Π E₂`, lower-triangular
  invertible factors and a pivot list with distinct rows and columns; `PivotRank` gives
  `L.length = rank A`. `ModularFrameSchedule` and `Swap/Modular` choose one prime avoiding every
  denominator and reduce rational programs to `ZMod (q^b)`.
- **The machine.** `Shared50Recursive*` over the generic `Recursive*` layer runs any fixed
  control list `List (FramedControlSchedule.Step World (ZMod 2) FieldProgram)` with XOR gates,
  segments and interchange calls. It is hardwired to Shared50 through `roleCount`, `m = 125000`,
  `Shared50PieceSchedule.pieces` and `Shared50FixedControl`; nothing in it depends on what the
  frames mean.
- **Cost.** `Shared50RecursiveBudget.budget (d+1) V = node·V + s·budget d (V/W)` and
  `Swap.Recurrence.power_width_bound`; `BinaryInterchangeBudget.uniform_bound` is the interface
  the cost chain consumes. Stage 2 uses `Layer.VariableRecurrence.variable_closed` plus a stopped
  variant.

`exists_prime_shear` does not give the exchange-frame lemma. It realizes the shear
`H ← H + A D`. A partial swap `D_U` factors through shears only with the within-field
involution `1 − 2U`, which is not lower triangular.

## 4. Exchange-frame edges

For an idempotent `U`, `D_U(h, d) = ((1 − U)h + Ud, Uh + (1 − U)d)`. For commuting idempotents,
`D_A D_B = D_{A+B−2AB}`; for `A ≤ B` (`AB = BA = A`) this is `D_{B−A}`, of rank `rank B − rank A`.

**Lemma (exchange program).** For idempotent `U` with `U = E₁ Π E₂`, the program
`[transformH E₁⁻¹, transformD E₂] ++ cross K ++ [interchange i j | (i,j) ∈ L] ++ cross (−K) ++
[transformH E₁, transformD E₂⁻¹]` runs as `D_U`, with exactly `L.length = rank U` interchanges.
Here `M = E₂E₁`, `P_E = ΠΠᵀ`, `P_F = ΠᵀΠ` and
`K = M P_E − P_F M + P_F M P_E − Πᵀ`; `cross K` is `D ← D + K H`, compiled to unit scalings and
`addToD`.

*Proof.* In the coordinates `(E₁⁻¹h, E₂d)` the map is `g = 1 + C R` with `C = [Π; −MΠ]`,
`R = [−M, 1]`. Idempotency of `U` is `ΠMΠ = Π`, that is `FᵀME = 1` for the pivot columns
`E`, `F` (`Π = EFᵀ`). With `S = [[1,0],[K,1]]`: `SC = [E; (K−M)E]Fᵀ` and `RS⁻¹ = [−M−K, 1]`, and
`K` satisfies `KE = ME − F`, `FᵀK = Eᵀ − FᵀM`. Hence `SgS⁻¹ = 1 + [E; −F][−Eᵀ, Fᵀ]`, the swap of
`h_i` with `d_j` on the pivot pairs. No characteristic assumption is used. ∎

This is the exchange-frame Bruhat statement in constructive form. The same identity holds over `ZMod (q^b)`
after one prime choice that avoids the denominators and the numerators of the scalings.

## 5. Plain frames

**Rank-one cost telescopes.** With rank-one children an edge `D_A → D_B` with `A ≤ B` costs
`rank B − rank A`. Along every wire the frames are nested, so its total is final rank minus initial
rank, plus the paid connectors. The intermediate frames therefore do not change `s`. Stage 1 can
use the simplest nested frames that the gates allow, in place of upstream's design-B frames
(deferred readouts, V-leaf frames, late-copy intersections, the flag `F_j`).

**The choice.** Readouts at frame `0`, at the start of the word. Sources (`slot += x_S`) at the
line `t_S`. The add and copy of node `n` at `span(n) = Σ_{S ∈ supp n} ℚ t_S`, recursively
`span(a) ⊔ span(b)`. Root reads at the root hyperplanes `t_T^⊥` and `U_c`. Centre scatters
through a zero temporary. Idempotents are the `G`-orthogonal projectors, `G = I − J/9`.

**Nondegeneracy is a theorem.** Every support lies in a star `star(c)` (the triples through one
point `c`): supports grow along parents, every node is below a root, and the root supports lie in
`star(c)`. For `S, S' ∋ c`, `G(t_S, t_S') = |S ∩ S'| − 1 = ⟨e_p, e_p'⟩` with `p = S ∖ c`, so on
`span(star c) = U_c` the form is the Euclidean form of the pair vectors `e_p ∈ ℚ^{[h]∖c}`. A
relation `Σ a_p e_p = 0` has `Σ a_p = 0` (count each coordinate twice), so `e_c ∉ U_c` and `G` is
positive definite on `U_c`, hence on every `span(n)`. No per-frame computation is needed.

**Links by pair graphs.** For supports in `star(c)`, `span(n) ≤ span(t)` iff every pair edge of
`n` lies in the span of the unsigned incidence vectors of `t`'s pair graph: both ends in one
component, and on opposite sides if that component is bipartite. 37579 of the 38741 links have
`supp(n) ⊆ supp(t)`; the other 1162 carry a spanning forest and a bipartition or odd-cycle
witness.

**What has to be checked.**
- DAG chains: free (`span(a) ≤ span(a) ⊔ span(b)`).
- Root inclusions: `supp(n) ⊆ {S : |S ∩ T| = 1}` and `supp(n) ⊆ star(c)`, as bitsets.
- Links: support inclusion, or the pair-graph witness.

All checks pass, by computation (`plain.py`, `graphlink.py`).

**Same `s`.** The compiled plain word has `R = 28866`, 91137 ops (62271 adds, 27095 copies,
1771 sources), 555403 start-readout XORs and 10626 root reads. It passes the complete F2 shear on
all 32408 basis vectors (`plainword.py`). Its two-stage histogram has `Wm − s = 1344189`
exactly, so stage 1 has the same `s` and the same `a_b` (`plainhist.py`).

**Stage 2 with plain frames.** The whole-projector moment of the plain histogram gives
`a* = 9.700·10⁻⁵`. Design-B gives `1.2410·10⁻⁴`, a 28% larger saving, by moving rank into larger
blocks: the deferred readout frames `σ_u` enlarge the exteriors. Design-B is a later upgrade with
its own frame certificates (11565 readout and 11374 V-leaf bases, about 15 MB of integer data,
plus exact dimensions of `M_n = span(n) + (U_n ∩ F_j)`).

## 6. The local word: scalar proof

The word is `OPS' ; RR ; OPS'⁻¹ ; OPS ; RR ; OPS⁻¹` (`Local/Word.lean`), where:
- `OPS` is the compiled operation list as XOR gates: source gates `slot += x_S`, additions
  `a[piv] += a[oth]`, and copies;
- `OPS'` is `OPS` without the source gates;
- `RR` adds each root's slot into the targets of the root.

The first pass runs at frame 0, so it costs no edges.

Proof structure:
1. Compiler (`Local/Compile.lean`, `compile_correct`): for every valid DAG, from zero side slots,
   each root's read slot holds the root's value. Validity: arguments precede their node, a link
   names a later use of the same operand, distinct donors serve distinct uses, every node has a
   free use.
2. Word (`word_run`): on arbitrary contents, the first three parts add the side slots' garbage
   into the targets and restore the side slots; the last three add the same garbage and the root
   values. Over `𝔽₂` the garbage cancels: `y_T += Σ_j count(T, targets j) · val(root j)`, with
   sources and side slots unchanged.
3. Checks (`Local/Kernel.lean`, `Local/Checks/*`, `Local/Witness.lean`): every record passes its
   local kernel check, which gives `dag_valid` and `supp_add` (an addition's support is the
   disjoint union of its arguments' supports).
4. Scalar (`Local/Scalar.lean`): the leaf triples increase lexicographically, so they are
   distinct, and `val_eq` sums each node over its support. The output root `(c, T)` has the
   triples meeting `T` exactly in `c` and the centre of `c` has the triples through `c`. The
   triple identity `Σ_{c∈T}[c ∈ S, S∩T = {c}] + Σ_{c∈T}[c ∈ S] ≡ [S = T] (mod 2)`
   (`Local/Triples.lean`) then gives `word_run_target`: `y_t += x_t` for every leaf `t`.

Result: `y += x`, `x` unchanged, side slots restored, on arbitrary dirty contents, on the
standard axioms. The reflected word (time reversed, banks exchanged) is `x += y` by the same
theorem with the register kinds exchanged.

## 7. The global node

Files: `Global/FrameMachine`, `Auto`, `Lift`, `Map`, `Stage`, `StageFrames`, `Node`,
`NodeFrames`, `NodeRun`, `NodeCost`, `Instance`.

**Wires.** Contract roles: the data `X S T` and `Y S T` for triples `S`, `T` (`2N` roles) and
the side slots of the `2v` invocations (`2vR`, `R = 28866`, `slot_count`). Temporaries: one per
stage, invocation and centre, one per data pair, and one unused wire (3217908 in all). Each
temporary is used once. A zero stream is valid in every frame, so each temporary starts in the
frame its first gate needs, and no relabel or reset is needed.

**Framed steps** (`FrameMachine`). A wire in frame `U` stores its logical stream read through
`D_U` mod `p^b`. Moves between nested frames are the exchange programs of their difference; XOR
gates act on wires in one common frame. The physical run is the logical run of the gates,
encoded in the final frames (`run_phys`). Aligned lists (`Auto`) insert the moves before each
gate. They are valid when each wire's frames form a chain of comparable frames (`ChainOk`).

**Stages** (`Stage`, `StageFrames`).
- Stage one, invocation `T`: the doubled local word with frames `K ⊗ Q_T` (`lift1`). Its centre
  reads go through temporaries: copy at the star frame, move to `0`, scatter.
- Stage two, invocation `S`: the blocks of stage one in reverse order with complemented frames,
  each centre block in its own order, lifted to `(1 − P_S) ⊗ 1 + P_S ⊗ K` (`lift2`), with the
  banks exchanged.
- Each stage adds every source into its target (`stage1_run`, `stage2_run`). Along every local
  register the frames increase (`chain1_aux`, `chain1_x`, `chain1_y`), and stage two sees them
  reversed and complemented (`fseq2_reg`).

**Gauges.** `X S T` starts in `U = P_S ⊗ Q_T`, the frame of its source gate. After the
correction (`ct += X` at frame `1`, then `Y += ct` at frame `1 − U`), `Y S T` ends in `1 − U`. On
scalars the node maps `(x, y) ↦ (y, x)` (`node_scalar`). With `D_U D_{1−U} = D_1`, every contract
role ends with its route's stream, address fields exchanged (`node_run`).

**Cost.** Interchanges are wire sums of move ranks (`edgeRanks_autoSteps`). The contract roles
climb monotone chains: `528` for `X` and `Y`, `529` for side slots, including the final sinks
to `1`. Centre temporaries make one move of rank at most `22`, and correction temporaries one
of rank `1`. In all, `calls ≤ s₀ = 57403754177` (`calls_node_le`).

**Instance.** `pr97₀ : BitNetwork` (`Instance`) takes `rankSum := calls control`. Branching
comes from `Branching97.branching` at `s₀`. Its run identity is `node_run`, moved to the
structure's decidable-equality instance by `run_inst`. `pr97` seals it with `irreducible_def`.
The machine runs it (`runs_pr97`), and its exponent is `Branching97.tau` (`pr97_tau`). All of
these rest on the standard axioms.

**Elaboration of the node.** The node's terms are closed and built from the compiled word. Lean
evaluates them, past 10 GB, whenever it checks a defeq between closed terms that differ
syntactically. That happens in the kernel's numeral reduction under `+` and `*`, after a `simp`
step by a definitional lemma, or after a rewrite whose instance unfolds an abbreviation such as
`V` or `Slot`. It also happens when `whnf` runs over `Valid` of the gate list. The files avoid
this in four ways:
- `allGates` and `sideWires` are `@[irreducible]`, with `allGates_def` and `sideWires_def`;
- proofs about the node use `rw` chains with lemmas stated on the node's own types (`card_V`,
  `card_Slot`);
- sums and counts go through generic lemmas over type variables (`calls_sinks`,
  `sum_costBoundOf`);
- the compiled schedule is used only through generic statements (`compile_chain`,
  `compile_root_nodes`).

## 8. Interface between the word side and the machine side

The structure `M8.BitNetwork` (`BitNetwork.lean`) contains:
- the contract roles `World` with `roleCount` and `roleEquiv : Fin roleCount ≃ World`, and the
  temporaries `Temp` with `tempCount` and `tempEquiv`;
- the width `m` with `2 ≤ m`, and the prime `q` (prime, odd);
- `control : List (Step (World ⊕ Temp) (FieldProgram m))`, with field programs over `ℚ`;
- the route `route : World → World`, an involution;
- the certificates:
  - `calls_exact : calls control = rankSum` (`rankSum` is `s`);
  - `legal` and `legal_mod b`: every field operation is legal over `ℚ` and after reduction mod
    `q^b`;
  - `xor_gate`: every gate is one XOR of two distinct streams;
  - `run_identity b`: on arbitrary contract-role streams and zero temporaries, role `i` ends with
    the stream of `route i`, its two address fields exchanged;
  - `tau` with `0 < tau < 1` and `branching : s / roleCount < m ^ tau`.

The machine side also needs `Runs N` (section 9): the shared prime, the coefficient bound and
`m ≤ roleCount`. The word side (sections 4–7) produces `M8.Global.pr97 : BitNetwork` and `Runs pr97`;
the machine side consumes any network that meets `Runs`. Shared50 is the existing instance in all
but name: its control is `Shared50FixedControl.control`.

## 9. The machine side

`M8/Machine/` is one generic copy of the recursive interchange machine over a `BitNetwork`: the
Shared50 machine (`Shared50Recursive*` and the arbitrary-width wrapper up to
`BinaryInterchangeBudget`) with the network as a parameter.

**Parameter.** `class Net` (`Net.lean`) carries the network and `Supports net`
(`Network.lean`):
- `prime_eq`: the network's prime is `Shared50ModularControl.prime`, the prime of the machine
  alphabet;
- `coeff_supported`: every operation of every edge program has coefficients that the coefficient
  stages accept (`Coordinates.CoeffSupported`). That is a coefficient of Shared50's schedules, or
  any coefficient with numerator and denominator at most
  `Networks.coefficientBound = 2^(2^(2^16))`;
- `width_le_roleCount`: `m ≤ roleCount`, so the row divisor `roleCount^k` of the wrapper
  dominates the width `m^k`.

`Runs net` has the same fields, with every coefficient within the bound (`coeff_bound`), and it
gives `Supports net` (`Runs.supports`). The word side proves `Runs pr97`
(`Global/EdgePrograms`). Shared50 meets only `Supports`: its factorizations are
`Classical.choose` witnesses with no height bound, and its coefficients are accepted because they
occur in its schedules.

**Shared50 as a network.** `Machine/Shared50Network` makes Shared50's fixed control a
`BitNetwork` on its World roles with no temporaries (`network`, sealed with `irreducible_def`)
and `net : Net`:
- the control's run is Shared50's run (`run_step`), so `run_identity` comes from
  `Shared50FixedControl.run_identity`;
- the certificates are Shared50's: calls `s`, legal programs over `ℚ` and mod every `q^b`, XOR
  gates, and branching at `Shared50Parameters.tau`.

Definitions use `variable [Net]` and refer to the network like a global constant. Nothing
evaluates the prime or the bound: comparisons are on exponents, and the prime is a
`Classical.choose` witness.

**Shared prime.** `Shared50ModularControl.prime` is chosen beyond `coefficientBound` and every
Shared50 denominator, and `Shared50AffineCoefficients.Occurs` admits every coefficient within the
bound, so one alphabet serves Shared50 and every network that meets `Runs`. With the `Or.inl`
witnesses in `Shared50NonrecursiveCoordinates`, these are the only edits to existing files;
`Networks/CoefficientBound` is new.

**Temporaries.** The wires are the contract roles and the temporaries (`Wire = World ⊕ Temp`),
each on its own tape, plus one input/output tape. The split and the merge use the contract roles
only. After the split `tempInit` fills every temporary with the zero bit, and after the last piece
`tempClear` blanks them (`NodeLayout`, `NodeData.init_encoded`, `NodeData.clear_network`).
Resets (a fill with the zero bit) are pieces.

**Results** (standard axioms):
- `Induction.contract`: at every depth, the graph started on a canonical source bank returns the
  full H/D transpose to the decoded caller within `Budget.budget k depth V`, with every stack and
  spectator restored;
- `RootExecution.halts_power_bound`: the root program halts within `C·V·width^τ`, `τ = N.tau`;
- `BinaryInterchangeRun.runs` and `BinaryInterchangeRun.uniform_bound`: the width-selecting
  rectangular interchange from five caller headers costs at most `C·V·max(1,h,d)^τ`, the
  interface the cost chain consumes.

The node coefficient is `node k = entry + exit + Σ overhead + tempInit + tempClear + 137 + k`, and
`budget (d+1) V = node·V + s·budget d (V/roleCount)`. For PR97, `m = 529`,
`roleCount = 108516254` and `τ₉₇ = 1 − 3734/10⁹`; `Runs pr97` comes from the word side. Switching
`Parameters.tau` and retuning go through main, since they touch the Cost chain.

**Proof conventions.** `width`, `roleCount` and the tape counts are symbolic. Width facts come
from `two_le_width`, `width_pos`, `one_lt_width`, `two_le_roleCount` and `width_le_roleCount`; no
`decide` touches `width` or its powers. Where a failing tactic alternative would unfold a symbolic
tape count, the proofs list their cases directly or simplify slot values first.

**Module map.** Kenny's module, then its M8 counterpart under `M8/Machine/`.

| Kenny's module | M8 module |
| --- | --- |
| `Networks/Shared50FixedControl`, `Shared50TapeGlobal` | `BitNetwork.control`, `Net` |
| `Shared50NonrecursiveCoordinates` | `Coordinates` |
| `Shared50CleanSegments` | `Segments` |
| `Shared50PieceSchedule`, `Shared50OrderedPieces` | `Pieces` |
| `Shared50PieceSemantics` | `Semantics` |
| `RecursiveXorRoleBank` | `FillRoleBank` |
| `RecursiveMixedSchedule`, `RecursiveMixedInitialized`, `RecursiveMixedClean`, `RecursiveMixedRoleBank` | `RoleOps`, `RoleOpsInitialized`, `RoleOpsClean`, `RoleOpsBank` |
| `Shared50NodeSegments`, `Shared50NodeGates` | `NodePieces` |
| `Shared50NodePieceTransport` | `NodeTransport` |
| `Shared50RecursiveNodeLayout` | `NodeLayout` |
| `Shared50RecursiveNodeSemantics`, `Shared50RecursiveNodeBinary`, `Shared50RecursiveNodePieces` | `NodeData` |
| `Shared50RecursiveChildPermutation` (`child`, `child_spec`) | `ChildPermutation` |
| `Shared50RecursiveSegments`, `Shared50RecursiveGates`, `Shared50RecursiveBankNodes`, `Shared50RecursiveCallLayout` | `BankNodes` |
| `Shared50RecursiveX`, for `X` = `Control`, `Implementation`, `Execution`, `BlockExecution`, `ReturnExecution`, `BaseExecution`, `Root`, `CallSemantics`, `CallRecovery`, `BinaryInvariant`, `PieceExecution`, `NodeBoundary`, `Depth`, `NodeExecution`, `CallReady`, `CallInductionBridge`, `Induction`, `BudgetBound`, `RootExecution` | `X` |
| `Shared50RecursiveBudget`, `Shared50RecursiveBudgetAssembly` | `Budget` |
| `Shared50RecursiveInductionBase`, `Shared50RecursiveBasePermutation` (`source_roles_updated`) | `InductionBase` |
| `ArbitraryWidthPieces` (`slice_shape`, `piece_shape`, `piece_view`) | `ArbitraryWidthPieces` |
| the 76 modules of the arbitrary-width wrapper that depend on `W = 125000` or on the Shared50 root, `ArbitraryWidthSchedule` through `BinaryInterchangeRun` and `BinaryInterchangeBudget` | the same names |

`Network`, `Net` and `BankFacts` are new. Used unchanged: the generic `Recursive*` layer,
`Shared50RecursiveBank`, `Shared50RecursiveBankReturn`, `Shared50RecursiveNodeRows`,
`Shared50RecursiveNodeTranspose`, `encoded` from `Shared50RecursiveNodeSemantics`, `array` and
`toChild` from `Shared50RecursiveChildPermutation`, `array_transpose` from
`Shared50RecursiveBasePermutation`, the generic part of `ArbitraryWidthPieces`, and the 43
arbitrary-width modules independent of `W` and the root (for example `ArbitraryWidthHighLayout`,
the `RadixHighBlockJoin*` chain and the `BinaryAdjacentWidth*Shared` banks). At integration the
Shared50-specific modules on the left become candidates for retirement.

## 10. Certificate engineering

- **Kernel cost model** (one thread, guarded checker):
  - records are structures and the checks apply the `Nat` functions themselves (`Nat.add`,
    `Nat.land`, …) to their fields, which the kernel evaluates on literals directly; instance
    arithmetic and `let`-bound fields cost about 0.5–1 ms per operation;
  - a lookup in the static tree of 65536 records (depth 16, through `Tree.rec`) costs about
    0.7 ms;
  - pair sets are 529-bit masks in the layout `pb u w = 23u + w`; star and touch masks are
    loops of 23 steps.
- **Consequence.** No state is replayed in the kernel. Every certificate is a list of local
  checks over static data, with a few lookups per item.
- **Data** (`Local/Data/*`, about 11 MB of source, emitted by `scripts/pr97/emit_lean.py` from
  the output of `scripts/pr97/generate.py`; `scripts/pr97/mirror.py` reruns the checks in
  Python):
  - the DAG in compile order: 64042 nodes, each with arguments, link, donors, a free use and a
    support (a leaf triple, two points with a mask of third points, or a point with a pair
    mask);
  - 5336 roots: 5313 outputs and 23 centres; 38741 links, 1162 of them with pair-graph paths.
- **Checks.** Sixteen node chunks of 4096 records and the root check, each `decide +kernel`,
  each 4–11 s and at most 2.3 GB; about 2.5 min in all.
- **Proof style.** Everything else is a general lemma; no literal word list is ever unfolded.

## 11. Stages and estimates (conservative, one agent per side)

| stage | content | estimate |
| --- | --- | --- |
| 1a | exchange-frame algebra; the exchange program (section 4) over ℚ and `ZMod (q^b)`; nested-edge cost; tensor (Kronecker) lifts and ranks | 3–5 weeks |
| 1b | generator, witness data, DAG and slot-bookkeeping kernel checks; scalar theorem of the local word and its reflection (section 6) | 6–10 weeks |
| 1c | plain frames: spans, positive definiteness on stars, pair-graph links, roots; per-wire nesting; the local cost | 4–7 weeks |
| 1d | the global node (section 7): World, stages, gauges, connectors, temporaries, correction; routed transpose; `calls = s` | 8–12 weeks |
| 1e | machine side (section 9): generic recursive machine over `BitNetwork`, temporaries, PR97 instance, `uniform_bound` at `τ₉₇` | 8–12 weeks |
| 1f | switch `Parameters.tau` and retune with T16 (through main) | 1–2 weeks |
| 2a | generic common basis (nonvanishing-polynomial lemma), exact plain-frame dimensions, whole-projector histogram and its moment | 5–8 weeks |
| 2b | opposite-bank factorization with reversal over atom rings `(ℤ/q^w)^f`, one reversed child per increment | 4–6 weeks |
| 2c | atom adapters `O(Vn)`, reversed recursive family, stopped recurrence, outer wrapper `F L F`, width selection `w = e^θ`; machine changes for variable-rank children | 10–16 weeks |
| 3 | optional: design-B frames for the extra 28% | 6–10 weeks |

**Totals.**
- Stage 1: 30–48 weeks of work. With the word side (1b–1d) and the machine side (1a, 1e) in
  parallel, 5–8 months calendar.
- Stage 2: another 19–30 weeks.
- T16 is already in the layer chain (upstream `2e11a91c`, `κ = 25222/2^46`), so the bit side
  binds.

## 12. Risks

- **Kernel throughput.** The local checks total about `2·10⁵` lookups (section 10). The
  remaining exposure is the global node (1d): its lemmas must stay general in the invocation
  index, since `W` is about `10⁸`.
- **Machine temporaries.** These are settled. The machine zero-fills and clears its temporaries
  (section 9), so PR97's 3,217,908 temporaries add only constants to the node coefficient. The
  branching ratio and the row divisor use contract roles only.
- **Stage 2.** The stopped recurrence with a linear toll and the reversed atom family are new to
  the machine; their estimates are the least certain.

## 13. Stage 2: the stopped opposite-bank supplier

The construction is icekylinx's stopped product-ring interchange (`notes/stopped-product-*.tex`
in the research tree). It was written for the retained h23 producer; stage 2 applies it to
PR97's plain-frame node (section 5).

**Atom model.**
- One invocation fixes the prime `q` and an atom width `w`.
- A field of `n` atoms is `(ℤ/q^w)^n`. `C_n` reverses the atoms and keeps their digits.
- The recursive target is the reversed interchange `F_n(H, D) = (C_n D, C_n H)` on two
  contiguous chunks with complete spectators.
- The machine's descriptor already has this shape: width `n`, digit width `w`. A node of
  `n = m f` atoms has `m` sub-fields of `f` atoms. Every rational scalar acts on each atom
  separately, so it commutes with reversal.
- Lean: a reversal of `RecursiveScalarCoordinates.Address` with its index lemma, and the
  reversed array as the counterpart of `Shared50RecursiveNodeRows.transpose`.

**Frame convention.**
- Conjugating every frame, gauge and endpoint of the node by `diag(I, C_m)` turns its partial
  swap into
  `D'_P = [[(I−P)⊗I_f, (P C_m)⊗C_f], [(C_m P)⊗C_f, C_m(I−P)C_m⊗I_f]]`.
- The common-frame identities of `FramedCircuit` are invariant under one common conjugation. So
  the word side's node theorem holds with endpoint `F_n`, through one conjugation lemma for
  framed runs.

**Generic basis** (`GenericBasis.lean`).
- `exists_generic_basis_of_idempotent`: for a finite family of idempotents `P_j`, one basis `g`
  with natural entries at most `degreeBound m (rank ∘ P)` makes every `g P_j g⁻¹` generic.
  Generic means nonzero leading principal minors of sizes `1..rank P_j`, and
  `degreeBound = m + Σ_j Σ_{i ≤ r_j} i (m + 1)`.
- Proof:
  1. Each minor of `X P adj(X)`, for the matrix of variables `X`, has total degree at most
     `i (m + 1)` (`totalDegree_minorPoly`).
  2. The minor is nonzero, because an adapted basis of range and kernel makes `P` generic
     (`exists_generic_of_idempotent`) and `g P adj(g) = det g • g P g⁻¹` (`minor_adjugate`).
  3. Mathlib's combinatorial Nullstellensatz then gives a common non-root with entries bounded by
     the total degree (`exists_generic_basis`).
- The bound is explicit because a basis from `Classical.choose` would have no height, and the
  prime must avoid every numerator and denominator. Shared50's factorizations are such
  unbounded choices, so the machine accepts Shared50's coefficients by occurrence
  (`Coordinates.CoeffSupported`).
- After elimination (`Height`, `FE N n α ≤ (16N⁵)^n (α+1)`), every coefficient stays below
  `coefficientBound`.

**K-factorization: one reversed child per projector** (`ReversedExchange.lean`,
`ReversedPivots.lean`).
- `revExchange P = transform 1 C ∘ D_P ∘ transform 1 C` is the partial swap in the frame
  `diag(1, C)`. `revPivots m r` are the pivots `(k, m-1-k)` for `k < r`.
- `revExchange_factor`: if `P C = L Π_r R` with lower-triangular invertible `L` and `R`, then
  `revExchange P = transform L R⁻¹ ∘ cross(−K) ∘ swaps(revPivots) ∘ cross K ∘ transform L⁻¹ R`,
  with `K = kMat Π_r (R C L)`. This is section 4's `exchange_factor` at `E₂ = R C`.
- `exists_rev_factor`: in a generic basis, every lower-triangular factorization of `P C`
  (`Swap.LowerTriangular.factorization`) has exactly the reversed pivots.
  - The factors keep the rank of every northeast rectangle, and that rank is the number of pivots
    inside it (`rank_mask`).
  - Genericity makes these ranks `min(i, m − j, r)` (`rank_mask_rev`).
  - The four counts around a cell count its pivots (`cell_count`), which forces the pivots
    (`pivots_forced`).
- `revExchange_generic` combines the two: a generic projector's reversed exchange has the `r`
  interchanges of one reversed child `F_r`.
- `revExchange_atoms` lifts this to `f` atoms per sub-field. The reversal of all atoms is
  `C_m ⊗ C_f`, the projector acts as `P ⊗ 1`, and the factors are `L ⊗ 1` and `R ⊗ 1`. The
  `r f` pivots `atomPivots` pair head atom `(k, x)` with tail atom `(m-1-k, f-1-x)`: one reversed
  child `F_{rf}` on the first `r f` head atoms and the last `r f` tail atoms.
- Still to do: lower-triangularity of the lifted factors in the atom order, which the streaming
  adapters need, and the machine side.

**Atom adapters.**
- Chosen design (2026-10-20): a coordinate carries its `f` atoms, with atomwise arithmetic in
  `S = (ℤ/q^w)^f`, and the atom reversal is a ring involution `σ` of `S`. The field programs and
  the control stay the network's, at `m` coordinates, for every `f`. `TwistedExchange.lean`:
  conjugating the tail by `σ` keeps fixed transformations, twists the cross shear to
  `d ← d + K σ(h)` and every interchange to `h_i ← σ(d_j)`, `d_j ← σ(h_i)`; so the reversed
  exchange over `S` is `twisted_rev_factor`. `TwistedProgram.lean`: the twisted semantics
  `twRun` of the unchanged field operations is the conjugated ordinary run (`twRun_eq`) when the
  coefficients are scalars, and `revOps_twRun` runs the reversed exchange program.
- Machine side (done 2026-10-20): an atom operation is one ordinary operation per atom level on
  `2 m f` coordinates (`AtomOps`). A padded shift with a three-field prefix
  (`Machine/FlatPaddedShift`) and the scaling stage run from runtime counters
  (`FlatPaddedShiftFromCounters`, `FlatPaddedScaleFromCounters`), so one fixed program serves every
  `f`. `LevelLoop`, `AtomShiftLoop` and `AtomScaleLoop` loop over the levels; `AtomSegment.segment`
  runs a whole nonrecursive segment at `segConst ops · f · V` (`segment_realizes`), with the
  twisted semantics (`segment_twisted`). The loop count `f - 1` is still a supplied input.
- Each lower-triangular factor expands to unit scalings and additions from earlier to later
  fields.
- A cross-bank update `D_{i,t} += k H_{j,f−1−t}` reads an earlier head atom. So the
  ordered-affine streaming primitive applies per atom: `O(V)` per pass, `O(f)` passes per fixed
  matrix, `O(V n)` per node.
- The segment compiler (`Segments`, `Coordinates`) runs on atom-indexed coordinates.
- The node toll is linear in `n`, which is the main change to the budget.

**Reversed recursive family and remainders.**
- For `n = m f + δ` with `δ < m`:
  - the first `δ` head atoms pair with the last `δ` tail atoms through `δ` ordinary width-`w`
    leaf interchanges (stage 1's supplier);
  - the two contiguous `m f`-atom intervals take the node construction;
  - for `n < m`, at most `m` leaf calls complete `F_n`.
- The machine changes:
  - variable-rank children, of width `r⌊n/m⌋` atoms;
  - a node at every `n`, so `Depth.Shape` counts atoms with no power-of-`m` condition;
  - remainder pieces;
  - the call piece becomes a block call of rank `r`.

**Stopped recurrence with linear toll.**
- With `n_r` the rank histogram on `W` contract roles, for `n ≥ m`:
  `T(n,w) ≤ Σ_r (n_r/W) T(r⌊n/m⌋, w) + C n + C w^{1−a_leaf}`. For `n < m`:
  `T(n,w) ≤ C w^{1−a_leaf}`.
- The two moment gaps `μ_1 = s/(Wm) < 1` and `μ_{τ*} = Σ_r (n_r/W)(r/m)^{τ*} < 1` give
  `T(n,w) ≤ A n + B n^{τ*} w^{1−a_leaf}` by strong induction.
- `StoppedRecurrence.stopped_closed` proves this for any node type. Children have sizes at most
  `(r/m) n`, the moments are `Σ w (r/m) ≤ q₁ < 1` and `0 ≤ Σ w (r/m)^τ ≤ q_τ < 1`, and every node
  has size at least one. The bound is `cost ≤ C/(1−q₁) n + C/(1−q_τ) n^τ L`.
- The moment certificate is rational, with exp/log enclosures as in `Global/Branching97`
  (`Stage2Moments.lean`, data `Stage2Histogram.lean` from `scripts/pr97/stage2hist.py` and
  `stage2cert.py`). The whole-projector histogram has 23 ranks over 754171495 moves and rank mass
  `s₀`; `linear_moment` gives `q₁ = 1409269/1409302` and `tau_moment` gives `q_τ = 1 − 2/10⁸` at
  `τ* = 1 − 969/10⁷`, against `a* ≈ 9.69991·10⁻⁵`. Linking the histogram to the node's moves
  remains, with the reversed family.

**`F L F` wrapper and width selection.**
- `F_n L F_n = (H+D, D)` for `L(H, D) = (H, D+H)`. So `D ← D−H; F_n; D ← D+H; F_n; D ← H−D` is
  the ordinary interchange `(H, D) ↦ (D, H)` (`ReversedExchange.flf_wrapper`, for any involution
  `C`), at `O(V n)` outside the recursion.
- For radix width `e`: `θ = 1/1000`, `w = ⌈e^θ⌉`, `n = ⌊e/w⌋`. The residual digits use the leaf
  interchange.
- Cost: `O(V[e^{1−θ} + e^{(1−θ)(1−a*)+θ(1−a_leaf)}])`, so `a_b = (1−θ)a* + θ·a_leaf`.
  Since `θ > a_b`, the adapter term is of lower order.
- For the stage-2 supplier this replaces the power-of-`m` arbitrary-width wrapper (section 9).
  The binary range padding and the `BinaryInterchangeRun` seam stay. The stage-2 switch is again
  one seam instance (`scripts/s6/apply_seam.py`).

**Numbers.** With plain frames, `a* = 9.700·10⁻⁵` (section 5) and `a_leaf = 3.734·10⁻⁶`
(stage 1). So `a_b ≈ 9.69·10⁻⁵` and `κ ≈ ε c a_b ≈ 2^-14.5` (section 1).

**What stage 1 supplies.**
- The algebra pattern of `Exchange` and `ExchangeProgram`.
- The coefficient heights of `Height` and `ExchangeBound`.
- The node of the M8 machine: split, temporaries, schedule, merge and induction. `Budget` and
  `BudgetBound` give way to the stopped recurrence.
- The supplier seam.

Estimates are in section 11 (2a 5–8, 2b 4–6, 2c 10–16 weeks).

## 14. The supplier seam and the retune

**Seam.** The cost chain uses the interchanges under Kenny's names. `scripts/s6/apply_seam.py`
makes those names a seam, and it is idempotent, so it can be rerun after an upstream merge:
- Shared50's implementations live in `Machine/Shared50BinaryRadixEqualShared`,
  `Shared50BinaryInterchangeRun` and `Shared50BinaryInterchangeBudget`.
- The Shared50 supplier modules (`scripts/s6/shared50_supplier_modules.txt`) use Shared50's own
  exponent `Shared50Parameters.tau`, and `Shared50RecursiveBudgetBound.tau_range`.
- The seam modules at the old paths (`Machine/BinaryRadixEqualShared`, `BinaryInterchangeRun`,
  `BinaryInterchangeBudget`) do three things:
  - re-export the chosen supplier (`export`, which `unfold` and `simp` see through);
  - state both uniform bounds at `Parameters.tau`, through `supplier_tau`;
  - keep `Shared50RecursiveBudgetBound.exponent_range` as the range of `Parameters.tau`.

`Parameters.tau` is now the exponent of the cost chain, and no consumer was edited. The choice of
supplier is kept in `scripts/s6/supplier.txt`:
- `m8` re-exports the M8 machine at Shared50 as a bit network (`Machine/Shared50Network`),
  under a sealed instance;
- `pr97`, the current choice, re-exports the M8 machine at the PR97 node (`Global/Instance`),
  through the sealed `Global.pr97` and its lemmas `runs_pr97` and `pr97_tau` only.

At `pr97` the default build, the `Theorem` target and the seven checks (`CompletedProofCheck`,
`CompactControlCheck`, `AxiomAudit`, `MathlibTM2Check`, `FastPathCheck`, `CRTControlCheck`,
`CRTGapCheck`) are green, with κ = 111364923/2⁴⁶. `mulInTime` and `DFT.dftInTime` use only
`propext`, `Classical.choice` and `Quot.sound`. `Host.swapMachine` and the gadget programs unfold
to M8's programs. Kenny's Shared50 tail and root, and with them the `shared50` choice, were
retired ([record](../../../docs/retired-shared50-machine.md)).

**The PR97 choice** (`apply_seam.py --supplier=pr97`, then `scripts/s6/retune.py`) sets:
- the seam instance and `supplier_tau`, from `Global/Branching97`;
- `Parameters.tau := 1 − 3734039/10¹²`;
- `CompactInterimParameters` (λ, λ', κ);
- the value of `Cost.Total.tot_kappa_eq`;
- the statement of `Theorem.lean`;
- the κ literals of `Fast/CompactFinalR`, `Fast/CompactMainDispatch`, `DFT/DFTCheck` and
  `CompletedProofCheck.lean`.

**Retune.** These numbers assume T16 as in master, `ε = 31/64`, `c = 7/8` and `δ = 1/128`.
- `τ₉₇ = 1 − 3734039/10¹²`. The exact threshold for `s/W < 529^τ` is
  `1 − τ < 3.73403992·10⁻⁶`. The certificate is `Global/Branching97.branching`: a 26-term
  exponential series for `log 529`, the cubic bound `Real.exp_bound'`, and rationals.
- `λ = 1 − 35/10⁷` and `λ' = 1 − 33/10⁷`. Then `τ < λ`, `999/1000 < λ`, `λ < λ'`, `1 − c < λ'`
  and `λ' < 1`.
- `κ₉₇ = 111364923/2⁴⁶ ≈ 1.5826·10⁻⁶ ≈ 2^-19.27`, against master's `88279/2⁴⁶ ≈ 2^-29.57`.

| margin | value | slack over κ |
| --- | --- | --- |
| layout `εc(1−τ)` (binding) | 1.582591e-6 | 6.9e-15 |
| layers `ε(1−λ')` | 1.598438e-6 | 1.6e-8 |
| CRT `(1−ε)(1−τ)` | 1.925364e-6 | 3.4e-7 |
| resampling `1/2 − δ − ε(1+2^-33)` | 7.8125e-3 | 7.8e-3 |
| direct `ε(1−c)` | 6.0547e-2 | 6.1e-2 |

The facts of the older path in the cone (`Cost/Total`) hold at `τ₉₇`. `tot_kappa_eq` becomes
`totKappa = 115755209/(10¹²·2³⁸)`.


## 15. The stage-2 switch

**Seam.** The cost chain's binary interchange (`M8/Machine/BinaryRadixEqualRun` and the wrappers
above it, up to `BinaryInterchangeRun`/`BinaryInterchangeBudget`) runs its root descriptor through
the stage-2 supplier, `Stage2Machine.Total`, in place of `ArbitraryWidthOriginalTotalRun`:
- `Total.runs` has stage 1's hypotheses. Stage 2's run time is existential per run
  (`Bound.uniform_bound`), so the paid budget `Total.cost d` is the bound
  `⌊C V max(1,e)^τ₂⌋₊` itself; `Total.uniform_bound` is immediate.
- The chain is no longer generic in the network: it runs on `supplierNet`
  (`Global/SupplierNet`), with the family's program-counter width as an instance
  (`Total.Capacity`, given at the seam as `supplierCapacity`).
- The supplier's tape and state counts are sealed (`Total.count`, `Total.states`, by
  `irreducible_def`). They are large closed numbers; with them unsealed, a consumer at the concrete
  instance that compares tape counts (`Host/ChunkSwap`) blew the elaborator and the kernel.
- The private banks are blank outside the caller (`Padded`, `Total.input_pad`), so the sparse
  header bank of `BinaryRadixEqualShared` carries over by one lemma (`Padded.headerBank_eq`).

**Retune** (`scripts/s6/retune.py`): `Parameters.tau := 1 − 96806834039/10¹⁵` (`Bound.tau₂_eq`),
`λ = 1 − 9680683/10¹¹`, `λ' = 1 − 9680682/10¹¹`, `κ = 3299646951/2⁴⁶ ≈ 2^-14.380`, and
`tot_kappa_eq : totKappa = 3001011855209/(10¹⁵·2³⁸)`.

| margin | value |
| --- | --- |
| layers `ε(1−λ')` (binding) | 4.6891e-5 |
| layout `ε(1−τ)` | 4.6891e-5 |
| CRT `(1−ε)(1−τ)` | 4.9916e-5 |
| resampling `1/2 − δ − ε(1+2^-33)` | 7.8e-3 |


## 16. Design-B frames

**Complete and selected (2026-10-22).** At selection the fixed Mathlib multiplier ran this
supplier and proved `kappa = 4222422970/2^46 ≈ 2^-14.0246`. The compiler, complete
frame traces, actual signed histogram, reversed programs, strict ranks and stopped
recurrence are connected to `Stage2Machine.Total`; the full build and all proof
and control audits pass. The milestone notes below record the implementation.

The November retune uses the same 46 histogram rows at `a = 12402/10⁸`.
The rational upper bound lies 2.43e-09 below the same `q_τ`.

**Numbers** (`scripts/pr97/stage2framebank.py` and `designbhist.py`, on the pinned upstream inputs):
- The design-B word changes no slot count and no rank mass: `R = 28866`, `W = 108516254`,
  `s = 57403754177`, so `q₁ = 1409269/1409302` is unchanged.
- The whole-projector histogram has 46 ranks, the largest `528`. Its saving is
  `a* ≈ 1.24086·10⁻⁴` (plain: `9.700·10⁻⁵`).
- The rational τ-moment certificate of `stage2cert.py` holds at `a = 1240/10⁷` below
  `q_τ = 1 − 1/10⁸`, with slack `6.208·10⁻⁹`.
- Then `1 − τ₂ = 123879734039/10¹⁵`, `λ = 1 − 12387973/10¹¹`, `λ' = 1 − 12387972/10¹¹`, and
  `κ = 4222422970/2⁴⁶ ≈ 2^-14.0246`, against `3299646951/2⁴⁶ ≈ 2^-14.380`.
- The layer margin `ε(1−λ')` still binds. `totKappa = 3840271755209/(10¹⁵·2³⁸)`.

**Where the gain is.** A side slot `u` reads its garbage out at a frame `σ_u` instead of `0`.
- Its local chain starts at `σ_u`, so the slot's local steps lose `dim σ_u` of rank.
- Its exterior grows by the same amount: `E₁ = I − (I − σ_u) ⊗ Q` (stage one) and
  `E₂ = (I−P) ⊗ I + P ⊗ σ_u` (stage two), of rank `m − h + dim σ_u`.
- The slot's total is still `m`, but rank moves from children of rank at most `22` into children
  of rank up to `528`.
- Over the 11565 deferred slots, `Σ dim σ_u = 209213`.
- The y and X chains are finer (`0`, then the deferred levels, then `t_T^⊥`; `⟨t_S⟩`, then the V
  frames, then `1`), which costs a little.

**The frames are structural.** Every design-B frame is a root complement
`W(X) = (span X)^⊥_G` of a finite set `X` of vectors, intersected only through unions of `X`.
- *Root vectors.* `G t_T` is proportional to the output covector `9 t_T − 3·1`, and
  `G w_c` to the centre covector `1 − 3 e_c`, with `w_c = 1 + 7 e_c`. So `t_T^⊥ = W{t_T}` and
  `U_c = W{w_c}`. Nesting is free: `X ⊇ Y ⇒ W(X) ≤ W(Y)`.
- *Node frames.* For a lifted addition (`j(n) > 0`, 56460 nodes, up-closed along slot
  successors), upstream's `M_n = span(n) + (U_n ∩ F_j)` equals `U_n = W(R_n)` for every node.
  Here `R_n` is the root vectors reachable along slot successors (DAG uses and links). So the flag
  `F` and the lift indices `j` are not needed, only the lift bit.
  - `span(n) ≤ U_n` holds by support inclusion: `|S ∩ T| = 1` for outputs, `c ∈ S` for centres.
  - The other 5811 additions keep `span(n)`.
  - Lifting all of them is valid (`U_n` is nondegenerate on all 5811), but it gives a smaller
    `a* = 1.2364·10⁻⁴`.
- *One centre* (45884 lifted nodes):
  - `span R_n ≤ span(star c)` (outputs) `⊕ ⟨w_c⟩` (the centre). `G` is positive definite on
    the star and `G(w_c, w_c) = −14`, so `U_n` is nondegenerate. This is a theorem, as in
    section 5.
  - `rank R_n = pairRank(E) + [c retained]`, where `E` is the pair graph of the reached output
    triples relative to `c`. This was checked on all 45884 nodes; the parity forests of
    `Frames/PairRank` and `MaskRank` apply.
- *Two centres* (10576 nodes, supports in `{c, c', ·}`): no per-centre formula holds; the
  deficit is `0..17`. These need computed ranks and Gram determinants. Nondegeneracy was checked
  on all 10576.
- *Late copies* (1396 intersections) and *V-leaf starts* (11374) are unions:
  `C_i = W(⋃_{i' ≥ i} X(ℓ_{i'}))`, and `s_i = N_i ∩ N_{i+1} ∩ ⋯`, a suffix in the `X_S` order.
  All 11374 V starts equal the suffix intersection; the `⟨t_S⟩` fallback is never taken.
- *Deferred readouts* follow a reverse recursion over the readout order:
  `σ_u = F₀(u) ∩ ⋂_{T ∈ targets(u)} t_T^⊥ ∩ ⋂_T σ_{next_T(u)}`, where `next_T(u)` is the next
  deferred slot reading `y_T`.
  - Nesting on every `y_T`, `σ_u ≤ F₀(u)` and `σ_u ≤ t_T^⊥` hold by construction.
  - The rule reproduces upstream's `σ_u` on 11541 slots.
  - The other 24 are exactly the slots where the rule's frame is `G`-degenerate. There
    upstream's basis is data: 24 integer bases with entries at most 13.
  - Falling back to frame `0` there instead gives `a* = 1.24058·10⁻⁴`.
- The maximal choice `F₀(u) ∩ ⋂ t_T^⊥` breaks nesting on 12543 of 18053 consecutive chain pairs.

So the certificate data are:
- the design-B schedule: ops with late copies and V gates, the slot holds and starts, phase 1
  and the readout order;
- one lift bit per addition;
- the 24 exception bases.
Upstream's 15 MB of bases is replaced by computed ranks.

**Kernel cost.** For the general ranks, `X` is replaced by the successors' cobases and the direct
roots, at most about 70 vectors of entries `≤ 9`. The Hadamard bound `43^23 < 2^127` makes the
rank mod `2^127 − 1` exact. Gram determinants mod a prime give nondegeneracy. With about 35000
non-structural frames (10576 two-centre nodes, 11541 deferred frames, 1396 late copies and
11374 V starts), that is roughly `10⁹` kernel bignum operations. Chunks of 256 frames per module
make about 140 modules. A complement-basis certificate trades this for data. B2 measures one
chunk before choosing.

**What changes in Lean.**
- `Local/Compile`, `Schedule`, `SlotCount`, `SlotMoments` and `Word`. These take the design-B
  word: late copies, V gates on `X_S`, and readouts after phase 1, ordered by `dim σ_u`. Only the
  topological order changes, so a generic lemma suffices: a reordering of XOR gates that keeps
  each slot's order keeps the run. `Scalar.word_run` carries over.
- `Local/Data` and `Checks`: the schedule records, the lift bit, the dims table and its checks.
- `Frames`: a new root-complement module for `W(X)`. Its contents are nesting, the one-centre
  rank and nondegeneracy, and the general rank and Gram checks. A deferred-frame module holds the
  recursion and the exceptions.
- `Global/Stage` and `StageFrames`: the first stage with deferred readouts, V gates and late
  copies; the chains along every local wire.
- `Global/Node` and `NodeFrames`: the side slots start in the gauge `σ_u ⊗ Q` and exit through
  the commuting move `D_{I−A} D_T = D_{E₁}`. The exit is a move between commuting, not nested,
  frames, with `D_A D_B = D_{A+B−2AB}` (section 4). Likewise in stage two.
- `Global/Lift`: ranks of the gauged exits.
- `LocalRanks` and `LocalSteps`: the new dims and local-step tables, from a successor of
  `stage2local.py`.
- `Stage2Link` and `Rev97Ranks`: `ranks97_lt` now follows from `σ_u ≤ t_T^⊥`, a hyperplane, so
  every exterior has rank at most `528`.
- `Stage2Histogram` and `Stage2Moments`: `a = 1240/10⁷` and `q_τ = 1 − 1/10⁸`.
- The constants `τ*` of `Rev97Ranks` and of `Stage2Machine` (`Bound.tau₂_eq`), and the retune
  (`scripts/s6/retune.py`).
- The machine side above the node (`RevMachine`, `Stage2Machine`) is generic in the histogram
  and does not change.

**Milestones** (one forked agent each):
- **B1 moments.** `stage2designb.py` emits the design-B histogram rows. `Stage2Moments` checks
  them at `a = 1240/10⁷`, `q_τ = 1 − 1/10⁸`. This step is independent of the geometry and small.
  Done: `Stage2HistogramB` (46 rows, `stage2cert.py --designb`) and `Stage2MomentsB`
  (`tau_momentB`, `linear_momentB`, `rank_massB`, `histogramB_lt`), with the certificate
  generic in the saving (`moment_le_at`). B6 makes `Stage2Moments` an instance of it.
- **B2 root-complement frames.** `W(X)`, nesting, the one-centre theorem (positive definiteness,
  the pair-graph rank) and the node frames `U_n` with the lift bit. The checks of the two-centre
  ranks, with one chunk measured first.
  Done, without the two-centre ranks: the 10576 nodes that reach two centres keep their plain
  frames. The lifted set stays up-closed (a two-centre node's predecessors reach both centres
  too), and the saving drops only to `a* = 1.23686·10⁻⁴` (σ by the rule, frame `0` at its 21
  degenerate slots), certified at `a = 1236/10⁷` with slack `6·10⁻⁹`: `κ = 4208802659/2⁴⁶ ≈
  2^-14.0292` against `2^-14.0246`. So no frame needs a computed rank or Gram determinant.
  - `Frames/LiftFrame`: `liftFrame c M r = (S or 1) − frameOf {c,u,w : M}`. With
    `w_c = 1 + 7 e_c` (`G`-orthogonal to the star, `G(w_c, w_c) = −14`) the star and the line of
    `w_c` are complementary (`starFrame_add_centreLine`). Nesting (`liftFrame_nest`), hyperplanes
    (`liftFrame_hyper`), the star (`liftFrame_star`), orthogonal supports (`frameOf_lift`),
    rank `23 − dimC c M` or `22 − dimC c M` (`liftFrame_rank`), heights `2 · 10²⁰⁰`
    (`liftFrame_bounded`, by Cramer with the integer column `w_c`).
  - `scripts/pr97/stage2lift.py`: the lift records (centre, pair mask, centre bit) of the 45884
    lifted nodes, reached along slot sources exactly as upstream's reach (checked against it),
    `Local/Data/Lift*` (4.7 MB) and the checks `Local/Checks/Lift*` (`liftOk`, `liftRootOk` in
    `Local/LiftKernel`): about 4 minutes and 1.3 GB for the heaviest chunk.
  - `Frames/DesignB`: `frameB n`, with `frameB_src` (the source of every argument),
    `frameB_out`, `frameB_centre`, `nodeFrame_le_frameB`, `frameB_rank`, `frameB_bounded`.
  - B1's rows (`a = 1240/10⁷`) are the full-lift histogram; B5's tables give the one-centre
    histogram, so B1's rows are regenerated there at `a = 1236/10⁷`.
- **B3 the design-B word.** The schedule as checked data against the DAG (late copies, V gates,
  phase 1, readout order), the reordering lemma and scalar correctness over `𝔽₂`.
  Done. The schedule is not an op list: it is the compiler's own output under three choices.
  - *Serving order* (`Dag.rank`, default `0`, so the plain `dag` is unchanged). A node's slot
    keeps the use of rank `0` (the last late user, else the first free use) and its copies follow
    by upstream's starting dimensions. With it, `Dag.compile` reproduces upstream's history on
    all 28866 slots (`designbword.py`). Late copies need no reordering: per wire a late copy sits
    where the compiler puts it, between the pivot's addition and its next gate.
  - *V leaves* (`VLeaves`): `vop` turns a leaf's copies into source gates on their own slots.
    `opsB` computes the compiled contents on clean input (`opsB_root`), and its source gates move
    to the front (`run_opsB_front`).
  - *Phases* (`Phase`): an addition of `n` is in phase one by `Φ n`, a copy by `Ψ n` (copies and
    additions differ at 2000 nodes, linked donors). Five local conditions (`PhaseHyp`), checked
    per node and per deferred use, give through a compiler invariant that the split is sorted,
    that phase two leaves the centres alone and phase one the deferred slots.
  - *The word* (`WordB`): `readout s` adds slot `s` into the targets of its `𝔽₂` garbage
    coefficients `cov s T`, defined semantically; all readouts add the pass's garbage
    (`run_readouts`). `wordB` is `RDₙ ++ Vₑ ++ OPS₁ ++ CR ++ RD_d ++ V_d ++ OPS₂ ++ OR ++ (…)⁻¹`
    for a plan `BPlan`; under the plan's four conditions it runs as the canonical
    `RD ++ OPS ++ RR ++ OPS⁻¹` (`wordB_run`, by `Commute`'s block swaps, permutations and the
    sorted split), which adds the root values.
  - *Data*: `DataB` (phase bits and serving order per node, the 11565 deferred uses in readout
    order, 6258 early and 5116 deferred V uses), checks `ChecksB` (`KernelB`), `WitnessB`
    (`dagB`, `phaseHypB`), `ScalarB` (`planB`; `wordPR97B_target`: every target gains its
    source, `wordPR97B_other`). Every module checks under 1.6 GB.
  - For B4 and B5: the readout targets of a slot are `cov`'s support, so B4 needs a computed
    sweep for them; the per-wire orders are the frame chains of section 16 (y: readouts at `0`,
    centre reads, deferred readouts in readout order, the output read).
- **B4 deferred, late and V frames.** Suffix intersections, the `σ` recursion with its 24
  exceptions, their nondegeneracy and dims, and the nested y and X chains.
  In progress. `scripts/pr97/stage2defer.py` replays the schedule with checked frames, with
  every chain nesting verified and `F₂` garbage targets:
  - one-centre unions only (all `liftFrame`): `a* = 1.0575·10⁻⁴`, `κ ≈ 2^-14.255`;
  - multi-centre unions with B2's node frames (`--multi`): `a* = 1.2178·10⁻⁴`,
    `κ = 4144106186/2⁴⁶ ≈ 2^-14.0516`;
  - with multi-centre node frames too (`--multi-nodes`): the B0 target `4222422970/2⁴⁶`.
  The σ frames at degenerate slots fall back to `0`, so no exception bases are needed.

  So most of the gain needs computed frames: about 8671 σ, 3542 V and 420 late frames.
  - `Frames/RootCheck`: the kernel check `basisOk B gens`. It runs an untrusted fraction-free
    Gauss–Jordan, then checks `Γ N = d·1` and a zero Euclidean residual for each generator.
  - `Frames/RootFrame`: its soundness, `rootFrame B = 1 − proj G [B]` with its rank, height and
    nesting, and the relations to hyperplanes, stars, `liftFrame`, plain frames and sub-masks
    (`liftFrame_eq_of_dim`).

  Kernel cost measured at about 0.2–0.4 s per frame with `r ≈ 8`. One-centre children enter
  through sub-mask bases.

  Computed-bank checkpoint: `stage2framebank.py` reconstructs the pinned schedule,
  shares equal modular spans (with every resulting span rechecked exactly), and emits 15,100
  root records and 14,121 distinct computed sections of the wire chains. `RootBankCheck`
  validates each normalized integer inverse once and the generators in batches of 16;
  `RootBank` proves idempotence, ranks, height bounds and nesting generically. The largest
  sampled frame (rank 22, 977 generators) checks in 80 seconds at 852 MiB, versus over
  6 GiB before splitting. All bank checks and all 14,121 computed-chain checks pass,
  and `Computed/Facts` links their integer rank steps to exact frame moments.
  This original checkpoint covers only the computed sections. The complete signed bank
  below now discharges the intervening plain/one-centre geometry as well.

  Mixed-chain support: `SignedCheck` describes positive spans, root complements and
  endpoints uniformly, with exact span/orthogonality checks and batch composition.
  `SignedFrames` proves their ranks and nesting; `SignedMoves.chainMoment_rankSteps`
  links every checked mixed chain to its exact projector moments, omitting equal-rank
  steps. The latter checks at 1,288 MiB peak RSS. `SelfCheck` avoids redundant residual
  checks for new bank entries whose generators are exactly their own basis.
  `SignedExtra` adds 22,077 spans to the checked prefix. `SignedFull/Facts` now certifies
  all 32,408 complete mixed chains, their nesting and their exact projector moments.
  All finite checks pass; the largest sampled check modules use 1,265 MiB (mixed chains)
  and 1,002 MiB (new inverse bank); the facts module uses 1,761 MiB. A fresh pinned
  reconstruction reproduces every generated module byte for byte.

  `designbframes.py` replays B3's compiler, maps upstream slots by their creation uses,
  and matches all 32,408 wire chains after compressing adjacent repeated frame labels.
  It found a necessary order correction: 150 fallback-zero readouts must precede the
  nonzero deferred readouts. Keeping the old order introduces backward frame moves on
  319 target wires. `ScalarB.wordWithReadoutOrder_*` proves scalar correctness for any
  readout key with the source schedule fixed, and `StageB` now accepts that key separately.
  This replay is untrusted; the corresponding Lean alignment theorem remains to be proved.

  Left for B5: prove the replayed wire-chain alignment of the concrete stages in Lean.
  `Global/StageB` now constructs the first stage from B3's actual word, with separate
  frame assignments for readouts, sources, side operations and output reads, with an
  independent readout ordering. Its
  `stage_run`, `stage_target` and `stage_other` theorems reuse `ScalarB`: scalar correctness
  is independent of the supplied frames. `Global/CentreBlocks` proves the temporary
  implementation for arbitrary centre slots, so the new slot allocation is supported.
  `StageBReverse` also proves the second stage's register semantics, using the exact XOR
  inverse of the word and a generic permutation lemma for untouched centre reads.
  `Frames/AssignmentB` gives checked signed labels in compiler numbering, generated by
  `designbframes.py --lean-root`; each lookup is valid even in padding. `Global/DesignB`
  instantiates both stages with these labels and the corrected readout order, proves
  source-to-target semantics, idempotence and height bounds for their supplied frames.
  The concrete module checks at 1,655 MiB; all 66 assignment modules reproduce byte for byte.
  `Local/Schedule.SourceFrameOrder` weakens compiler alignment to actual donor sources;
  the old raw-edge interface adapts to it. `Local/SourceNodes` extracts the checked donor
  identification without importing old node costs. `Frames/DesignBSchedule` now proves
  `frameB_compile_chain` for B2's node frames and the actual `dagB.compile`. This is a
  structural compiler theorem, not a replay certificate. It does not yet cover the
  concrete bank's varying late-copy frames; those need per-use alignment.
  The per-use invariant tracks actual donor additions, each copied slot's `startLabel`,
  and the kept slot's last actual copy frame. Leaf copies become independent V sources.
  Reuse the already checked complete-chain edges rather than adding another bank of
  geometric residual checks.
  `Local/FrameFlow` now tracks arbitrary operation labels and proves wire chains from
  operation monotonicity, allowing different copy frames within one node. `FrameFlowB`
  handles V-leaf copies as independent sources and proves `pending_birth_frame`: every
  pending use retains its frame from the prefix immediately after its actual source.
  This is a whole-prefix structural invariant, derived from the existing raw-node
  invariant and the fact that V-leaf conversion only removes slot touches. Slot assignments
  likewise remain fixed after creation, even after consumption. `Global/CopyFramesB`
  connects these traces to actual `opBlocks` and `fseq`, and identifies concrete birth
  frames for free leaf uses, internal copied/kept uses, and linked donor uses. The kept
  internal use ends at the last allocated copy's start frame, or its node frame when
  no copy was made. These three modules check at 846, 918 and 1,663 MiB respectively
  (about 1.5, 1.5 and 2.9 seconds); the guarded target build peaks at 2.2 GiB.
  `Local/WitnessOrderB` now identifies complete stored serving orders with the actual
  compiler's sorted free uses, using membership checks at each consumer and generic
  list permutation/sorting lemmas. The deterministic emitter fills default orders and
  caches the next-slot counts; local recurrence checks prove these are exactly
  `(dagB.compileTo n).next`. Each 4,096-node check is split into four independent
  1,024-node declarations. No check evaluates a compiler prefix.
  `Global/ArgumentFramesB.argument_frame` and `root_frame` instantiate the birth invariant
  with direct labels from those tables, including linked donors and kept internal uses.
  `Local/FrameCompile.compileTo_mono` proves whole-compiler monotonicity for arbitrary
  operation frames from incoming-use edges and each node's copy chain; the concrete
  `compiler_aux_chain` connects those two remaining geometric conditions to actual
  framed compiler gates. ArgumentFramesB checks at 1,662 MiB / 1.8 seconds, FrameCompile
  at 908 MiB / 1.2 seconds. All 51 emitted modules reproduce byte for byte; seven Python
  framebank tests and the guarded build including the public theorem pass.
  `Frames/ChainLookup` and `SignedFull/LookupChecks` reuse the existing signed-chain
  declarations and their geometry proofs through a balanced tree of chunk references.
  `GeometryB` checks only label equality and ordered-pair membership in those chains;
  no span inclusion, inverse or orthogonality certificate is regenerated. All 62,271
  additions and their copy paths pass. `Global/CompilerFramesB.compiler_aux_nested`
  discharges the two geometric hypotheses and proves unconditional nesting on every
  actual compiler auxiliary wire; filtering gives the actual first/rest side-block chains.
  The 16 geometry check modules use at most 3,137 MiB (394 seconds total sequential
  checking); LookupChecks uses 1,081 MiB, GeometryB/Facts 1,682 MiB, CompilerFramesB
  1,816 MiB. Each check is split into 1,024-node declarations.
  `Local/FrameBirth` structurally proves that every allocated slot first appears at its
  own start frame. `Global/CompilerBoundaryB` uses this and the explicit root-use frame
  to bound all compiler frames from below by the start and above by each final root frame.
  `GeometryB/SlotFacts` also checks the readout-to-start edge for all 28,866 slots;
  `compiler_readout_bound` connects these edges to all actual compiler frames. The cached
  final allocation count proves the same slot count as the existing supplier.
  All 52 new emitted geometry/lookup modules reproduce byte for byte, including a fresh
  reconstruction through the pinned upstream compiler; seven Python framebank tests
  and a guarded build including the public theorem pass. κ remains unchanged.
  `Frames/GeometryB/RootKernel.rootOk` now defines the remaining root endpoint check:
  a path from the explicit root-use label into a known root complement, together with
  membership of the output triple or centre code in that complement's basis.
  `RootEndpointFacts` proves the code/vector identities and projector bounds directly
  from the already certified Gram unit. `GeometryB/RootFacts` proves checker soundness;
  `Global/RootBoundaryB` connects a passed check to all actual compiler frames on the
  corresponding output or centre slot. The concrete `RootChecked.rootOk_at` theorem now
  discharges both endpoint hypotheses, so the compiler boundary theorems are unconditional.
  The four endpoint modules check at 1,168, 1,448, 1,662 and 2,614 MiB respectively;
  the guarded integration build including the public theorem passes.
  `designbgeometry.py` now emits all 5,336 endpoint witnesses from the compiler's
  `rootSlots` and full-chain endpoints. Each names an existing signed chain and a negative
  bank label whose basis contains the endpoint code. Eight small check modules, split
  into 256-root declarations, prove the concrete `rootOk` checks; `RootChecked.rootOk_at`
  aggregates them. The checks peak at 1,576 MiB (22 seconds total sequential checking),
  and the aggregator at 1,485 MiB. All 69 emitted geometry modules reproduce byte for byte
  from fresh downloads at the pinned upstream revision; the seven Python framebank tests pass.
  Reconstruct with `generate.py SOURCE DAG.json`, then
  `stage2framebank.py SOURCE BANK.json --multi-nodes --signed-output SIGNED.json`, then
  `designbgeometry.py SIGNED.json --lean-root . --dag-json DAG.json --pr97-dir SOURCE`.
  `Global/PhaseFramesB.side_phases_trace` proves that splitting the side compiler into
  its two phases preserves the exact auxiliary trace. Source gates on an auxiliary slot
  all use its start frame; the first phase avoids deferred slots. Together these prove
  `forward_aux_chain` across both source phases and both side phases, unconditionally.
  `Global/DataTraceB.stage_source_trace` identifies the source-wire trace of the actual
  stage for arbitrary frame assignments: the ordered early sources, late sources and
  uncompute. Readouts, side operations and centre blocks contribute no source frames.
  RootBoundaryB, PhaseFramesB and DataTraceB check at 3,014, 2,244 and 2,338 MiB;
  the guarded integration build including the public theorem passes. The new-module and
  completed-proof axiom audits pass using only the standard axioms. κ remains unchanged.
  `Global/BlockTraceB` identifies auxiliary frames in readout, output, centre and
  uncompute blocks. `AuxBoundaryB` transfers every reordered phase frame back into the
  compiler trace and proves the phase exclusions at deferred and centre slots.
  `AuxStageFramesB.firstStage_aux_chain` now proves the complete auxiliary chain from
  `sigma` through both phases, readouts, centre/output boundaries and frame-one uncompute.
  `finalStage_aux_trace` identifies its reversed complemented trace, and
  `finalStage_aux_chain` proves the complete second-stage chain ending at `1 - sigma`.
  These are structural list proofs; no compiler prefix or new certificate is evaluated.
  The three modules check at 1,568, 3,022 and 3,030 MiB. The guarded build including the
  public theorem and the new-module standard-axiom audit pass. κ remains unchanged.
  `Global/TargetTraceB.stage_target_trace` gives the exact target-wire trace: early
  readouts, centre scatters, deferred readouts and final root reads. All repeated frames
  are retained. `TemporaryTraceB` proves the complete temporary traces of both stages:
  star then zero, and complemented star then one. `StageReflectionB` proves reversed
  complemented traces for every register, and now supplies the auxiliary reflection proof.
  These three modules check at 1,600, 1,568 and 1,566 MiB.
  `Local/UseSlotsB.useSlotB` computes slots from the checked allocation count and serving
  index. `Global/UseSlotsB` proves agreement with actual compiler assignments for leaf
  uses and non-kept internal uses, including consumed uses. The existing deferred-use
  checks exclude kept internal uses. Twelve generated source-check modules certify all
  11,374 source-key uses in 128-use declarations, peaking at 1,142 MiB.
  `Global/SourceKeysB` replaces the actual early/late source keys and deferred-readout
  keys and membership predicate by these computable slots, without evaluating any
  compiler prefix. UseSlotsB and SourceKeysB check at 1,999 and 1,988 MiB.
  All 82 emitted geometry/source modules reproduce byte for byte; seven Python tests,
  the guarded build including the public theorem, and standard-axiom audits pass.
  κ remains unchanged.
  Next: connect the data-wire source/readout traces to the signed chains, allowing
  repeated equal frames. For target T, the backward recurrence over uses is
  c(root j) = [T ∈ targets j], b(n) = Σ_{u ∈ freeUses n} c(u), and
  c(gate n pos) = b(n) + [pos is the linked operand] c(linkUse n), over F₂.
  An untrusted Python replay agrees with all 28,866 actual slot covectors. The generic
  compiler recurrence soundness theorem and the concrete coefficient certificates
  satisfying its local hypotheses are now proved and kernel-checked.
  `Local/AdjointB` now proves generic backward observation weights for arbitrary operation
  lists. Its `cov_eq_pullOps` identifies the actual `Dag.cov` with the initial auxiliary
  slot coefficient obtained by pulling back the root weights through `sideB`. This
  structural theorem needs no register-state support assumption or concrete evaluation;
  it checks at 1,097 MiB. `Local/CompilerAdjointB` proves that source erasure
  preserves auxiliary weights and gives exact backward identities for fresh-copy
  serving blocks and both linked and unlinked addition steps. Leaf steps preserve
  auxiliary weights, including through the earlier compiler prefix. This module checks
  at 1,093 MiB. The block identities and pending-use allocation invariant feed the
  full recurrence theorem below.
  `Local/PendingWeightsB` now constructs the finite pending-use frontier, proves its
  exact disjoint transition into survivors, free uses and the linked use, and identifies
  its terminal observation with `rootWeights`. The compiler invariant supplies exact
  coefficients at live slots and zero contribution at unallocated slots.
  `Local/ServingWeightsB` identifies the actual serving-slot observation list with the
  kept pivot followed by consecutive fresh slots, and proves that pulling back internal
  copies gives the pivot exactly the sum of free-use weights. These modules check at
  1,105 and 1,087 MiB. The composition tracks the frontier
  observation plus the proposed garbage weights restricted to slots not yet allocated:
  each reverse step preserves this combined boundary, the terminal boundary is the
  root observation and the initial boundary is the proposed garbage coefficient vector.
  `Local/BoundaryWeightsB` defines this combined boundary and proves its initial and
  terminal equations and the exact splitting of future garbage weights at allocation.
  `Local/LeafBoundaryWeightsB` now proves its preservation through every leaf step,
  including backward propagation through the already compiled prefix, when each
  newly allocated slot has its named use coefficient. It checks at 1,090 MiB.
  `Local/InternalBoundaryWeightsB` proves both linked and unlinked addition cases:
  fresh-copy pullback gives the pivot b(n), addition sends b(n) to both arguments,
  and the linked-use contribution remains on its operand. It checks at 1,110 MiB.
  `Local/CovarianceRecurrenceB.UseRecurrence.cov_eq` now composes all node cases
  and identifies the actual `Dag.cov` with the proposed initial garbage vector, from
  local use/allocation equations, root weights and the final allocation bound. It checks
  at 1,095 MiB. No concrete compiler prefix is reduced.
  `scripts/pr97/designbcovariance.py`, invoked by `designbgeometry.py`, now emits 39,014
  shared bit masks, 64,042 argument-mask pairs and all 28,866 slot masks from the
  pinned reconstruction. An independent reverse replay agrees with every slot mask.
  `CovarianceKernelB` checks consecutive fresh allocations and argument XOR equations
  in 128-node declarations; `CovarianceChecksB` proves them for all 64,042 nodes.
  `CovarianceRootChecksB` checks all 23 centre masks against the checked leaf records;
  output-root masks are single target bits. `CovarianceFactsB` proves scalar soundness
  simultaneously for all target bits. `Global/CovarianceDataB` proves agreement with
  the actual root target lists. `Global/CovarianceB.covariance_eq_slotMask` now
  identifies every actual `dagB.cov` coefficient with its slot-mask bit, by instantiating
  the full use recurrence and the structural allocation correspondence. This integration
  checks at 2,048 MiB. All 141 emitted modules reproduce byte for byte; the three
  covariance generator tests pass. Next: use these coefficients to connect the exact
  data-wire traces to their signed frame chains, including repeated equal frames.
  `Local/KeyedOrderB` proves that sorting a permutation of a duplicate-free key
  recovers its order, and that filtering commutes with this recovery.
  `scripts/pr97/designbkeyorder.py` emits inverse-position certificates reusing the
  existing key chunks. `Local/KeyOrderChecksB` checks 34,504 entries: the 11,565
  framed readouts, 11,565 deferred slots, 6,258 early sources and 5,116 late sources.
  `Global/KeyOrderB` proves uniqueness for the actual stage readout order and all
  three plan keys. `Local/SequenceCheckB` compares lists structurally through an
  independently indexed sequence. `ReadoutOrderChecksB` now proves that the concrete
  readout key is exactly the stable partition of the deferred-use slots: 150 zero
  frames followed by 11,415 nonzero frames. Its checks reference the existing key
  chunks and prove the allocated-slot bounds; no large list equality is kernel-reduced.
  `Global/ReadoutOrderB` proves the actual deferred-range permutation and identifies
  `lateSlots assignment.readoutOrder` with the concrete key itself. It checks at
  2,246 MiB. `Global/TargetMaskTraceB` rewrites the full target trace using checked
  mask bits and the zero/nonzero readout partition, retaining repeated frames, and
  proves the zero-readout segment has only zero frames. It checks at 2,299 MiB.
  All 72 ordering certificate modules reproduce byte for byte. Remaining: source-key
  coverage/order and alignment of the exact traces with their signed frame chains.
  `Local/ReadoutCoverageChecksB` now certifies that every nonzero allocated readout
  frame occurs in the concrete key. `Global/ReadoutZeroB` uses it to prove that every
  immediate target readout has frame zero. `TargetGeometryB` checks the target labels
  against the existing full signed chains, with the negative endpoint containing the
  output triple code. Checked masks on 32-slot blocks accelerate filtering; the generic
  `fastLabels_eq` theorem proves that skipping a block preserves the exact trace.
  The first target check uses 1,685 MiB rather than over 7 GiB for a direct scan.
  `Global/TargetLabelTraceB` identifies these labels with the actual late readout trace,
  retaining zero frames and repeated frames. The target and ordering emitters reproduce
  250 and 81 modules byte for byte from the pinned reconstruction.
  All 1,771 target endpoint checks pass. `TargetGeometryB/Facts` proves their
  chain and hyperplane bounds. `Global/TargetStageFramesB.firstStage_target_chain`
  connects them to every actual target wire, including the zero prefix and repeated
  output reads; `finalStage_target_chain` gives the reversed complemented chain.
  The stage module checks at 3,096 MiB. The sampled target modules, including the one
  with the most slot lookups, use at most 1,761 MiB. Source coverage/order and source
  chain alignment remain before the compiler/frame checkpoint is complete.
  `Local/SourceListB.srcB_eq_sourceBlocks` now extracts the exact source list from
  arbitrary valid compilers: consecutive fresh slots for each leaf, with distinct
  source targets. `SourceOrderB` recovers sorted operation lists from their complete
  target keys. `KeyMembershipB` proves both membership and nonmembership from checked
  inverse positions and indexed sequences. The key emitter reuses the existing chunks
  for early/late/deferred lookups and certifies every allocated leaf source slot and
  all 11,374 source entries' phases. `Global/SourceOrderingB` proves that the actual
  early and late compiler lists are exactly `earlyV.map sourceOpB` and
  `lateV.map sourceOpB`. `Global/SourceTraceB` rewrites the actual first-stage source
  trace into those exact ordered labels and the frame-one uncompute, retaining repeats.
  SourceListB checks at 1,088 MiB; SourceMembershipB, SourceOrderingB and SourceTraceB
  at 2,001, 2,007 and 2,007 MiB. All 134 key modules reproduce byte for byte, and the
  Python tests pass. Remaining for the compiler/frame checkpoint: connect these source
  labels to the signed chains and prove complete source nesting in both stages.
  `Local/SourceListB.srcB_leaf_targets` now extracts each leaf's exact allocation
  interval. `SourceOrderB.sort_index_eq` recovers key-sublist order from checked inverse
  indices; a structural insertion sort keeps the short checks reducible by the kernel.
  `Global/SourceSlotTraceB` identifies these sorted intervals with the actual filtered
  early and late source keys. `SourceGeometryB` checks all 1,771 source paths using only
  the existing signed chains and positive bank entries containing the input triple.
  Every selected entrance also has checked rank one. The generic soundness theorem
  bounds every source path from the input line to one, and records that the entrance
  has the same rank as the input line for subsequent cost linkage.
  `Global/SourceStageFramesB.firstStage_source_chain` and `finalStage_source_chain`
  prove complete nesting in both actual stages, including frame-one uncompute and
  repeated frames. SourceSlotTraceB checks at 2,128 MiB and the stage module at
  2,329 MiB. All 58 emitted source-geometry modules reproduce byte for byte; the
  guarded build including the public theorem and the Python tests pass.

  The compiler/frame checkpoint is complete: auxiliary, target and source chains,
  plus both stages' temporary traces, are proved for the actual compiler word.
  Integration assessment: the existing `Lift`, placement/reflection and recursive
  supplier interfaces remain applicable. The next work is the gauged design-B node:
  side-role entrance/exit projectors, semantic boundary cancellation, and an upper bound
  on its actual move moments by the checked signed-chain histogram. The current local
  checks allow equal frames and skipped chain entries, so cost linkage must explicitly
  handle stuttering/refinement rather than assume literal chain-list equality.
  `Global/Node`, `NodeFrames`, `FrameMoments` and `Stage2Link` provide the existing
  plain-frame pattern; `Stage2MomentsB` supplies the checked numerical target.
  No new recursive-machine construction or further design-B optimization is indicated
  by these interfaces. Boundary/cost proofs, supplier replacement and retuning remain;
  the public κ is unchanged.
  The boundary primitives are now implemented. `Global/FrameMachine.FStep.exit`
  moves from `A` to `1 - C` in one exchange of `1 - (A - C)`, for nested `C ≤ A`.
  Its validity checks retain the existing frame/coefficient limits. Ordinary modular
  execution, arbitrary-ring interpretation, reversed execution, rank counts and move
  moments all cover this case. This keeps the commuting exit as one whole projector.
  `Global/GaugedExitB` proves the two lifted exits are valid and have rank
  `506 + rank σ`; `Global/SideExitB` instantiates them with the actual checked σ frames,
  including their complements and one-term moment contributions.
  `AssignmentB/RankFacts` now checks all 28,866 allocated σ ranks are at most 22, so
  each exterior child has rank at most 528. The nine generated rank-check modules
  reproduce byte for byte. `Local/WordOrderB`'s operation permutation and `Global/AuxEndpointB` prove that every allocated first-stage
  side wire actually reaches frame one in uncompute. Generic complementary-gauge
  cancellation is proved for modular addresses (`swapAt_complement`) and interpreted
  coordinate rings (`Rev/GaugedBoundary`).
  The complete public theorem rebuild passes after extending the framed-step language:
  11,108 modules, 36.8 GiB total peak under the guard. Sampled new/changed modules use
  at most 2,242 MiB; coefficient bounds and proof limits are unchanged.
  `Global/StageGateB` proves that every gate of the actual first-stage word is
  an XOR on distinct, in-range wires, for any frame assignment. The compiler-role
  count bridge reuses the existing global world's side roles; the generic
  `Local/SourceListB.srcB_node_lt` supplies source bounds without evaluating the
  concrete compiler. The stage check uses 3,033 MiB under the default proof limits.
  These concrete stages and exits are not yet the public supplier. The node integration
  below closes boundary semantics; the histogram bound, supplier replacement and
  B6 retune remain. Public κ remains unchanged.
  The executable gauged node is now assembled in `Global/NodeB`, using the existing
  roles, placements and correction. `StageValidityB` proves gate legality and frame
  validity in both orientations. `NodeScalar` proves the global swap for arbitrary
  local shear programs; `NodeScalarB` instantiates it with the actual design-B word.
  `NodeTraceB` gives exact placed traces, and `NodeFramesB.chainOk_node` joins the
  complete local chains through the two lifted stages and the correction.
  `GaugedSinks` explicitly aligns each side role to its terminal endpoint before
  the whole-projector exit. This matters for reflected chains that can stop below
  their padded endpoint. `NodeRunB.valid_node` proves every implemented step valid;
  `NodeRunB.node_run` proves the routed transpose on arbitrary stored streams and
  zero temporaries. Every side stream closes through complementary entrance/exit
  gauges, rather than assuming its entrance is zero.
  `GaugedMoments` prices both terminal alignment and the single exterior projector;
  `NodeMomentsB.edgeMoment_node` expresses the exact executed moment as a wire sum.
  Each side path includes its terminal endpoint and one exterior of rank
  `506 + rank sigma`. The next obligation is to bound these actual paths, including
  repeated frames and skipped chain entries, by the checked signed-chain histogram.
  Node semantics alone does not improve the public kappa; histogram linkage,
  recursive supplier replacement and the B6 retune remain.
  All ten new modules pass the single-file guard, with peak RSS at most 3,111 MiB.
  The guarded build including the public root passes (14,295 jobs, 30.9 GiB combined
  peak). The completed-proof check and standard-axiom audits pass. Default proof
  limits and coefficient bounds are unchanged.
  Cost linkage now handles repeated and skipped frames structurally.
  `Global/ChainRefinement.chainMoment_le_of_subset` removes repetitions and bounds
  a covered nested path by its reference chain, for nonnegative subadditive costs.
  `Frames/ChainLookupMoments.pathCheck_moment_le` applies this to existing path
  checks, including the constant-path case. No matrix certificate is regenerated.
  `SourceMomentsB` proves that checked rank-one source entrances are exactly the
  input lines and bounds all actual source paths by their full signed chains.
  `designbtargetranks.py` checks the lengths of all 1,771 existing endpoint bases,
  in 128-target declarations across four check modules. It introduces no new bank
  records or endpoint data and needs no temporary reconstructed inputs. All six
  emitted modules reproduce byte for byte; the main geometry emitter invokes it.
  `TargetMomentsB` identifies these complements with the actual output hyperplanes
  and bounds every actual target path by its full signed chain, including zero
  prefixes, repeated readouts and repeated output reads.
  `LocalMomentsB` proves that either side orientation pays exactly the full local
  path from sigma to one, plus one exterior of rank `506 + rank sigma`.
  `DataMomentsB` joins the two local data paths through the rank-484 connector.
  `NodeBoundB.node_moment_le_data_chains` combines these costs with all owned
  centre/correction temporaries. Its remaining side terms are the actual local
  auxiliary moments. Next: cover those paths by the canonical slot chains, sum
  the resulting signed rank steps against the histogram, replace the supplier
  and retune. Public kappa is unchanged.
  All thirteen new modules pass the single-file guard, with peak RSS at most
  3,436 MiB, and the guarded build including the public root passes. The new cost
  closure passes the standard-axiom audit; all ten Python tests pass. The checked
  endpoint-rank modules reproduce byte for byte without temporary input files.
- **Checked compiler slots for auxiliary cost coverage.** `Local/SlotAssignment` proves
  structurally that local free-allocation and donor-link equations determine every
  pending slot. `Local/CompilerCoverage` propagates per-operation membership through
  arbitrary compiler prefixes and their frame traces. `designbslots.py` reconstructs
  64,042 argument-slot pairs and 5,336 root slots from the pinned inputs; the 36
  generated modules reproduce byte for byte. The local equations pass kernel checks,
  and `Global/SlotAssignmentB` identifies every actual argument and root slot without
  evaluating concrete compiler prefixes. All 41 new modules pass the single-file
  memory guard, at most 1,954 MiB peak RSS. These indices feed the cost linkage below.
- **Canonical auxiliary costs.** `designbauxcoverage.py` reuses the existing
  slot-chain map, argument table and root endpoint data: all 64,042 node cases,
  28,866 slot cases and 5,336 roots pass membership checks. Endpoints are checked
  to have codimension one on the same chain as the actual root slot.
  `AuxTraceCoverageB` propagates an arbitrary property from compiler frames and
  boundary frames through the whole reordered first stage. `AuxMomentsB` identifies
  the root endpoints with output hyperplanes and centre stars, proves membership
  of every actual side frame in its canonical chain, and applies chain refinement.
  `SignedNodeBoundB.node_moment_le_signed_chains` bounds the complete executed node
  by canonical auxiliary/source/target chains, with exteriors, connectors and all
  owned temporaries still charged. Its closure passes the standard-axiom audit
  (251,801 declarations); the 33 emitted check/aggregation modules reproduce exactly.
  All 39 affected modules pass the single-file guard, at most 3,148 MiB peak RSS.
  Fresh reconstruction of the complete signed snapshot matches the recorded digest
  `606486ea…b4909b`. Its slightly different histogram replaces the preliminary
  schedule-dimension certificate in the next step.
- **Actual histogram and stopped moments.** `designbhist.py` counts auxiliary
  chain steps directly over the physical compiler slot map, so no unproved
  permutation of chain indices is used. Separate checks count source/target chains
  and the actual readout-frame ranks. `Global/SignedHistogram` proves structural
  histogram concatenation and evaluation for arbitrary checked chains and trees;
  the concrete chunks are joined without checking their frames twice.
  `Global/HistogramB` identifies the four histogram evaluations with the actual
  canonical-chain and exterior sums. `Stage2HistogramB` is regenerated from this
  full signed geometry, replacing the preliminary schedule-dimension counts.
  Its linear rank mass remains `57403754177`; the rational tau moment is at most
  about `0.999999983792195`. `Stage2LinkB.edgeMomentB_le_histogram` now bounds the
  actual executed node by this histogram, and `linear_premiseB` / `tau_premiseB`
  prove both stopped-recurrence premises at `savingB = 1240/10^7`, with
  `qτB = 1 - 10^-8`. The closure passes the standard-axiom audit (254,416 declarations).
  All 25 affected modules pass the single-file guard (at most 2,427 MiB peak RSS),
  all 20 generated modules reproduce byte for byte, and all ten Python tests pass.
  These moment premises are used by the selected reversed supplier below.
- **Reversed execution bridge.** `Rev/FramedRingB` proves the actual gauged node's
  routed interchange for arbitrary stored streams and any permitted common frame
  interpretation over a commutative coordinate ring. It reuses the generic framed
  execution proof, the actual design-B logical run and the complementary side exit.
  `Rev/NodeB.rev_node_runB` then runs its existing conjugated reversed edge programs
  under the same basis/prime and involutive atom-map hypotheses as the plain node.
  Both modules pass the single-file guard (at most 2,443 MiB); the joint closure
  with `Stage2LinkB` passes the standard-axiom audit (264,701 declarations).
  The selected recursive supplier now uses this bridge; its rank and parameter
  connections are recorded below.
- **Strict ranks and the unchanged basis budget.** `Global/RankMoments` proves
  linear telescoping and natural-to-real moment identities structurally.
  `Global/NodeRanksB.rank_lt` proves every actual node exchange has rank below 529:
  source and target local paths telescope to 22 each, a data wire pays at most 528,
  local side moves have rank at most 23, and the exterior rank is at most
  `506 + rank sigma ≤ 528`. Owned temporaries are included. Its `calls_node_le`
  bounds the actual total rank by `57403754177`, so the existing generic-basis
  degree and machine-prime estimates can be reused. The closure passes the
  standard-axiom audit (264,712 declarations). All three affected modules
  pass the single-file guard (at most 3,276 MiB peak RSS). These are the rank
  bounds used in the completed supplier selection and retune below.
- **B5 supplier integration complete.** `RevNetwork` / `Rev97Machine` select the
  actual gauged node and its reversed execution. `Rev97Ranks` uses its strict
  ranks, `savingB` and `qτB`; the existing recursive family and F L F wrapper build
  unchanged in architecture. The obsolete plain-node top-rank argument is removed
  (restore from `bd16f751`).
- **B6 retune complete.** `Bound.tau₂_eq` and `Stage2Machine.Total.tau` are
  `1 - 123879734039/10^15`. `scripts/s6/retune.py` sets the matching outer parameters
  and `kappa = 4222422970/2^46`. `MathlibTM2.mulInTime`, the unconditional statement
  and DFT corollary compile at that value. `CompletedProofCheck`, `AxiomAudit`
  (340,777 declarations) and `CompactControlCheck` (521 contracts) pass with only
  the standard allowed axioms. All 687 geometry-generator outputs reproduce exactly
  from the freshly reconstructed pinned inputs.
  The guarded public build completes 14,447 jobs at 46.4 GiB combined peak RSS.
  All 21 changed library modules pass individual guarded checks, at most 3,384 MiB.

The original risks—deferred covariance, ordering, data paths and commuting exits—are
resolved for the actual executed node. No new recursive machine was needed. This
completes the design-B improvement of about 0.356 bits; future bound work follows
M9–M11 in the root `PLAN.md`, with long-term target `kappa = 0.0023`.
