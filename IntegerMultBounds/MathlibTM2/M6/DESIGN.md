# M6: the selected suppliers in the running machine

M6 replaces both finite suppliers of the running multiplier with the selected ones: T16 on the
complex side and PR589 on the bit side, each with variable-rank children. This file maps what
remains, what is in progress upstream, how the machine consumes a supplier today, and where
parallel work has the lowest collision risk.

## 1. Why both suppliers are needed

Write `a_c = 1-σ` (complex saving) and `a_b = 1-τ` (bit saving). The compact route needs
`τ < λ`, `σ < λ`, `internal = τ + (1-β) max(σ-τ, 0) < λ` and `λ < λ'`, and its binding stage
margins are the layer margin `ε(1-λ')` and the layout margin `ε c (1-τ)`, with `ε < 1/2`
(resampling margin `1/2 - δ - ε`).

| suppliers | `a_c` | `a_b` | cap on `1-λ'` | cap on `κ` (`ε = 31/64`) |
| --- | --- | --- | --- | --- |
| mixer + current bit (today) | `2.5·10^-9` | `2.96·10^-9` | `2.5·10^-9` | `2^-29.62` |
| T16 + current bit | `1.6755·10^-3` | `2.96·10^-9` | `2.96·10^-9` (τ binds) | `2^-29.38` |
| mixer + PR589 | `2.5·10^-9` | `1.7334·10^-3` | `2.5·10^-9` (σ binds) | `2^-29.62` |
| T16 + PR589 | `1.6755·10^-3` | `1.7334·10^-3` | `1.6756·10^-3` | layer `2^-10.27`; layout at `c = 7/8`: `2^-10.41` |

Either supplier alone leaves the cap near `2^-29.4`. The leap needs both.

## 2. What remains, per supplier

Sources: PLAN.md (M6 row), plan/D-sharper-bound.md (M6a, M6b, "T16 semantic progress",
"Selected PR589 frame-state bridge", "Concrete PR589 rational frame operators", "Complete
selected PR589 label dimensions"), and the certificate trees.

### T16 (complex, parent width `m = 73`, live stock `W = 14336`, ranks ≤ 48)

Checked: the canonical complex word of every native frame (`PauliCanonical`, `PauliSchur`,
`PauliCorrection`, `BinaryElimination`, `PauliLowering`); `edge_lowering` (every transition is a
monomial, `S C_r S` and a monomial, up to a Pauli and a scalar); the action of both native local
words on dirty inputs (`Trace/Framed`, `Trace/Action`); the eight-stream composition for all 16
replicas and 112 ports (`Streams/*`); the charge profile, owner rows, label traces, finite
geometry and tableau ranks; the occurrence list `t16Ranks` with `Realizes t16Ranks
complexHistogram` (`Layer/SelectedMoments`); and the closed variable-rank recurrence
`t16_variable_closed` (`Layer/VariableRecurrence`).

Remaining, in Kenny's own words:
1. **Node-level bridge:** chart and route lifts, adapters and wrappers as exact operators through
   `edge_lowering`, per-wire event alignment over cover classes, the `X_δ(g)` correction.
2. **Machine:** monomial instructions from slot XORs and linear phases, an address-translation
   pass, and retargeting the node from `m = 25³` to `m = 73`.

### PR589 (bit, parent width `m = 64`, live stock `W = 28416`, ranks ≤ 42)

Checked: the 5583-instruction scalar word on 661 registers with its dirty endpoint and
restoration (`DirtyEndpoint`, `FiniteWord`); frame-ID replay through D, A, the scatter boundary,
B, C and final alignment (`Frames/*`, 29250 phase incidences, 527 scatter incidences); the
rational E8 frame interpretation (`Geometry/Model`); the nine COPY ranks, all 7
(`Geometry/CopyRanks`); all 636 label dimensions (`Geometry/Dimensions`); the nesting-to-rank
bridge (`Geometry/Moves/Model`: `CheckedPair`, `rank`, `profile`); and the bill
`bit_bill_le` at `a = 10/5769` (`Layer/SelectedMoments`).

Remaining:
1. **Local MOVE profile.** The ranks of all 29250 phase incidences and 661 final-alignment
   incidences. Kenny lists this as open ("concrete nesting/rank certificates").
2. **Occurrence link** `Realizes L bitHistogram` for the nine-stage hosted occurrence list `L`.
   `bit_occurrence_moment_le` takes it as a hypothesis.
3. **Framed execution:** distinct-frame COPY execution and compatibility of the rational frames
   with binary scalar data.
4. **Variable-rank bit recursion** at the cost level, and the **bit interchange machine** that
   executes it (section 3).

## 3. How the machine consumes a supplier today

**Complex side.** `Layer/Node.lean` fixes `m = 25³` and wire roles `NWire =
ComplexFramedExecution.Wire`. `program ds = lowerSkel skeleton ds` interleaves scalar gates with
rank-one factors `Instr.factor w (q, v)`, `v : BinaryWalsh.Address m`. Each factor is one child
call of size `e/m`. `Cost/Branching.lean` proves `factorCount (program brDirs) = rankSum` and
`F/NW < m^σ`. `Layer/Recurrence.recurrence_closed` turns that uniform branching into the layer
bound. `Cost/BranchingMoment.lean` restates the hypothesis as a uniform occurrence moment.

A variable-rank child changes three things:
- the instruction carries a rank-`r` operator (T16's `C_r` between monomials), implemented by one
  child call of size `r e/m` on an `r`-row sub-array;
- the cost chain uses the occurrence moment `Σ_i w_i (r_i/m)^λ` in place of `F/NW`, closed by
  `VariableRecurrence.variable_closed`;
- `m`, the wire roles, the array layout and the address arithmetic change from `25³` to `73`.

All three are the T16 "machine" item that Kenny lists next.

**Bit side.** `Host/ChunkSwap.lean` and `Host/PlacedSwap.lean` run the vendored binary
rectangular interchange machine `Machine/BinaryInterchangeRun.program`. Its cost is
`C · V · max(h, d)^τ` (`Machine/BinaryInterchangeBudget.uniform_bound`). The exponent comes from
the Shared50 recursion: `Shared50RecursiveBudget.budget (depth+1) V = node·V +
s·budget depth (V/roleCount)`, with uniform branching `s/roleCount`
(`Shared50RecursiveBudgetBound`). That native recursion is about 23k lines (`Machine/Shared50*`,
`Machine/Recursive*`, `BinaryAdjacent*`, `BinaryRadix*`, `DigitInterchange*`).

A variable-rank bit child replaces the uniform budget with children of volume `(r_i/64)·V` and
weights from the hosted occurrence list. That needs a PR589 interchange recursion in place of the
Shared50 one. The cost-level step is an instance of `VariableRecurrence.variable_closed`, which is
generic in the node type.

## 4. What Kenny is doing (from `git log`, 10-17)

Every commit after 13:00 is T16: Clifford words, tableaus, Pauli correction, `C^r` child
lowering, framed event traces, local-word actions, the eight-stream composition, kernel products,
orthogonal charts, nine-bit chart lifts to 73-bit arrays, and the parent node at the level of
unit operations. The cost-level `Variable-rank closed layer recurrence with the T16 instance` is
from 13:02. PR589 was last changed on 10-15 (15:21), apart from an import shake on 10-17 02:44.

| remaining piece | collision risk |
| --- | --- |
| T16 node-level bridge | very high (in progress) |
| T16 machine: monomial instructions, address translation, node retarget to `m = 73` | high (his stated next step) |
| wiring occurrence moments into the main layer cost chain | high (part of the retarget) |
| PR589 local MOVE profile | low |
| PR589 nine-stage occurrence link `Realizes L bitHistogram` | low |
| PR589 framed execution (COPY lifecycles, frame/scalar compatibility) | low |
| PR589 variable-rank bit recursion and interchange machine | low now, large |

## 5. Recommendation: the PR589 side

The bit side is the largest piece with low collision risk, and the leap needs it whatever
happens on T16.

| stage | content | estimate |
| --- | --- | --- |
| S1 | Local MOVE profile: every phase and final-alignment incidence is a `CheckedPair`, its `moveRank` is the certified `value`, and the positive ranks plus the nine COPY ranks have upstream's `local_histogram` `{1:1323, 2:1342, 3:79, 4:44, 5:102, 6:11, 7:19}` | 1–2 days |
| S2 | Nine-stage occurrence list from S1 and the frozen hosting selections (`selection9-p111.json`, `hosting11-p111.json`, PR #510 chain with 32 replicas): `Realizes L bitHistogram` | 1–2 weeks |
| S3 | Framed execution: the nine COPY/ERASE lifecycles and the frame-zero ADDs as exact operators on rational frames, compatible with the binary scalar endpoint | 2–3 weeks |
| S4 | Variable-rank interchange budget: an instance of `variable_closed` for the bit recursion with exponent `τ = 1 - 10/5769` | 1 week |
| S5 | PR589 interchange machine replacing the Shared50 recursion behind `BinaryInterchangeRun` | 2–4 months |
| S6 | Retune of `Parameters.tau` and the compact margins once T16 is in the layer machine | days |

**S1 is checked.** `Networks/Certificates/PR589/Geometry/Moves/` holds 230 chunk certificates, four section
glue files and `Profile.lean`, all generated by `scripts/generate_pr589_moves.py` from the pinned word.
- `phase_ranks`: the `moveRank` of every phase incidence (`phaseEdges`, 29250 pairs) is the certified
  dimension difference, listed as `phaseValues`.
- `phase_histogram`: `phaseValues` has `{0:26339, 1:1323, 2:1342, 3:79, 4:44, 5:102, 6:11, 7:10}`.
- `final_ranks`: all 661 final-alignment incidences have rank zero.
- `copyRanks_eq`: the nine retained COPY ranks are all 7.
- `localPaid_histogram`: the positive phase ranks followed by the COPY ranks have histogram
  `{1:1323, 2:1342, 3:79, 4:44, 5:102, 6:11, 7:19}`, the tuned word's `local_histogram`.

These depend only on `propext`, `Classical.choice` and `Quot.sound`; `phase_histogram` uses no
axioms. As with the rest of the PR589 checkpoint, the root module does not import them. Building
the closure takes the whole PR589 frame replay. The D-section frame chunks and their MOVE
certificates use 6–10 GB each, so build those one module target at a time.

**S2 is checked.** `MathlibTM2/M6/BitOccurrences.lean` builds the nine-stage occurrence list and closes
the open link.
- `nineRanks` is the local paid ranks of the `9·32` local invocations, then 32 replicas of the
  hosted idle remainders.
- `idleRanks` transcribes the schedule rules of `global_k.py`; `idleRanks_four` gives
  `[14, 7, 28, 7, 42, 7, 42, 28, 14, 0]`.
- `patterns` and `stageCounts` are the frozen `selection9-p111.json`. They are checked to cover all
  `2V = 222` copy positions of each idle (`patterns_cover`), to fit inside the idle ranks
  (`patterns_fit`), to agree with the stage counts (`patterns_stageCounts`), and to host all 439
  helpers of every stage (`stageCounts_all`).
- The hosted width 8 is every helper's certified residual width (`helper_width`).
- `nineRanks_realizes : Realizes nineRanks bitHistogram`, so `nine_moment_le` is the selected bit
  bill with no open link. Standard axioms only.
- Window membership of the hosted slots, and the hosting itself, are part of S5.

**S3 is checked.**
- `Networks/Certificates/PR589/Framed.lean` defines the physical framed execution `execute frameOf`:
  the compiled D/A phases, the nine COPY/ADD/ERASE windows, the compiled B/C phases and the final
  alignment edges. `execute_endpoint` shows that on arbitrary dirty streams it decodes every register
  from its initial frame, runs the literal scalar word, and encodes in the final frame. `execute_high`
  shows the temporary and every higher register end at zero.
- `FramedDirty.lean` combines this with `dirty_endpoint`. `execute_dirty` covers any frames, and
  `selected_dirty` uses the selected rational E8 shear frames `Geometry.frame` on `Geometry.Stream`:
  sources and helpers are returned and each target receives its source, all in their final frames.

**S4 is checked.** `MathlibTM2/M6/BitRecurrence.lean`:
- `nineRanks_le`: every rank is at most 42.
- `nine_moment_le_one`: the bit bill, surcharge dropped.
- `bit_variable_closed`: the closed variable-rank recurrence at every `λ > 1 - 10/5769`, the bit
  analogue of `t16_variable_closed`. Its execution premises (child sizes, per-node cost) are the
  hosted interchange machine of S5.

All S3 and S4 results use only `propext`, `Classical.choice` and `Quot.sound`.

S1–S4 are mostly certificate and cost work in new files. S5 is the large machine piece. The
total, conservatively, is 3–5 months, and the leap also needs Kenny's T16 machine.

Checks on the S1 data, from the pinned word `bitE8mut-p111-tuned.json.gz` (SHA-256 `e3e301e6…`):
- all 29911 incidences (29250 phase and 661 final) are root-list nested, over 3014 distinct
  frame pairs;
- the positive phase ranks are `{1:1323, 2:1342, 3:79, 4:44, 5:102, 6:11, 7:10}`;
- the nine COPY ranks of 7 give upstream's `local_histogram`;
- the final-alignment incidences carry no rank;
- the nine-stage profile `bitHistogram` is `288 ×` the local profile at ranks 1, 3 and 5, with
  hosting adding pieces at ranks 2, 4, 6, 7 and 42.

## 6. S5: the PR589 interchange machine

### Where the bit supplier runs

The complex supplier runs in the layer machine (`Layer/Node`, `m = 25³`, and in Kenny's T16 work
`m = 73`). The bit supplier runs in a different recursion: the binary rectangular interchange
`Machine/BinaryInterchangeRun.program`, called by `Host/ChunkSwap` and `Host/PlacedSwap`, with cost
`C · V · max(h, d)^τ` (`BinaryInterchangeBudget.uniform_bound`). Its node is the manuscript's
power-width interchange (§4, `RecursiveInterchangeLayout`): a parent of width `w = m·b` interchanges
two address fields, and the Shared50 network over the World roles calls one child per role on
volume `V/roleCount` (`Shared50RecursiveBudget`). With PR589, a rank-`r` occurrence is a single
child interchange of width `r·b`, that is `(r/64)·w`, which is the `hsize` premise of
`BitRecurrence.bit_variable_closed`.

### What is shared with T16, and what is not

Shared, already in the tree:
- **Semantics.** `FramedCircuit` (compile, edges, encode). S3's `Framed.execute` uses it for the
  PR589 word, as the complex side does for its networks.
- **Cost.** `Layer.VariableRecurrence.variable_closed`. S4's `bit_variable_closed` and Kenny's
  `t16_variable_closed` are two instances of it.

Not shared: Kenny's T16 execution layer (`T16/Impl`). `TInstr` is a rational gate or a `Prim` on
`Arrays 73` over `ℂ`, run through a representation of the 73-bit operators. Its child calls are
rank-one odd kernels: a rank-`r` edge lowers to `r` kernels, and the node makes
`Σ r n_r = 1,041,408` of them (`nodeProgram_children`). This is complex-specific. The bit
interchange's children are interchanges of address fields, so its node program is not a `TInstr`
list.

Generic pieces the leap needs that do not exist yet, and that are Kenny's active front:
1. A batched child: one call per rank-`r` occurrence, of size `(r/m)·e`, in place of `r`
   rank-one calls. `t16_variable_closed` prices this form; the T16 node program still makes
   rank-one calls.
2. The main cost chain consuming occurrence moments in place of `F/NW` (`Cost/Branching`, the
   layer recurrence), together with the node retarget to `m = 73`.

The design does not depend on either. The bit side keeps its own recursion and its existing cost
interface `uniform_bound`. Only the exponent changes, from the Shared50 budget to
`bit_variable_closed`. `ChunkSwap`, `PlacedSwap` and the MathlibTM2 cost chain consume `τ` through
`uniform_bound` unchanged, so the retune (S6) touches parameters only.

### Stages

| stage | content | depends on Kenny | estimate |
| --- | --- | --- | --- |
| S5a | Bank semantics of the nine-stage node: the recipe (local sweeps on pairs with orientation, `±1` bridges, final exchange) acts on the `2K` banks as the identity over `ℤ`, and every single omitted bridge breaks it. Each local sweep acts on its pair as S3's framed endpoint (`target += source` per port). | no | 1–2 weeks |
| S5b | The node's child calls: every rank-`r` MOVE of every local invocation and every hosted idle remainder is one child of width `r·b`, and the node's child list is `BitOccurrences.nineRanks` | no | 1 week |
| S5c | Variable-width child descriptors: generalize `RecursiveInterchangeLayout` so a child selects `r` consecutive sub-fields of the parent's `m`, with the address and size equalities | no | 1–2 weeks |
| S5d | The recursive interchange machine for PR589: roles, stage/replica schedule, owner routes, banks and hosted residuals, child-call protocol (adapting `Shared50Recursive*` and `Recursive*`), base case | no | 2–3 months |
| S5e | Cost: the machine's recurrence meets the premises of `bit_variable_closed`; `uniform_bound` at `τ = 1 - 10/5769` plus the polylogarithmic overhead | no | 1–2 weeks |

S5a and S5b are certificate and semantic work in new files under `Networks/Certificates/PR589/`.
S5c–S5e change the bit-side machine (`Machine/*Interchange*`, `Machine/Shared50Recursive*`). Their
last substantive changes are from 10-08 (the complete binary interchange and its runtime bound).
Since then only the module-system migration (10-11) and an import shake (10-17) have touched them.

### S5a: checked

`Networks/Certificates/PR589/Nine/`:
- `Recipe.lean`: `recipe K` (`global_k.py`'s recipe) and upstream's integer eight-bank matrix
  (`small()`). `recipe_identity`: at `K = 4` the matrix is the identity, with 18 bridge shears.
  `bridge_needed`: omitting any one shear breaks it. `sweep_stages`: the sweeps run through stages
  `0, …, 8` in order.
- `Bank.lean`: the recipe on banks of any `F₂`-module. `stepBank` commutes with additive maps and is
  local to the eight data banks, so one kernel evaluation on coefficient vectors gives
  `recipe_runBank`: the recipe is the identity on banks.
- `Node.lean`: one replica's columns: 888 data columns (bank `b`, port `t` at `111b + t`) and
  `9 · 439` helper columns. The pieces:
  - a sweep runs the selected word on its owner columns, through `moduleRun_rename`, renaming along
    an injection, with `owner_injective`;
  - `sweep_bank`: a sweep acts on each port's banks as the word's dirty endpoint;
  - `bridge_bank`: the bridges act port by port;
  - `node_identity`: the node's sweeps and bridges followed by the exchange relabeling are the
    identity on every column, for arbitrary dirty streams.

Standard axioms only; `recipe_identity` and `bridge_needed` use `propext` alone. Both sweep
orientations use the forward word. The physical reverse stream, its frames and the hosted
coordinates are later stages.

### S5b: checked

`MathlibTM2/M6/BitSchedule.lean`:
- `schedule K` is the node's schedule, the recipe with its idle entries. `windows` transcribes
  upstream's hosting windows.
- `windows_four`: the nine-stage windows
  `{0,1}, {2}, {0..3}, {4}, {0..5}, {6}, {3..8}, {5..8}, {7,8}`, and an empty window for the
  rank-zero idle.
- `windows_ranks`: the idle ranks match `BitOccurrences.idleRanks`. `idle_rank_window`: each idle
  rank is 7 per window stage.
- `selection_in_windows`: every stage that the frozen selection hosts into an idle lies in that
  idle's window, closing S2's open window check.
- `nodeChildren_realizes`: the node's children in schedule order realize `bitHistogram`. They are
  the 32 invocations of each of the nine sweeps, then each idle's remainders in each replica.

The window facts use `propext` (and `Quot.sound`); the child list uses the standard axioms.

### S5c: checked

`Machine/RecursiveInterchangeLayoutRank.lean` (a new file in the existing namespace; Kenny's
`RecursiveInterchangeLayout` is unchanged):
- `childR q roles b m r i j v` is the rank-`r` child on `H` sub-fields `i, …, i+r-1` and `D`
  sub-fields `j, …, j+r-1`, of width `r·b`.
- `childR_index`: regrouping moves no symbol within a role stream.
- `childR_volume`, `childR_volume_div`: a child holds one role stream's volume.
- `childR_positive`, `childR_rows_divisible`, `childR_spectators_bounded`: positivity, row
  divisibility at the next depth, and spectator ranges.
- `childR_width`: the width ratio is `r/m`, the size premise of `bit_variable_closed`.
- `child_eq_childR`: the rank-one child is `child`.

Standard axioms only.

### S5d plan: the PR589 recursive interchange machine

**What the Shared50 machine is.** A node splits its rows cyclically into the `W` World roles plus
an I/O role (`RecursiveRows*`, `Shared50RecursiveNodeRows`). It runs a fixed literal piece list
(`Shared50PieceSchedule`):
- nonrecursive segments: shifts, scalings and XORs on role arrays in one H-before-D coordinate
  layout (`Shared50Nonrecursive*`);
- scalar gates (`Shared50NodeGates`);
- role-specific recursive calls. Each call parks every other role and runs a child H/D swap in the
  cross-field view of the active role (`Shared50RecursiveCall*`, `Shared50RecursiveChildPermutation`).

It then merges the rows. The generic layer (`Recursive*`) holds the call protocol, child setup and
return, dimension arithmetic, the row split and merge, the shift/scaling/XOR primitives and the
width-one base case. It is parameterized by the role count, apart from `RecursiveRowDivisor`
(`W^k`). The Shared50 files hold the network, its piece list, its control graph and its budget.

**What PR589 changes.**
1. Variable-rank call sites. A MOVE of rank `r`, or an idle remainder of rank `r`, is one call with
   descriptor `childR` (S5c), whose sub-fields are fixed by the geometry.
2. Roles. Host-every-residual (`live = 2KVT = 28416`) has no separate helper roles. A helper
   register is a coordinate slice `[off, off + w)` of an idle data family. Operations on helpers
   need sliced coordinate views.
3. COPY/ERASE lifecycles through the nine private registers (`physical = live + 9`).
4. Scale. A node has `288` local invocations of `5583` gates and `904,896` child calls. The
   Shared50 control is a literal piece list, but this one has to be structured (loops over replicas
   and stages, as Kenny's T16 `nodeProgram = template.flatMap eventProgram` is), or the control
   graph and its certificates become unmanageably large. This is the main design risk.

**Sub-stages.**

| stage | content | estimate |
| --- | --- | --- |
| S5d.1 | The compressed nine-stage geometry: per-port Weyl recipes `g_t` (exact rational factorizations, `geometry.py`), the window `m = 1 + 7L`, stage maps `ρ_stage` and data routes, as a Lean certificate | 1–2 weeks |
| S5d.2 | Hosted coordinates: the slots that emission (`emit_k.py`) generates from the frozen selection, disjoint per idle and copy position, inside the windows (S5b), with the residual isometries (`validate_isometries`) | 2–3 weeks |
| S5d.3 | The node program at role level: the structured piece list over the schedule (S5b) with word gates on roles and hosted slices, MOVE and idle children with `childR` positions, COPY lifecycles, bridges and exchange. Its semantics on binary World payloads is the full H/D interchange, from S3, S5a and S5d.1–2 | 3–4 weeks |
| S5d.4 | The physical machine: the Shared50 recursive graph (control, pieces, call sites, parking, budget) adapted to the structured PR589 piece list, reusing `Recursive*`, with the route programs (upstream's elementary factorizations of `ρ`) on its coordinate primitives | 6–8 weeks |
| S5d.5 | Root execution and runtime: a `BinaryInterchangeRun` counterpart whose `uniform_bound` has exponent `1 - 10/5769` through `bit_variable_closed`, then S6 | 2 weeks |

Total, conservatively, 3–4 months. Parts of upstream's hosting pipeline (#442 hosting, #472
emitter) cite review status in their own receipts; those receipts are the sources for S5d.1–2.

### S5d.1: checked

`Networks/Certificates/PR589/Nine/`:
- `PortFrame.lean`: `PortCertificate` holds a port's line `q` and twice its complement columns
  `A`; `Checked` is the integer form of `qᵀq = 4`, `AᵀA = 1`, `AAᵀ + qqᵀ/4 = 1` and `qᵀA = 0`.
  `lineProj = qqᵀ/4`, and `rho = [[P, A], [Aᵀ, 0]]` is a symmetric involution with upstream's
  four conjugation identities (`rho_conj_line`, `rho_conj_one`, `rho_conj_zero`,
  `rho_conj_complement`). `exchange U = [[1 - U, U], [U, 1 - U]]` is the bit address operator
  `D_U`: `exchange_one_mul` (`D_1 D_U = D_(1-U)`), `exchange_mul_self`, `exchange_change` (a
  nested frame change is the exchange on the projector difference) and `exchange_conj` (a
  coordinate change on both address halves conjugates `D_U`).
- `PortData.lean`, generated by `scripts/generate_pr589_ports.py`: the 111 port certificates. The
  script repeats upstream's reflection walk over the 120 E8 lines (`bitE8-r865.json.gz`,
  SHA-256 `1fb726ea…`) exactly and compares the complement columns with upstream's `GEOMETRY.json`
  for the pinned word. `ports_checked` is one kernel evaluation (4.5 GB peak).
- `Stage.lean`: the 64 parent axes `Axis = Fin 8 ⊕ (Fin 8 × Fin 7)` (eight local axes, eight
  exterior blocks of seven) in upstream's numbering (`axisIndex`); the stage routes, symmetric
  involutions (`route_transpose`, `route_mul_self`); the lifted frames `stageLift n U`. The stage
  boundary identities `stage_source`, `stage_source_exit`, `stage_target` and `stage_target_exit`:
  at every stage `n` the word's source frames `P → 1` lift to `sourceFrame n → sourceFrame (n+1)`
  and its target frames `0 → 1 - P` to `targetFrame n → targetFrame (n+1)`, so each column leaves
  a stage in the frame in which it enters the next. `lift_sub` is the orthogonal lift argument (a
  lifted MOVE is the route conjugate of the local one, extended by zero), and `exchange_lift` its
  form for `D_U`. `node_exchange_source` and `node_exchange_target`: after nine stages and the
  exchange of sides, every column's frame is `D_1` after its initial frame.
- `PortLabels.lean`: the certificates are the word's own frames. `root_port` matches the lines;
  `projector_source_initial` (`P`), `projector_source_final` (`1`), `projector_target_initial`
  (`0`) and `projector_target_final` (`1 - P`) identify the orthogonal projectors
  `Geometry.projector` of the port registers' initial and final frames.

All use only `propext`, `Classical.choice` and `Quot.sound`.

For S5d.3:
- **Frame model.** The node identity holds for exchange frames `f ↦ f ∘ D_U`: over the node every
  column changes by `D_1`, the parent interchange. Under the shear frames of `Geometry.frame`, side
  zero would change by the shear of `1 - 2P` and side one by the shear of `1`. `Framed.execute` is
  generic in its frames, so S5d.3 runs the word with exchange frames. By `exchange_change` each
  MOVE is then the partial interchange `D_(P_j - P_i)`; a coordinate change taking the range of
  `P_j - P_i` to `r` axes makes it a swap of `r` sub-fields (`exchange_conj`, `childR`). Whether
  such a coordinate change is cheap on the tape is the open point under "Realizability of the
  PR589 accounting".
- **Left to S5d.4.** Upstream's elementary factorizations of `ρ` (at most 77 swap, scale and add
  factors per port, denominators `1, 2, 4`) are the physical route programs, and their form
  depends on the machine's coordinate primitives. The bank slots and permutations of
  `GEOMETRY.json` are unused: PR589 hosts every residual (`bank_assignments = 0`).

### S5d.2: checked

`Networks/Certificates/PR589/Nine/Flag.lean` (geometry, per port):
- The flag basis of the line's orthogonal space: the seven complement columns, then the 56 exterior
  axes block by block (`pendingIndex`; upstream's chart `A_q` numbers the same axes `1, …, 63`).
  `span x y` projects onto flag positions `x, …, y - 1`.
- The level frames are flag prefixes: `targetFrame_eq` (`span 0 (7n)`) and `sourceFrame_eq`
  (`linePart + span 0 (7n)`). An idle advance from `a` to `b` stages is `span (7a) (7b)` on both
  sides (`pending_source`, `pending_target`).
- `exchange_slots`: the exchange of a pending interval is the product of the exchanges on `k`
  eight-wide slots and on the remainder.
- `slotChart x` embeds a helper's eight local axes isometrically onto the slot at position `x`
  (`slotChart_orthonormal`, `slotChart_proj`). `rank_conj` keeps ranks, so a hosted MOVE
  (`rank_slot_sub`) and a lifted MOVE at every stage (`rank_lift_sub`) have their local ranks.

`MathlibTM2/M6/BitHosting.lean` (the frozen selection, expanded):
- `levelRun_eq`: the schedule replays with every sweep of stage `s` at level `s`, every bridge at
  equal levels and every idle advancing its pair to the current stage at rank `7` per stage, ending
  with all pairs at level `9`; `idleLevels` are the idles' source and target levels.
- `slots`: upstream's expansion of `selection9-p111.json`, 3951 slots per replica (`slots_length`),
  equal to upstream's emitted slot list (`slots_fingerprint`). Every slot lies in its idle's window
  and off the active pair, at an offset `8j` with `j < 5`, inside the pending interval
  (`slot_in_window`, `slot_off_active`, `slot_fits`, `slot_in_pending`). Every helper of every
  stage is hosted exactly once (`slot_helpers`), and distinct slots differ in idle, copy or offset
  (`slot_key_injective`).
- `idle_pending`, `idle_hosting`: on every copy, an idle's advance is the product of its hosted
  slots' exchanges and the remainder's; `rank_remainder` gives the remainder rank, and
  `remainders_perm` shows the remainders are those of the occurrence list (S2).
- `helper_frames`: helpers start in frame `0` and end in the full frame, so the residual isometry is
  the slot chart itself (entrance rank `0` for every PR589 helper).
- `hostClass_distinct`, `hostClass_bijective`: the host classes below.

All use only `propext`, `Classical.choice` and `Quot.sound`.

**Host classes.** In one invocation a family can host up to five helpers, on slots of one idle
(`same_pair_windows`); at stage 2, registers 232–236 (helpers 10–14) share one family
(family 666 in replica 0). The helpers are separate registers, so they need separate storage. Upstream's model
indexes every physical stream by a family and an element of the full orthogonal group
`O(I_64/2, F_q)` and visits every element (`pr589-five-helper-hosting`, PROOF.md §2 and §4), an
astronomically large number of streams.
Five row classes suffice: split each family's rows into five classes, run each invocation once per
class `d`, and give the helper on the slot at offset `8j` class `d + j mod 5` of its host family.
Within a run the owners are distinct, and over the five runs each class of a host family receives
each residual once. The node then has `5W = 142080` roles; every child appears five times with
weight `1/(5W)`, so the occurrence moment, and `bit_variable_closed`, are unchanged. The machine's
row divisor becomes `5W`.

**Routes.** In upstream's model the data routes `ρ` and the slot charts act on the class labels
of the cover streams, not on the payload's address digits. Here they are coordinate changes
applied to the data columns and the hosted streams before and after each invocation; their
physical cost is the subject of "Realizability of the PR589 accounting".

### S5d.3: checked, conditional on upstream's idealization

The invocation and stage layers:
- `Nine/StreamFrames.lean`: exchange frames `f ↦ f ∘ D_U` on bit streams.
- `Nine/Invocation.lean`: the framed word in its stage window, forward and reflected, on arbitrary
  dirty registers.
- `Nine/Charts.lean`: stage routes; the port chart `A_q` and the helper charts onto slots.
- `M6/BitInvocation.lean`, `M6/BitInvocationFrames.lean`: one class run on the `5W = 142080` roles.
  Both sides of the active pair change between their stage frames, and a hosted helper's role
  changes by the exchange on its slot (`invoke_host`).
- `M6/BitStagePiece.lean`, `M6/BitStageHost.lean`: all 160 class runs of a stage. Each role of
  another pair changes by the exchange on the sum of the slots its family hosts at that stage.

The node:
- `M6/BitNodeProgram.lean`: `nodeProgram`, the node as 29 pieces, one per schedule entry
  (`nodeProgram_schedule`): stage pieces, remainder pieces (the exchange on the pending interval
  the hosted slots leave), bridges and the exchange of sides. `logicalStep` runs the same schedule
  on logical streams. Kernel facts give the levels and pending slots, checked on the 14
  (idle, stage) pairs that occur.
- `M6/BitNodeFrames.lean`: after `τ` entries a role is stored in the exchange frame `frameAt τ ρ`:
  the line on side zero, the flag prefix `span 0 (7·level)`, and its family's pending slots.
  `Inv τ X L` says every role is its logical stream in that frame.
- `M6/BitNodeSteps.lean`, `M6/BitNodeIdle.lean`: every piece keeps `Inv` (`sweep_step`,
  `idle_step`, `bridge_step`).
- `M6/BitNodeInterchange.lean`: `runNode_interchange`. On arbitrary dirty streams the node changes
  every role by `D_1`. The logical streams return by `Nine.recipe_runBank`, and each role ends in
  its exchanged frame.
- `M6/BitNodeCost.lean`: the child list `nodeChildren5` realizes `fiveHistogram`, five times
  `bitHistogram`. At weight `1/(5W)` the occurrence moment is at most one at `1 - 10/5769`
  (`five_moment_le_one`), and `five_variable_closed` instantiates the variable recurrence. The
  headline `five_class_node` collects these facts.

All use only `propext`, `Classical.choice` and `Quot.sound`. `BitNodeCost` peaks at 4.0 GB.

**Scope: an upstream-conditional certificate.** These theorems certify upstream's PR589 accounting
under its idealization. Each frame change is an exact partial swap priced as one child of its
rank, and the routes and charts are exact coordinate changes priced at nothing.
`five_variable_closed` takes the per-node cost as the hypothesis `hcost`, and only a machine that
realizes the idealization discharges it. The next section finds no such machine on this tape.
S5d.4 and S5d.5 need one.

### Realizability of the PR589 accounting

The accounting `bitHistogram` prices every frame change of rank `r` as one child interchange of
width `r·b`, and every route and chart as free. The physical machine does not support either
directly:
- **Cheap coordinate operations are lower triangular.** In the H-before-D layout the nonrecursive
  primitives are scalings and shifts whose control precedes the target
  (`FlatCoordinateSchedule.Op`), plus cross shears of D by H. A child swaps H and D sub-fields
  `S`. Every product of cheap operations with one child has a lower-triangular H-to-D block, so the
  exchange on a non-diagonal symmetric projector difference is not one child.
- **Oblique frames.** Giving each label `V` the idempotent with range `V` and kernel spanned by the
  coordinates that are not pivots of `V` makes every frame lower triangular, keeps nesting, and makes
  each frame change a legal conjugate of the swap of its new pivot coordinates, of the same rank.
  Those coordinates are in general not consecutive sub-fields, and `childR` and the recursion's
  layout need consecutive ones.
  There is also an endpoint obstruction for complementary oblique frames.
  At a port with line projector `P`, the word requires the source line and its orthogonal
  target hyperplane (`Nine.projector_target_final`). If `U` fixes the source line
  and `1 - U` fixes the target hyperplane, then `U P = P` and
  `(1 - U)(1 - P) = 1 - P`, hence `U = P`. For a line with two nonzero coordinates,
  `P` has an entry above the diagonal (`PortCertificate.incompatible_port_frames`).
  In the pinned `Nine/PortData.lean`, 103 of the 111 lines have four nonzero coordinates.
  Thus `oblique_stage_route` proves boundaries for a changed target hyperplane at those
  ports. Using that route requires a word or a separately costed change of frame that
  realizes the changed target. The explicit correction `target_frame_correction` is a
  shear of rank at most one. Charging one extra unit-rank child per affected target per
  invocation already costs `103 · 9 · 32 = 29664` in the single-class profile. At exponent
  one the spare rank mass is only `64 · 28416 - 1808352 = 10272`, enough for 35 such
  children per invocation (`M6.bit_extra_rank_budget`). A correction charged
  independently at every affected port therefore exhausts the saving even before routing.
  At the selected saving `10/5769`, one additional rank-one child in the entire single-class
  profile already takes the moment above one, even with zero bad-residue surcharge
  (`M6.bit_one_extra_child_over_budget`). Retaining that exponent requires paying for the
  correction inside existing charges, reducing another charge, or changing the profile.
  A common basis change for the original line projectors cannot remove all port dependence.
  For two unit-line projectors `P,Q`, write `a = tr(PQ)`, the squared normalized inner
  product. Since `PQP = aP` and `QPQ = aQ`, cyclicity of trace gives
  `tr((PQ-QP)²) = 2a(a-1)`. Two lower triangular matrices have a strictly lower triangular
  commutator, so simultaneous triangularization forces this trace to vanish. Distinct
  rational port lines can therefore share a triangularizing basis only when orthogonal.
  Ports 1 and 8 (zero-based) have `a = 1/4`, giving trace `-3/8`.

  Orthogonal groups do admit shared bases: extend their line vectors to an orthogonal
  basis over the rationals. In dimension eight each group has at most eight ports, so
  covering the 111 distinct lines takes at least 14 bases. A constructive upper bound
  is 17: traverse the pinned ports in order and assign each to the first group in which
  it is orthogonal to every previous member, starting a new group when necessary.
  The resulting group sizes are `8,8,6,8,7,8,8,8,6,6,4,6,7,8,6,3,4`.
  This groups port endpoints only. Internal word frames, cross-group transitions and
  executing each basis change on tape still need accounting.
- **Routes and charts are coordinate permutations.** The stage routes `ρ` and the helper charts
  are orthogonal and not triangular; in Bruhat form each route contains 7 sub-field
  transpositions per field, for all 111 ports. On a tape they move data from less significant
  sub-fields into more significant ones, which costs an interchange of those sub-fields. A
  compressed geometry needs port-dependent routes, because the word adds registers of different
  ports in one frame.

**Cost model.** A node's nonrecursive work must be `O(V)`: a constant number of linear passes,
with a constant independent of the width. The linear passes are scalings of one address coordinate,
shifts whose control sub-field is more significant than the target (`FlatCoordinateSchedule.Op`),
cross shears of D by H, XORs and copies of role arrays, and relabeling roles. An operation that
moves data from a less significant sub-field into a more significant one (an upper transvection or
a sub-field transposition) is an instance of the interchange problem: if a transposition of two
width-`b` sub-fields were linear, the parent interchange, 64 such transpositions, would be linear.
Implementing an upper shift by offset copies takes one pass per digit of the shift amount, so
`O(V · width)` per node.

**Verdict for this machine.** With these costs the PR589 accounting gives no bit saving.
- *Compressed geometry.* At `λ = 1` the base moment is `63.6385/64 = 0.99435`, a slack of `0.0056`.
  The routes add at least two width-`7b` interchanges per active column per stage, about `4.5` per
  role and `+0.49` to the moment.
- *Uncompressed geometry* (`m = 72`, one block of 8 axes per stage, no routes). A saving needs
  child mass below `m·W`, since at `λ = 1` the moment is the mass over `m·W` whatever the ranks.
  PR589's only coordinates exchanged without a child are the shared line: side zero starts in
  `P_t` and side one ends in `1 - P_t`, one per role, against `0.638` per role of COPY overhead.
  That needs the side asymmetry inside the active window at every sweep. With a block per stage it
  leaves the window; moving it to a port-independent axis outside the windows makes every sweep add
  the other side through `τ = D_u`, and the recipe's bank matrix over `F₂[τ]/(τ² - 1)` is `τ·I`,
  which cancels it. The mass is then at least `72.638·W`.
- *Upstream's fast routes* (`selected-bit-stream-routes`, `selected-bit-fast-primitives`) index every
  stream by a class of `GL_64(Z/q^w)`. A route is the right action on the class label: a
  permutation of the `|GL_64(F_q)|` low-class blocks and carry-aware updates of the `4096` label
  fields of fixed width `w - 1`, through a bootstrapped interchange at that width; this gives the
  local toll `O_q(V(n + w^(1-a1)))`. Our roles carry no class label, so a route acts on the payload's
  own sub-fields, of width growing with the node, and costs about `V·n·w^p` per node in place of the
  sum. Upstream's result is itself conditional: it leaves open the finite-cover to stopped-GL domain
  bridge, data-dependent normalizers for the MOVE children, the correlated-helper premise and the
  COPY lifetimes. Completed, a class-indexed machine bootstrapped once from Shared50 would give
  `a_b = c(1 - c) = 1.697·10^-3`, `c = 17/10000`.

The semantic five-class node (S5d.3) certifies upstream's accounting under ideal routes and
partial swaps. Its exponent `1 - 10/5769` holds under that idealization only.
