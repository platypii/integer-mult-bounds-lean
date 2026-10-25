# Plan and progress

✅ Complete · 🟡 In progress / partially complete · ⬜ Not started.

**Bound improvement progress:** M1 ✅ · M2 ✅ · M3 🟡 · M4 ⬜ · M5 🟡 · M6 🟡 · M7 🟡 · M8 ⬜ (legacy route deferred) · M9 ⬜ · M10 ⬜ · M11 ⬜.
The completed compact multiplier proves saving `4222422970/2^46 ≈ 2^-14.0246`.
With today's bit supplier (PR97 stage 2 on design-B frames), the ceiling in this
outer plan is about `2^-12.98`; going further needs a better bit supplier.
The long-term target is **unconditional `kappa = 0.0023`**, with smaller checked
machine bounds delivered along the way. Design-B is now the running supplier.

## Bound scoreboard

We measure progress by the **proved exponent saving `kappa`** in worst-case
time `O(n (log n)^(1-kappa))`. Larger saving means a smaller time exponent.

| Bound | Exponent saving `kappa` | Proved (UTC) | Status |
| --- | --- | --- | --- |
| **Current unconditional result** | **`4222422970/2^46 ≈ 2^-14.0246`** | 2026-10-22 09:33 | ✅ PR97 design-B frames run in the existing reversed supplier and fixed Mathlib machine. The actual signed histogram proves the stopped moment gap at `tau* = 1-1240/10^7`; the F L F wrapper uses `theta = 1/1000`, giving `tau = 1-123879734039/10^15`. `lambda = 1-12387973/10^11`, `lambda' = 1-12387972/10^11`; the binding layer margin is rounded down to `2^-46`. About 27.97% more saving, or 0.35576 bits, than the plain-frame result. |
| **Previous plain-frame result** | **`3299646951/2^46 ≈ 2^-14.3803`** | 2026-10-21 10:10 | ✅ Superseded; PR97 stage 2: the bit interchange's root runs the stage-2 supplier (`M8/Stage2Machine/Total`): the reversed family over atoms with variable-rank block children (#104's opposite-bank compiler on plain frames, stopped recursion at `tau* = 1-969/10^7`) inside the F L F wrapper, width `theta = 1/1000`. `tau = 1-96806834039/10^15` replaces `1-3734039/10^12`, about `26` times the saving. `lambda = 1-9680683/10^11`, `lambda' = 1-9680682/10^11` sit just above `tau`; the layer margin `epsilon (1-lambda')` binds, rounded down to `2^-46`. |
| **Previous full-width result** | `127238784/2^46 ≈ 2^-19.0770` | 2026-10-19 06:54 | ✅ Superseded; full-width chunks: the chunk root is `Kroot = ⌈d/2⌉` (`c = 1`), so the layout margin is `epsilon (1-tau)`. The direct-round log factor is bounded by the legacy `2^-32` chunk, so it no longer caps `c`. `lambda = 1-3734/10^9`, `lambda' = 1-3733/10^9` sit just above `tau`; the layer margin `epsilon (1-lambda')` binds, rounded down to `2^-46`. |
| **Previous PR97 seven-eighths result** | `111364923/2^46 ≈ 2^-19.2693` | 2026-10-19 01:42 | ✅ Superseded; PR 6: the bit interchange runs PR97's two-stage partial-swap word with rank-one children on the recursive interchange machine, made generic in the bit network (`MathlibTM2/M8/`). The word needs no routes, charts, cover classes or helper hosting. `tau = 1-3734039/10^12` replaces Shared50's `1-296/10^11`, about `1261` times the saving. `lambda = 1-35/10^7`, `lambda' = 1-33/10^7`; the layout margin `epsilon c (1-tau)` binds, rounded down to `2^-46` ([note](docs/pr97-stage1/pr97-stage1.pdf)). |
| **Previous T16 seven-eighths result** | `88279/2^46 ≈ 2^-29.5702` | 2026-10-18 17:18 | ✅ Superseded; T16 node with seven-eighths-power chunks `K = ⌊d^(7/8)⌋` (`c = 7/8`, from PR 4). The binding layout margin `epsilon c (1-tau)` grows by `7/2`; `lambda = 1-28/10^10`, `lambda' = 1-23/2^33` keep the layer margin `epsilon (1-lambda')` above it. The saving is the layout margin rounded down to `2^-46`. |
| **Previous T16 result** | `25222/2^46 ≈ 2^-31.3776` | 2026-10-18 09:47 | ✅ Superseded; T16 layer node: 73 slots, 14336 data roles and 8 private centres, 1,041,408 children (`log_73 (F/NW) < 999/1000`), lowered to factors, half-integral gates, translations, slot XORs and slot phases on the layer machine. With `lambda = 1-2/10^9`, `lambda' = 1-2^-30` the layer margin `epsilon (1-lambda')` no longer binds; the saving is the layout margin `epsilon c (1-tau)` rounded down. |
| **PR 4 mixer result** | `651/2^39 ≈ 2^-29.6534` | 2026-10-18 05:03 (branch) | Proved on the `further-improvements` branch only; not adopted. Size-25 mixer supplier (`sigma = 1-25/10^10`) with `c = 7/8`, binding layer margin `epsilon (1-lambda')` at `lambda' = 1-21/2^33`. T16 replaces the mixer in the complex-supplier slot. |
| **Previous T25 result** | `14229/2^46 ≈ 2^-32.2035` | 2026-10-17 21:11 | ✅ Superseded; retune to `epsilon=31/64`, `delta=2^-7`, `lambda'=1-459/2^40`: the Schönhage–Strassen allowance is `M(p) = p^{1+2^-7}`, the resampling envelope uses the logarithmic band width `α ≤ 4 b^{ε/2^33}`, and every size relation (moduli room, `d ≤ 2^(ℓ-1)`, `d+1 ≤ ℓ`, `16 d α² ≤ b`) is re-proved from `d^64 ≤ b^31` with `d ≥ 2^192`. All-input correctness and cost bound on one fixed finite Mathlib machine. |
| **Previous T25 dimension result** | `3213/2^44 ≈ 2^-32.3512` | 2026-10-17 19:40 | ✅ Superseded; `epsilon=7/16`, `delta=2^-5`. |
| **Previous dyadic-dimension result** | `36261/2^48 ≈ 2^-32.8539` | 2026-10-17 17:29 | ✅ Superseded; `epsilon=79/256`, capped by the coarse `α ≤ 2√d` resampling bound. |
| **Previous rounded result** | `2^-33.0000` | 2026-10-17 08:08 | ✅ Rounded synthetic layers and transforms at `epsilon=9/32`. |
| **Previous dyadic result** | `2^-34` | 2026-10-15 21:00 | ✅ Superseded by rounded synthetic layers, which allow the `9/32` dimension. |
| **Previous eighth-root result** | `2^-35` | 2026-10-15 19:56 | ✅ Superseded by the audited dyadic dimension retune and fourth-root chunks. |
| **Previous dimension result** | `2^-36` | 2026-10-15 19:25 | ✅ Superseded by the audited eighth-root retune and sharper logarithmic cost estimates. |
| **Previous compact result** | `2^-37` | 2026-10-15 18:55 | ✅ Superseded by the checked sixteenth-root dimension retune. |
| **Historical M2 result** | `2^-66` | 2026-10-15 12:42 | ✅ Superseded; the current theorem improves the public saving by more than `2^36`, not a measured runtime speedup. |
| **Historical M1 result** | `2^-93` | 2026-10-15 09:37 | M2 improves the public exponent saving by `2^27`; this is not a timing speedup. |
| **Pre-M1 unconditional result** | `296 / (10^11 * 2^131)` (between `2^-160` and `2^-159`) | 2026-10-15 05:31 | Superseded by M1; the existential theorem remains compatible. |
| **Intermediate benchmark: selected community construction** | **`836330098538459 / 500000000000000000 = 0.001672660197076918`** | — | ⬜ Not yet proved here. Upstream construction is conditional; matching this saving is a benchmark, not a requirement to reproduce its older construction. |
| **Long-term target: productive helper construction** | **`23/10000 = 0.0023`** | — | ⬜ Upstream PR 4359 is conditional; requires new supplier, compiler, cover, and outer execution proofs here. |

The long-term target corresponds to a log exponent of `0.9977`.
The intermediate benchmark corresponds to `0.998327339802923082`.
These are asymptotic exponent bounds, not measured execution speedups.
Update the current-result row only after the stronger machine theorem passes
the guarded checks and axiom audit; parameter arithmetic or a finite
certificate alone does not improve the proved multiplication bound.

**Integer multiplication below `n log n` is proved.**
`IntegerMultBounds.MathlibTM2.statement` constructs a fixed finite Mathlib
machine that multiplies every input pair correctly in worst-case time
`O(n (log n)^(1-kappa))`, with positive saving
`kappa = 4222422970/2^46`. No algorithmic or runtime assumption remains.

## Completed proof

| Part of the proof | Source | Mathematics | Tape | Files |
| --- | --- | --- | --- | --- |
| [Proved Mathlib end-to-end multiplier](plan/C-mathlib-end-to-end.md) | — | ✅ 1/1 | ✅ 1/1 | 1096 |

The [proof details](plan/C-mathlib-end-to-end.md) cover the numerical
algorithm, recursive layers, transforms, resampling, CRT routing, exact
recovery, fixed-machine assembly and actual step bound. All are complete.
The machine model is Mathlib's `Turing.FinTM2`, with standard binary encodings.
The Files column counts the components listed in that detail file; the full
transitive proof dependency set is larger, as recorded by the
[retention audit](docs/proof-retention.md).

At `4222422970/2^46` the checks pass: `CompletedProofCheck` (only `propext`, `Classical.choice` and
`Quot.sound`), `AxiomAudit` (340777 declarations) and `CompactControlCheck` (521 contracts).
The native-machine bridge and its `MathlibTM2Check`/`FastPathCheck` audits were removed
2026-10-18 (restore from 5e12c129).

**Corollary.** `MathlibTM2.DFT.dftInTime : DFTInTime (4222422970/2^46)`: one fixed finite machine
computes the discrete Fourier transform over every prime field `F_p`, at every length with a
primitive root of unity, in time `O(N (log N)^(1-kappa))` (`docs/dft/dft.pdf`).

## Where the bound stands

Parameters (`Cost/CompactInterimParameters.lean`): `epsilon = 31/64`, chunk root `⌈d/2⌉` (`c = 1`),
`tau = 1-123879734039/10^15` (`Parameters.tau`, the selected bit supplier's exponent),
`lambda = 1-12387973/10^11`, `lambda' = 1-12387972/10^11`, `delta = 2^-7`.

| Stage margin | Formula | Value |
| --- | --- | --- |
| Compact layer (binding) | `epsilon (1-lambda')` | `6.0004e-5 ≈ 2^-14.025`, rounded down to `kappa` |
| Chunk-exchange layout | `epsilon (1-tau)` | `6.0004e-5 ≈ 2^-14.025` |
| CRT and resampling exposure | `(1-epsilon)(1-tau)` | `6.3875e-5 ≈ 2^-13.934` |
| Gaussian resampling | `1/2 - delta - epsilon(1+2^-33)` | `2^-7 - 31/2^39 ≈ 2^-7.0` |
| Direct rounds | `epsilon (1-2^-32)` | `0.484` |
| Prefix (M5a) | `1-epsilon` | `0.516` |

**The `tau` ceiling.** `1-tau = 1.2388e-4 ≈ 2^-12.98` is the saving of the bit interchange. Every
margin near the top of the table carries it. The layer margin carries it too, because
`lambda' > lambda > tau`.

- **Retuning alone** is exhausted: the layout and layer margins both sit at `epsilon (1-tau)`,
  and the exposure margin `(1-epsilon)(1-tau)` falls as `epsilon` rises.
- **Near-one dimensions** reach about `1-tau ≈ 2^-12.98`, one bit. That needs `epsilon → 1`, which
  needs M7, M5b and the bulk exposure transfer
  ([NearOne/DESIGN.md](IntegerMultBounds/MathlibTM2/NearOne/DESIGN.md) §c).
- **Beyond `2^-12.98`** a better bit supplier is necessary (M6, then M10). Upstream's selected PR589 supplier
  has bit saving `10/5769`, but its accounting does not transfer to this machine: helper hosting,
  port routes and frame changes are not free here ([pr589-hole](docs/pr589-hole/pr589-hole.pdf)).
  The cover-free suppliers and candidate improvements are ranked in the
  [PR97 note](docs/pr97-stage1/pr97-stage1.pdf): PR97 with flag-basis corner runs
  (`a_b = 6.40e-5`), and #104's opposite-bank compiler on PR97 (`9.70e-5` plain frames, superseded by the integrated `1.24e-4` design-B frames).

## Bottlenecks by manuscript section

Section numbers are the [original manuscript](plan/D-sharper-bound.md)'s printed numbers.

| Manuscript section | Progress | What limits our bound | Improvement needed |
| --- | --- | --- | --- |
| §2 Machine model and streams | 🟡 | Every new algorithm needs actual finite-machine costs and clean returned state. | Price new schedules with the existing host primitives. |
| §3 Finite networks | 🟡 | Bit saving `1-tau = 1.2388e-4` (PR97 stage 2, design-B frames) caps every margin. Complex: T16 at `log_73 (F/NW) < 999/1000`, in the proof. | Design-B completed (M6); next productive complex jobs and delayed-cover BIT (M9–M10). |
| §4 Address interchange | 🟡 | Field moves inherit `tau`; the CRT uses linear direct routing. | Arbitrary-source coordinate routing (M5b). |
| §5 Butterfly layers; Appendix A | 🟡 | The T16 node takes the layer margin off the critical path. | General supplier closure, stopped recursion, precision and recursive stock (M3, M4), instantiated for M9. |
| **§6 Synthetic transforms/layout** | 🟡 | **The layout margin `epsilon (1-tau)` and the layer margin `epsilon (1-lambda')` bind together.** The balanced prefix (M5a) and full-width chunks are done. | M5b with `epsilon → 1` lifts the layout margin to `1-tau`. |
| §7 Exact polynomial products | ✅ | Packing widths must stay within budget. Not binding. | Revalidate under new widths. |
| §8 Resampling | 🟡 | The Gaussian margin keeps `epsilon < 1/2`. | The rest of M7: tape costs and bulk core/halo execution. |
| §9 Exact multiplication/cost | 🟡 | The exposure margin `(1-epsilon)(1-tau)`. The moduli are short-interval primes, so they no longer bound `epsilon`. | Grouped/fused bulk exposure and complete outer execution (M11); legacy M8 is deferred. |
| §§10–11 Corollaries | 🟡 | Not multiplication bottlenecks. | DFT over `F_p` done (`dftInTime`); division, square root and transposition not started. |

## Milestones

✅ means the whole deliverable is checked. M1–M8 are historical identifiers, loosely
organized by manuscript section, not a dependency order. The execution order below
controls the active queue. The [implementation plan](plan/D-sharper-bound.md) and
linked design notes contain reusable details and historical checkpoints; their older
parameter choices and route-specific completion lists are not all prerequisites for 0.0023.

| ID | Progress | Sections | Deliverable | Status |
| --- | --- | --- | --- | --- |
| M1 | ✅ | §§5, 6, 9 | Retune the existing construction. | Historical, `kappa = 2^-93`. |
| M2 | ✅ | §§4.3, 8.2, 9.3 | Direct nonadjacent CRT swaps. | Historical, `kappa = 2^-66`; the running CRT still uses it. |
| M3 | 🟡 | §5.2–5.3, App. A | Compact controls, caller integration, stopped recursion. | Compact integration complete; it is the current theorem. Stopped-recursion integration remains. |
| M4 | ⬜ | §5.4, §9.7 | Linear child-precision bound; recursive workspace and stock. | Derive constants from the actual finite template and account for simultaneous owned centers and BIT stock; feed M9–M11. |
| M5 | 🟡 | §6.2, §4 | Balanced prefix (M5a); arbitrary-source routing (M5b). | M5a done (`CompactStageGrowth.prefix_le`). M5b open ([design](IntegerMultBounds/MathlibTM2/Balanced/DESIGN.md)). |
| M6 | 🟡 | §§3–5 | Selected finite suppliers in the machine. | T16 complex supplier and the PR97 design-B bit supplier are in the proof. The complete gauged compiler word has arbitrary-input semantics, checked signed geometry, a kernel-linked cost histogram and strict child ranks. `Stage2LinkB` proves the two moment gaps; `RevNetwork` and `Rev97Machine` select that node. The stopped family (`Rev97Ranks`, `RevMachine.RevSemantics.rev97_family_spec`) and F L F wrapper (`Stage2Machine.Bound.uniform_bound`, `Stage2Machine.Total`) deliver the current public bound. The design-B checkpoint is complete; no further design-B optimization is planned. PR589 bit side remains checked only under upstream's idealization (`M6/Bit*`, outside the root); it does not run on this machine ([design](IntegerMultBounds/MathlibTM2/M6/DESIGN.md)). |
| M7 | 🟡 | §§8, 9.2, 9.7 | Faster rounded Gaussian inverse, prime supply, bulk execution. | Prime supply done (`primes_in_window`, `primeSrc_good`). Rounded inverse composed (`rounded_inverse`); chirped forward map approximated (`chirpA_approx`). Tape costs and bulk execution remain ([design](IntegerMultBounds/MathlibTM2/NearOne/DESIGN.md)); align new work with M11's fused, support-local outer contracts before implementing an older schedule. |
| M8 | ⬜ | §9.1–9.8 | Legacy selected bootstrap and 47 inequalities. | Deferred as a route-specific package. Reuse applicable transfer lemmas; reproducing its seven stages or PR589 supplier is not required for M11. |
| M9 | ⬜ | New supplier/compiler | Productive mixed jobs compiled into a finite uniform supplier. | Prove arbitrary-input endpoints, ownership, complements, integer batching and chronological execution; instantiate the p3 complex controller at uniform saving `0.002304`. Depends on the supplier closure and precision/stock work in M3–M4. |
| M10 | ⬜ | New BIT supplier | Delayed ambient cover and ordinary BIT saving above `0.0027`. | Use M9's mixed-job construction with projector covariance, common weights, modular matchers, priced cover routing and bad-class fallback; raise the atom exponent and prove the new stock bound. Reuse generic stopped-recurrence and wrapper results. |
| M11 | ⬜ | New outer assembly | Unconditional fixed-machine theorem at `kappa = 0.0023`. | Combine M9–M10 with M4, M5b and the adapted M7 work: grouped/fused execution, global support-local phases, boundary matrix costs, new sizing and every outer cost matched to actual execution. |

## Execution order and decision gates

**Design-B compiler/frame checkpoint complete (independent of routing).** The structural adjoint,
pending-use and combined-boundary lemmas are generic in the DAG or operation list;
they are useful beyond the concrete design-B tables. The full backward-weight
recurrence, source coverage/order, exact data traces and complete auxiliary/target/source
frame chains in both stages are now checked.
Current details are in [M8/DESIGN.md §16](IntegerMultBounds/MathlibTM2/M8/DESIGN.md#16-design-b-frames).

**Design-B integration complete.** The existing recursive machine now runs the
gauged design-B node, including source/target paths, exteriors, connectors and all
owned temporaries. Its actual signed-chain histogram, arbitrary-ring/reversed
execution and strict block-child ranks are proved. The stopped saving is
`1240/10^7`, and the ordinary supplier exponent is `1-123879734039/10^15`.
The retuned end-to-end machine proves `4222422970/2^46 ≈ 0.00006000424`, about
27.97% more saving (0.35576 bits) than the plain-frame result. The full guarded
build, completed-proof audit, root axiom audit and compact-control audit pass.
No further design-B-specific optimization is planned. Its generic compiler/frame
proofs survive a future supplier replacement; M9–M11 remain the next direction.

**Define the new contracts before further old-route integration.** Pin the M9 mixed-job
interface and M11 outer execution requirements, then direct M3–M5 and M7 work toward them.
Keep generic stopped recursion, completed-child precision, owned storage, coordinate
routing, analytic identities and exact recovery. Do not finish an older scanner, reserve,
Gaussian schedule or numerical bootstrap solely to check off a historical milestone.
The older PR589 machine integration and exact M8 seven-stage/47-inequality package are
optional alternatives, not the active critical path.

**Develop suppliers and outer execution as separate work streams.** M9 supplies the
finite mixed-to-uniform construction shared with M10; M10 supplies the stronger ordinary
BIT bound. M4's bounds must close for those actual templates. M5b and the adapted M7 work
supply M11's routing and grouped/fused execution. Preserve the current multiplier as a
working instance while introducing the needed general interfaces.

**Integrate smaller wins whenever all affected costs close.** Design-B is the immediate
candidate. Later routing, resampling and supplier improvements may yield intermediate
bounds before M11 is complete; each must include every affected execution and cost
contract. With today's supplier the near-one route is limited by its approximately
`0.000096807` saving. With the new complex saving but today's dimension, the layer
margin alone is only `0.001116`: reaching 0.0023 needs both work streams. These are
planning margins, not promised intermediate machine theorems. Reaching or exceeding
`0.001672660197076918` is a useful benchmark by whichever proved route reaches it first.

After each successful integration, record the proved saving, binding margin and guarded
checks/axiom audit. Component certificates and parameter arithmetic do not move the scoreboard.
The current numerical saving already exceeds the old bootstrap base `0.0000384599`;
whether it supplies a particular bootstrap interface still requires an explicit theorem.

## Routing work packages (M5b)

Routing is now an active work stream alongside the design-B checkpoint. R1–R4 are
local work-package labels in dependency order, not replacements for M1–M11. They
must provide the global support and spectator contracts required by M11, not only
the old layout's cheaper numerical bound. Implementation notes and the next concrete
obligation are in [Routing/DESIGN.md](IntegerMultBounds/MathlibTM2/Routing/DESIGN.md).

| Package | Status | Deliverable and acceptance gate | Additional Lean, estimate |
| --- | --- | --- | --- |
| R1 selective updates | ✅ | Complete selective primitive: arbitrary ordered allowed sources, physical good-set XOR, full source/spectator and borrowed-field restoration, global rank permutation, and executed setup/routing/cleanup with every phase priced. `SelectiveRouter.selectiveRouting_exec` instantiates concrete register placement, canonical header values, logarithmic guard widths and the physical exceptional bound `5 / (128 scale³)`. See [completion audit](IntegerMultBounds/MathlibTM2/Routing/R1-AUDIT.md). | ~6.5k |
| R2 exact repair | ✅ | Complete all-address selective primitive. `exactSelective_exec` in `ExactSelective.lean` executes all 34 metadata installations, complete-rank keying, R1 routing, physical classification, exceptional extraction/radix sort/merge/key stripping, and final cleanup on one concrete bank. Every register except the output stream is restored; canonical headers, explicit logarithmic guards and the physical density price the total cost. See [completion audit](IntegerMultBounds/MathlibTM2/Routing/R2-AUDIT.md). | ~2.7k |
| R3 complete router | 🟡 | Matching/reservoir partition, permutation decomposition, descriptor generation and short-record fallback. Compose R1–R2 into a full arbitrary-coordinate routing program, with all borrowed fields restored. | Estimate retired; see sizing audit below |
| R4 integration and support | ⬜ | Forward/inverse layout replacement and cost matching; preserve reserved coordinates and a complete untouched suffix for M11's grouped phases. Supplies S4's movement interface. | 3–6k |

R1 checkpoint: `Routing/Shear` and `PackedShear` prove the logical and packed
endpoints, arbitrary borrowed-field restoration, target upper-bit preservation,
and exceptional-set/repair identities. `Coordinates.program_decode` identifies the
packed endpoint with the requested coordinate shear; `PhysicalBits.program_physical`
identifies the actual radix-two target bits. `Density.encoded_repair_density` retains
the complete source/spectator tensor without changing the exceptional fraction.
`SourceGather.sourceOffset_exec` implements gathering and spreading **in increasing
source order**, restores gathering scratch, and charges `8 W + 8 n G + 2 n + 18`
host steps. `packed_read_eq` identifies its offset with the packed gadget's source
value. Source/mask registers are inputs to this call, so mask setup remains charged
at the future caller; arbitrary source ordering is not silently supplied by a mask.
`SelfRead` now loads from actual intermediate upper target bits, proves agreement
with the frozen-source program, and preserves the exceptional set; `SourceBits`
identifies arbitrary ordered physical upper-bit sources. No copied source field is
assumed in this extension.

`Mask` and `MaskedSelfRead` now prove active-target semantics, source stability
including inactive digit low bits, global ideal involutivity and exceptional-set
preservation. `ReadOrdered.readOrdered_exec` supplies a fixed-program interpreter
of arbitrary ordered source indices with restored source/descriptor and exact cost
`n (6 W + 8) + 6`. `ReadOffset.readOffset_exec` adds compact spreading and cleanup
with cost at most `n (6 W + 10) + 8 n G + 16`; `readOffset_value` matches the modular
load's arithmetic value. These metadata costs still require explicit caller
amortization. `MaskedBits` now identifies physical masked sources, including inactive
low bits. `SourceCode.sourceCode_spec` binds the actual reader into the live-index
callback interface; `SourceRot.sourceRotate_exec` executes complete source-controlled
record rotations, charging both callback computations. `SourceRotAlgebra` matches
that executed rank map with the packed modular load/unload on every address.
`ReadPattern`, `PatternGate`, `PatternCode` and `PatternRot` now implement the
mixed AND/XOR callbacks with optional selectors for inactive zeros. Each callback
costs `L (12 W + 38) + 24`, including two interpreted reads and cleanup.
`SparsePattern` and `CompactPatterns` identify the actual descriptor outputs with
the masked A and YZ compact offsets. `SourceHeader` copies live field counters
into a metadata header with exact cost and complete register restoration;
`PatternOperands` permits callback execution on that header without changing the
physical field bank. `HeaderOperands` composes header construction, concrete
callback execution and cleanup with full stack restoration and explicit cost;
`HeaderValue` identifies contiguous copied counters with the actual index window.
`HeaderCode.headerCode_spec` now binds this to the actual counter bank and proves
that field increments preserve its invariant. Its callback cost is
`6 W + 6 count + 1 + L (12 W + 38) + 24 + 2 W + 2`.
`HeaderRot.headerRotate_exec` executes the full rotation with both callback costs.
`HeaderFields` supplies the complete higher-field suffix and automatic source-window
bounds, including gap/spectator fields. `PlainPatterns` and `HeaderOffsets` identify
A, Z, Y and YZ with the actual gadget field digits and load/unload with arbitrary
ordered current address bits.
`MaskedGadget` projects the actual masked early schedule to the existing `run_E`
proof without initializing the physical controls. `MaskedSlot` proves guard and
complete source-observation preservation, including prefix/suffix spectators and
inactive low bits. `MaskedSchedule`, `MaskedEndpoint` and `MaskedDynamic` prove the
full twelve-rotation/twelve-interchange instruction endpoint with actual intermediate
source reads. `SlotSources` decodes arbitrary ordered physical sources, including an
arbitrary-width outer spectator word. `SelectiveXor` proves the exact sparse physical
XOR; `SelectiveIndex.selectiveRunIdx_good` binds that endpoint to one unchanged
five-field physical layout and restores every borrowed/spectator field, including
all bits above the layout.
`SelectiveLayout` and `SelectivePatterns` now instantiate every header window and
source wire of that layout. `SelectiveRotations` binds all real rotation programs;
`SelectiveSwaps` binds both b/t and b/u host interchanges, including symbol/bit
conversions and supplier-exponent costs. `SelectivePrepared` retains one descriptor
bank per offset and two canonical interchange banks, so repeated passes require no
descriptor transitions. `SelectivePasses.selectivePrepared_exec` composes the actual
full host schedule, restores all prepared metadata, and charges the sum of every
pass cost. `selectiveProgramPerm_good` proves that same composed permutation has
the physical good-set endpoint. `selectiveCost_sum` checks four A rotations, two
of each other rotation, eight b/t swaps and four b/u swaps, plus the sequence's
terminal step.
The new metadata layer executes copies, zero-field construction and binary-to-unary
counter construction from raw configuration tapes. `SelectiveSetup` installs the
fixed 27-word bank and proves the complete prepared invariant. `MetadataClean`
clears the installed bank with an exact cost and restores its initially empty
registers. `SelectiveProgram.selectiveProgram_exec` joins setup, all passes and cleanup
with the physical good-set endpoint of the same executed permutation. Configuration inputs are restored, and the program shape
is independent of all numerical dimension annotations.

R1 is complete at its selective-primitive boundary. `SelectivePlacement` supplies
one fixed finite register allocation and proves both the host and setup separation
contracts. `SelectiveDensity` adapts the existing all-ones-window count to arbitrary
spectator widths, and instantiates logarithmic guards using the ceiling binary
logarithm of the scale. `SelectiveRouter.selectiveRouting_exec` combines that count
with the same physical permutation executed by the fully priced host program.
There are approximately **6.5k** routing Lean lines in total.

The [R1 completion audit](IntegerMultBounds/MathlibTM2/Routing/R1-AUDIT.md) records
requirements and theorem evidence. Raw configuration descriptors and canonical
header bits are inputs, with installation executed and charged; uniform generation
remains R3's obligation. Exact exceptional-record repair is provided by the
completed R2 below; complete routing and long/short-record amortization remain R3, and multiplication integration
remains R4. Completing R1 does not change the current multiplication kappa.

R2 is complete. `SelectiveIdeal` supplies the all-address physical XOR permutation
and bad-set invariance; `SelectiveRepairSpec` instantiates the existing exact
stable-sort repair identities. `BadClassifier` handles the actual five-field bank,
including zero suffix width. `SelectiveKeyPass` executes complete-rank keying,
including row bits, with full counter and scratch restoration. `RepairPlacement`
supplies the shared finite bank, and `RepairCore` composes the actual phases.

`RepairSetupBank`, `RepairSetupData`, `RepairSetupBlank` and `RepairSetup` install
all 34 metadata words from raw configuration, preserving inputs and constructing
all counters with charged programs. `RepairProgram` executes setup, the exact core
and final cleanup. `RepairDensity` bounds the actual exceptional-sort cost using
R1's physical bad count. `exactSelective_exec` in `ExactSelective.lean` combines the complete
execution with canonical headers and explicit ceiling-logarithm guards; it has no
prepared-state, classifier, key-emitter or placement oracle. The
[R2 audit](IntegerMultBounds/MathlibTM2/Routing/R2-AUDIT.md) records the acceptance
evidence. At the R2 checkpoint, the routing directory had approximately **9.2k** Lean lines, about
**2.7k** beyond the R1 checkpoint, reusing the existing scan and radix-sort programs.

R3 has a checked logical matching schedule. `ReservoirPartition` splits an
involution into three classes, each fixing its assigned reservoir; `MatchingShears`
realizes each class with three admissible XOR shears. `ReservoirSchedule` composes
the nine shears and proves their targets avoid the borrowed reservoir.
`ReservoirBudget` constructs three disjoint banks and proves their capacity when
`n ≥ 64G`. Its router parameters use `K = 64G`, rather than R2's minimal spacing;
the generic R2 execution theorem already supports this choice, and the existing
radix/density inequalities remain valid. This is a logical schedule, not yet an
executed router or a change to the multiplication bound.

`PermutationMatchings` now decomposes every finite coordinate permutation into
two computable involutions by reflecting each cycle around its least coordinate.
Orbit membership uses bounded traversal, and the terminating exponent search is
proved shorter than the coordinate count. `permutationReservoirSchedule_eq`
composes their eighteen directional shears into the exact address permutation.
This closes the logical decomposition; it does not price or execute generation.

R3's work is ordered by dependency (the first two logical items are now proved):

1. **Done, logical:** computable two-involution decomposition and composition with
   the reservoir-safe matching schedule.
2. **Done, logical profiles:** `ResidueShears` partitions a directional shear
   without changing its source observations. `SparseProfiles` enumerates exactly
   the targets with complete `K`-bit segments; `ProfileCompiler` proves their R2
   dimensions, target positions, active masks, source-descriptor validity and
   common borrowed-width bound. `TerminalShears` composes the bulk passes with at
   most `K` singleton XORs and proves no target is omitted.
   The elementary execution path is now proved: `LowBitXor` gives stable
   route/merge semantics; `ElementaryXorExec` executes two width-at-most-one bit
   exchanges around the scan. `ElementaryRouting` runs any instruction stream
   with one fixed program and tape bank, loading and clearing each six-word
   configuration and finally restoring the raw input. Its full bank changes only
   at the record stream, with explicit costs for every phase.
   `ElementaryInstructionSemantics` connects the executed rank permutation to
   the simultaneous terminal shear and bounds the shared-geometry instruction
   count by `131G`. `ElementaryLoopCost` proves a closed total bound, linear in
   call count times volume and restored-bank size, plus total configuration length;
   `RouterTerminalCost` specializes it to the shared terminal geometry when the
   address width fits the record width. `ElementarySharedSetup` executes both
   binary-to-unary counters, zero-field construction and first-mask copying,
   with exact cost and a dimension-independent program. It establishes the shared
   invariant from binary input tapes. `ElementarySharedRouting` composes actual
   shared setup, the elementary router and final shared cleanup, with a complete
   bank frame and all phases charged. `ElementaryHeaderExec` generates all five
   canonical headers on a fixed bank, with restored inputs/scratch and linear
   cost; `elementaryHeaderInstruction_valid` proves their actual loader contract.
   `ElementarySourceMask` generates the full-width renamed source mask from
   unary coordinate and padding tapes, with restored inputs and linear cost.
   `ElementaryInstructionWrite` serializes the exact six-word loader frame.
   `ElementaryCoordinates` constructs the complete coordinate/exponent bank
   from binary width, target and source, restoring inputs and scratch and
   charging all phases. `ElementaryCompiler` now composes coordinate, header and
   mask generation, exact frame serialization and private-bank cleanup: one fixed
   program emits a valid instruction from five binary inputs and restores every
   register except the output configuration stream. `ElementaryCompilerCost`
   bounds private cleanup by input sizes, completing the priced single-instruction
   compiler. `ElementaryCompileTableCost` proves a fixed loop compiles any framed
   coordinate table into valid instructions, restores the complete raw input and
   reusable bank, and bounds total time using pair count and input dimensions.
   `CompiledElementaryRouting` joins table compilation, actual routing and
   generated-instruction cleanup, restoring every register except the record
   stream, with all phases charged. `CompiledElementarySemantics` proves the exact
   simultaneous shear, spectator-row preservation and terminal table-count bound.
   `CompiledSharedRouting` joins actual shared-counter setup and final shared
   cleanup to that path, with closed setup/cleanup prices and a complete
   stream-only bank frame. `SharedInputExec` now generates the raw record count,
   unary address width and initial mask from binary dimensions, preserving inputs
   and scratch, for positive address width. `SharedInputProgram` proves executed
   preparation and cleanup around a restored stream-only router, charging both
   phases. `BinarySharedRouting` now composes actual generation, shared setup,
   coordinate-table compilation, routing and all cleanup, with a stream-only
   final frame and a closed total cost. It starts from binary dimensions and a
   raw coordinate table; coordinate-table generation and composition with the
   bulk router remain open. The zero-width fallback is still separate.
3. **Coordinate placement and prepared execution proved; setup open:** `BlockExchange` specifies
   equal-width interval interchanges, and `ReservoirPlacement` composes at most
   three of them to populate the physical `b,y,t,u` layout from the selected bank.
   `PlacementShear` transports both targets and source names and proves exact
   restoration after unplacing, including dirty reservoir bits.
   `BlockExchangeIndex` now identifies the host rank map with those coordinate
   exchanges. `BlockExchangeExec` supplies the actual uniform host call;
   `BlockExchangeChain` composes all calls with their full frame and summed cost.
   `reservoirPlacement_exec` executes both the concrete forward and reverse
   three-call schedules from initially prepared canonical header banks, with only
   the stream changed. `BinaryTripleScale` executes the general payload-header
   arithmetic (three times record width, shifted by the lower interval offset),
   clearing its intermediate word and restoring scratch with a linear cost bound.
   `ExchangeHeaderValues` proves the canonicality and exact host values of all
   five general interval-exchange headers. `ExchangeHeaderExec` now executes
   generation of the complete five-word bank from unary exponent tapes and
   binary row, block and interval-width inputs, preserving all inputs and scratch
   and charging the full cost. `InstalledBlockExchange` executes raw-header
   installation, the actual host interchange and installed-header cleanup,
   restoring every tape except the stream. Exact installation and cleanup prices
   are proved in total raw-header length. `GeneratedBlockExchange` now composes
   header generation, installation, the actual exchange and cleanup of both
   header banks, restoring every register except the stream. Its bound charges
   all phases. `MetadataBankCost` bounds installed size structurally, without
   expanding concrete banks; `GeneratedBlockExchangeCost` removes generated-word
   and installed-bank sizes from the execution bound, using only original bank
   size and input dimensions. `UnaryDifference3` executes both binary subtractions,
   unary conversion and cleanup of both intermediate words. `ExchangeExponents`
   now generates all three exponent tapes from binary width, interval offsets and
   interval width, with restored input/scratch and a total cost bound; its final
   cleanup restores the original bank and has an exact geometry-based price.
   `BinaryCanonicalCopy` constructs canonical bits while preserving the padded
   source. `ExchangeBinarySetup` composes exponent generation and canonical-width
   construction from four padded binary coordinates, restoring inputs and scratch;
   the generated bank has a complete cleanup frame and a dimension-only cleanup
   bound. `BinaryBlockExchange` now composes binary-only coordinate setup,
   canonical-width construction, header generation and installation, the actual
   exchange and all cleanup. Its total bound uses original input dimensions and
   borrowed-bank size, and every register except the stream is restored.
   `BinaryExchangeCall` packages the fixed layout and original binary-input
   invariant, proving readiness and cost survive stream changes.
   `BinaryExchangeChain` executes structural schedules without per-call execution
   premises. `BinaryReservoirPlacement` now executes the complete three-call
   forward and reverse placement schedules from binary coordinates, including
   all setup and cleanup, with only the stream changed. `BinaryExchangeLayoutCall`
   discharges every single-call layout/separation premise from a common role bank;
   `BinaryExchangeSlots` numbers it with 28 tapes beyond the host bank, sharing
   scratch between phases. `BinaryExchangeInput` constructs its input bank and
   proves readiness while preserving arbitrary permitted borrowed spectator
   words. `BinaryScheduleLayout` gives each stage three coordinate-input tapes
   while sharing all scratch, headers and host words; its explicit numbering uses
   only 34 tapes beyond the host bank for three calls. `BinaryScheduleCalls`
   derives simultaneous readiness from this one input bank. `CommonBankReservoir`
   now executes both placement directions from that concrete bank, with all
   generated metadata cleared and arbitrary permitted spectators restored.
   Its input assumptions are scoped to owned roles, permitting other phases'
   configuration tapes to coexist. `EmbedStream` lifts stream-only executions
   with identical time and exact outside-bank restoration;
   `ExactSelectiveEmbedded` applies it to the actual R2 program in any larger
   common bank. `RepairInputFrame` proves raw R2 configuration survives stream
   permutations. `SharedScheduleLayout` constructs disjoint core and placement
   banks sharing only the stream; `PlacementRepairLayout` instantiates it for R2.
   `SharedScheduleInput` overlays the two input banks and proves every core word
   and every placement input is retained, without assuming zero spectator words.
   The indexing proofs remain generic until the concrete R2 tape count is
   instantiated, avoiding costly count expansion. `RepairStreamFrame` proves
   stream permutations preserve required R2 scratch blankness.
   `PlacedExactSelective` now executes forward placement, the actual embedded R2
   program and reverse placement, derives all intermediate invariants, restores
   every tape except the stream and charges all three phases. It still assumes
   raw R2 configuration and initial binary-call readiness. `JointBankExactSelective`
   now instantiates the concrete joint-bank entry point, deriving every call
   invariant from the overlaid binary inputs. `SelectiveIdealBits` proves exact
   target XOR, unchanged other bits and outer-row preservation on every address;
   `PlacedSelectiveBits` transports target/spectator bits through coordinate
   conjugation and identifies the literal executed record output with that
   permutation. `SelectiveCoordinates` gives exact absolute target/source
   coordinates and proves allowed sources avoid active targets.
   `PlacedSelectiveCoordinates` transports source reads to original physical
   bits; `PlacedSelectiveShear` identifies the complete conjugated permutation
   with simultaneous shear, including the concrete reservoir-placement instance.
   Terminal-bank integration, uniform raw R2 input generation, full matching
   scheduling and long/short-record amortization remain required.
   `RouterGeometry` resolves the shared-width constraint using
   `d = (n-K)/(K+3G)`: all residues share borrowed width `dG`, the complete field
   bank has width exactly `n`, and the terminal suffix is shorter than `2K+3G`
   (hence `131G` at `K=64G`). Fixed-count profiles cover exactly the bulk region;
   the target-field-only profiles in item 2 remain reusable local lemmas.
4. Execute uniform generation of all raw R2 configuration words: source and mask
   descriptors, dimensions and canonical headers. Charge generation and cleanup;
   raw words cannot remain an unpriced input oracle. `ConfigurationWord`,
   `ConfigurationLoad` and `ConfigurationBatch` now execute framed raw-word
   loading and input archiving with unchanged left stacks; batch loading costs
   at most six times the framed input length plus one. The elementary path
   supplies an actual six-word loader, cleanup and fixed loop, not a per-call
   prepared-state or execution oracle. Producing those raw words and building
   the persistent counters are still required. `BinaryMask` now generates one
   full-width one-hot descriptor row from binary width and selector inputs,
   computing and clearing all unary coordinates and padding. `BinaryMaskEmit`
   prepends that row to an accumulating output and restores the reusable row
   bank, with a closed total cost. `DescriptorRows` identifies these generated
   rows with the actual source/pattern-table format, including the optional-zero
   selector. `DescriptorCompile` now executes a fixed loop over arbitrary framed
   binary selector tables, emits all rows in reverse selector order, restores
   the complete selector input and compiler scratch, and charges loading, row
   generation, loop tests and input restoration. `DescriptorTableCompile` proves
   that reversed selector frames produce source and optional-pattern tables in
   the interpreter’s exact order, with a bound in selector count and binary width.
   `DescriptorJob` and `DescriptorBatch` now compile fixed descriptor banks
   with shared scratch, restored selector inputs, initial-bank readiness only,
   a non-output frame and a sum of every compilation cost. `DescriptorBank`
   derives readiness from a concrete shared layout with two inputs per table and
   twelve shared compiler/archive tapes. `RepairDescriptorBank` instantiates all
   eleven actual R2 tables and raw configuration destinations.
   `RepairDescriptorContents` proves destination injectivity, the exact intended
   table at every output, and restoration of all auxiliary tapes.
   `RepairDescriptorFrame` covers every descriptor and preserves all other raw
   configuration. `RepairDescriptorData` removes all eleven initial descriptor
   assumptions and proves the generated bank satisfies the complete setup-data
   contract. `RepairDescriptorInstall` now composes actual eleven-table compilation
   with the complete metadata installer, derives its intermediate conditions and
   sums both costs. `DescriptorClean` and `RepairDescriptorClean` erase all
   generated tables after an arbitrary stream change, restore the initial bank
   elsewhere and charge an exact cost in table dimensions.
   `RepairDescriptorScratch` preserves every repair scratch and installed target;
   `ExactSelectiveDescriptor` now composes all eleven table compilations, actual
   exact repair and descriptor erasure with a complete nonstream frame and all
   phase costs included. `RepairConfigurationData` supplies one initial contract
   omitting all thirteen generated raw words and proves width generation followed
   by descriptor compilation establishes full setup data. `RepairConfigurationWidths`
   executes width generation inside the combined descriptor/width bank and proves
   its exact projection into the descriptor bank. `FieldPairClean` supplies
   reusable stream-preserving erasure for the two generated fields.
   `RepairConfigurationFrame` proves width generation preserves all descriptor
   inputs, repair scratch and installed targets, and establishes the next input
   contract without an intermediate oracle. `ExactSelectiveConfiguration` now
   executes both generators, actual exact repair and all generated-word cleanup
   in one forty-auxiliary-tape bank, restores every nonstream tape and charges
   every phase. `ExactSelectiveConfigurationEmbedded` lifts this complete program
   to larger banks at identical time; `ConfigurationPlacementLayout` supplies the
   concrete placement bank and structural separation of its nonstream tapes.
   `RepairConfigurationInputFrame` preserves the complete initial data contract
   under a stream update and proves all compiler inputs and scratch lie off-stream.
   `PlacedExactSelectiveConfiguration` now executes forward placement, both
   generators, exact repair, every cleanup phase and inverse placement, deriving
   all intermediate invariants and restoring all nonstream tapes with full costs.
   `JointBankExactSelectiveConfiguration` now derives all placement and compiler
   readiness from the concrete overlaid initial bank, with all thirteen generated
   raw destinations initially blank. Sparse selector generation, remaining masks/
   headers, full matching scheduling and final amortization remain required.
   `WordRepeat` now executes fixed archived-count block repetition, restores
   the full count input, source block and scratch, and charges iteration, tests
   and rewind. `WordRepeatValue` identifies emitted words with explicit shifted
   block sums; `RepeatedTemporaryMask` proves the actual temporary classifier
   mask has that repeated-block value. `RepeatedPhaseMask` proves the phase-mask
   analogue, including its final boundary bit. `BinaryTemporaryBlock` constructs
   the temporary-mask repeated block from binary segment/run dimensions, generates
   and clears unary padding, and restores all scratch with every phase charged.
   `BinaryWordRepeat` generates and clears a binary-specified repetition count;
   `BinaryTemporaryRepeat` composes binary block construction, repetition and
   generated-block erasure with an output-only frame and all costs charged.
   `WordRepeatNumeral` identifies repeated outputs as fitted arithmetic registers.
   `BinaryLowPad` executes a binary-specified low-zero offset shift and clears
   its generated unary exponent, preserving inputs and scratch. `BinaryHighPad`
   supplies binary-specified final padding. `BinaryTemporaryMask` now composes
   all phases to generate the actual full-width temporary classifier mask from
   binary dimensions, restoring every non-output tape and charging all work.
   `PhaseBlockCounts` executes three-mark phase-block construction from unary
   run/complementary widths, restoring both inputs and all scratch with exact
   cost. `PhaseMaskNumeral` identifies repeated blocks plus the final boundary
   mark and low shift with the exact phase-mask register, including fit bounds.
   `BinaryPhaseBlock` now generates both unary dimensions from binary widths,
   constructs the phase block and erases both counters. `BinaryPhaseRepeat`
   repeats and clears the generated block; `BinaryPhaseSeed` executes the final
   boundary mark even for a zero repetition count. `BinaryPhaseMask` composes
   these with binary low/high padding, producing the full-width phase classifier
   with all non-output tapes restored and a closed total cost. The combined
   exact-repair integration below starts with both raw mask destinations blank.
   `ClassifierPair` now executes both generators with shared dimensions, counters
   and scratch, changes exactly the two output tapes and charges both costs.
   `RepairPendingMaskData` omits the raw masks; `RepairClassifierPair` proves the
   generated bank establishes the existing configuration contract. Concrete bank
   placement is defined in `ClassifierBankLayout`: sixteen auxiliary tapes,
   existing core mask destinations and proved register separation.
   `ClassifierBankFrame` proves core projection and auxiliary preservation.
   `ClassifierClean` executes final mask erasure, preserving an arbitrary changed
   stream and restoring all other tapes with exact cost. `ClassifierBank` now
   executes generation on this concrete placement from six binary dimensions
   and ten blank workspace tapes. `ClassifierBankRepair` composes generation,
   any embedded core execution with a stream-only frame, and mask cleanup,
   proving complete restoration and summing all phase costs; the exact-repair
   instantiation is supplied below.
   `RepairClassifierFrame` proves preservation of all descriptor, width, blank,
   target and stream inputs. `ExactSelectiveGeneratedClassifiers` now executes
   actual exact repair from the generated classifier bank using the reduced
   initial contract, discharging every input-frame obligation. This starts after
   mask generation and charges repair only. `ExactSelectiveClassifiers` now joins
   concrete generation, actual exact repair and final mask erasure in one
   execution theorem. It starts with both masks blank, restores every nonstream
   tape and charges every phase. The phase-width guard follows from the actual
   routing parameters. The placement and concrete-bank integration below
   retain supplied sparse selectors and remaining binary/raw headers.
   `ClassifierPlacementLayout` now gives a shared placement/repair bank with
   disjoint classifier workspace; `RepairClassifierInputFrame` preserves the
   reduced configuration and binary dimensions under stream updates.
   `ExactSelectiveClassifiersEmbedded` lifts the complete generated-mask repair
   execution into any larger bank with the identical step count and nonstream
   frame. `ClassifierRepairExec` gives
   the verified complete program under named `classifierRepairProgram` and
   `classifierRepairPrice` interfaces. `PlacementAround` proves reusable
   forward-placement/core-permutation/inverse composition, retaining nonstream
   tapes and charging all three phases. `ClassifierRepairMoved` transfers every
   initial readiness fact across an arbitrary prior record permutation.
   `PlacedClassifierRepair` now instantiates actual forward placement, complete
   classifier-generated exact repair and inverse placement in any larger bank,
   restoring all nonstream tapes and charging every phase.
   `JointBankClassifierRepair` now derives all placement readiness from the
   concrete overlaid initial bank and executes the full placed repair program,
   with both generated classifier destinations initially blank. Binary sparse
   selector tables and remaining dimensions/headers are still supplied; full
   matching scheduling, terminal-table generation and final amortization remain
   required for R3. `CanonicalHeaderValue` proves uniqueness of canonical binary
   representations and identifies executed padded-word normalization with the
   exact `advance value []` list. `RoutingHeaderCopy` now generates any actual
   R2 canonical header from its live padded numerical operand, restoring all
   other tapes with exact linear cost. Generating those operands, executing the
   ten-header bank and integrating its cleanup remain open.
   `CanonicalHeaderJob` and `CanonicalHeaderBatch` now execute arbitrary fixed
   header lists with shared scratch, deriving all intermediate readiness from
   the initial bank. They prove exact summed costs, each destination's literal
   canonical contents, preservation off the destination set and header-length
   bounds for later erasure pricing. `HeaderBankLayout` and `HeaderBank` place
   arbitrary indexed header banks with one numeric source per output and two
   shared scratch tapes. `RepairHeaderBank` now executes all ten actual R2
   headers at their raw configuration destinations, proves distinct destinations
   and exact contents, and preserves the twelve auxiliary tapes. Numeric operand
   generation and integration into repair remain open. `CanonicalHeaderClean`
   now executes erasure of any generated header bank after a stream change,
   restores all other tapes and bounds erasure by the supplied widths. The next
   arithmetic bridge can reuse `ExchangeHeaderExec` for shifted row/payload,
   power and width headers, identifying its canonical outputs by value rather
   than generating those large words again. `ExchangeCanonicalHeaders` now
   identifies the existing arithmetic generator's output with exact canonical
   swap lists. `RepairExchangeHeaders` instantiates it for either R2 interchange,
   with all generation costs charged and every non-output tape restored. Its
   shift counts reduce to spectator width (plus counter width for the first
   swap) and address width (plus counter width for the second swap). Generating
   and erasing these unary counts, preparing canonical row/width sources and
   composing both banks with repair remain open. `RepairHeaderCounts` now
   executes both shift-count constructions from live field-width tapes, proves
   their exact R2 lengths and the same closed cost for either swap.
   `RepairHeaderCountsClean` erases both counts with exact cost and complete
   restoration. Their composition around arithmetic header generation, canonical
   row/width preparation and repair integration remain open.
   `RepairHeaderLayout` now shares count construction with the arithmetic
   generator's row/gap and scratch roles. `RepairHeaderCountFrame` proves
   canonical-header writes preserve every count/dimension tape and commute with
   count preparation, supplying the state equality needed for count cleanup.
   `RepairHeaderGenerate` now composes count construction, exact arithmetic
   header generation and count erasure, restoring every non-output tape with a
   closed total bound. `RepairHeaderSources` prepares canonical row/width tapes
   from live padded binary inputs, restoring both inputs and shared scratch.
   `RepairHeaderSourcesClean` erases those canonical sources with a width-based
   bound; `RepairHeaderSourceFrame` proves compatibility with header writes.
   `BinaryRepairHeaders` now joins source preparation, count/header generation,
   count cleanup and source erasure in one execution from live binary inputs,
   restoring every non-output tape and charging all phases.
   `BinaryRepairHeaderPair` now composes both swaps with reusable non-output
   scratch and a shared binary row/width source pair. It derives second-bank
   readiness from initial inputs, proves all ten final header contents and
   preservation of every unrelated tape, and charges both full costs. Concrete
   shared-bank placement is now proved by `SharedHeaderRoles` and
   `SharedHeaderBankLayout`: fifteen additional tapes, with all non-output roles
   shared. `RepairSharedHeaderLayout` maps dimensions, block input and outputs
   to actual raw repair configuration. `RepairSharedHeaders` executes both banks
   from binary inputs and blank workspace on this placement.
   `RepairPendingHeaderData` now omits all ten canonical headers from the initial
   repair configuration; `RepairHeaderData.generated` proves that the generated
   bank satisfies the existing mask-free contract. `RepairHeaderDataExec` links
   actual execution to that readiness result, deriving dimensions and block
   input/fit from the reduced data. Full exact-repair composition and final
   generated-header erasure remain required. `RepairHeaderFrame` now proves
   preservation of classifier, width and descriptor auxiliary tapes, installed
   targets, raw descriptors and extras, every blank repair register and the
   record stream. These facts discharge the readiness-transfer part of the
   pending exact-repair composition. `ClassifierRepairGeneratedHeaders` now
   invokes actual classifier-generated exact repair on the generated-header bank
   using initial data with all ten headers omitted. Every readiness obligation
   follows from the initial frame. This theorem begins after header generation
   and charges repair only. `RepairHeadersClean` now erases all ten headers
   after an arbitrary stream update with an exact price determined by canonical
   header lengths. `HeaderRepair` joins actual header generation, complete
   classifier-generated exact repair and final header erasure in one execution,
   restoring every nonstream tape and charging all phases. `HeaderRepairProgram`
   names this complete program and price. `HeaderPlacementLayout` separates its
   shared header workspace from placement metadata; `RepairHeaderInputFrame`
   preserves header-free inputs under stream changes. `HeaderRepairMoved` now
   executes the complete header-generating repair after any record permutation,
   deriving intermediate readiness and preserving the cost/restoration contract.
   `PlacedHeaderRepair` now composes actual forward placement, header-generating
   repair and inverse placement in an arbitrary larger bank, charging all phases
   and restoring every nonstream tape. `JointBankHeaderRepair` derives placement
   readiness from the concrete shared initial bank, with no supplied phase
   execution assumptions. Sparse selector generation, remaining raw dimensions
   and the full matching/amortization gates remain open.
   `GeneratedReadPattern` composes actual table generation, pattern interpretation
   and descriptor erasure; only the requested output changes, with all three
   phases charged. `BinaryFullMask` identifies unary conversion with the exact
   full-mask word used by R2, and `BinaryZeroField` generates a zero field from
   its binary width and clears the temporary unary counter. Both restore their
   inputs and scratch with closed costs. `BinaryFieldJob` and `BinaryFieldBatch`
   now execute fixed mixed banks of these generators with shared scratch, derive
   every intermediate readiness condition from the initial bank, preserve all
   non-output tapes, and sum every generation cost. `RepairWidthFields` now
   instantiates the row and full-key-mask generators at the actual raw R2
   configuration registers, using six additional tapes shared by both jobs.
   `RepairWidthData` removes these two words from the initial data contract and
   proves the literal generated bank satisfies the complete R2 setup-data contract
   when the remaining configuration is supplied. `RepairWidthInstall` now executes
   width generation followed by the complete metadata installer in the larger
   bank, derives its intermediate input and scratch conditions, and sums both
   costs. `RepairWidthFrame` preserves every exact-repair blank and installed
   destination; `RepairWidthClean` erases the two generated raw words after an
   arbitrary stream change, restores every other tape and charges the exact
   cleanup cost. `ExactSelectiveWidth` now composes generation, actual exact R2
   execution and generated-word cleanup, restores every tape except the stream,
   and includes all three phases in its bound. Generation of the remaining
   configuration remains required. `ExactSelectiveWidthEmbedded` preserves this
   execution and exact step count in an arbitrary larger bank. `WidthPlacementLayout`
   supplies the joint placement/generated-width bank and proves all six width
   tapes disjoint from placement. `PlacedExactSelectiveWidth` now executes forward
   placement, width generation, exact repair, raw-word cleanup and inverse
   placement, deriving all intermediate invariants and restoring every nonstream
   tape with all phase costs included. `JointBankExactSelectiveWidth` derives
   all placement readiness from the concrete overlaid initial bank and supplies
   the generated-width repair inputs from its core words. The remaining raw
   configuration generator is still required.
   `DescriptorSelectorFrames` now proves exact framed selector lengths, append
   composition and executed serialization from live binary source registers,
   with exact cost `rows * (6 * width + 7) + 1` and all source/scratch tapes
   restored. This supplies emission only; it does not generate coordinates or
   remove the supplied selector-table hypothesis. `SelectorGap` now executes
   a binary-sized run of absent selectors with a fixed repetition loop, preserving
   its binary count, reusable zero frame and scratch, with the complete repeat
   cost charged. `BinarySelectorZeroFrame` constructs the reusable frame from
   a binary width. `GeneratedSelectorGap` composes construction, binary-sized
   gap emission and frame erasure, changes only the accumulating output and
   charges all phases. `SelectorEntry` now emits a gap followed by a live binary
   selector, restoring both operands, the reusable frame and scratch, with the
   serialization and repetition costs charged. `SparseSelectorRuns` specifies
   compact gap/entry runs, proves exact dense/framed sizes and proves that reverse
   run traversal with prepending produces the forward dense selector stream.
   `SelectorRunLoad` now reads each compact binary gap/selector pair using
   fixed scanners, with exact cost `4 * gapWidth + 4 * selectorWidth + 12`,
   preserving all other tapes and archiving both complete frames for rewind.
   `SelectorRunStep` now composes actual pair loading, gap/live-entry emission
   and operand erasure in one fixed iteration. It charges every phase, archives
   consumed input and restores every tape except input/archive/output. Its frame
   lemmas reestablish the next iteration's scratch blanks. `SelectorRunLoopData`
   proves compact-stream and archive/output composition; `SelectorRunLoop` now
   executes arbitrary finite compact streams with one fixed loop and a summed
   per-entry cost. `SelectorRunCompile` adds the initial test and final archive
   rewind, restoring the complete input and every non-output tape. It still
   uses a supplied reusable zero frame. `GeneratedSelectorRuns` now generates
   that frame once from a live binary width, compiles the complete compact stream
   and erases the frame, restoring every non-output tape and charging all phases.
   `SparseSelectorCompress` proves compact runs cover arbitrary dense selector
   lists, including trailing gaps and all-zero tables, and bounds each gap by
   dense length. `GeneratedSelectorList` executes the exact dense list from its
   compact representation. This representation is still supplied input; generating
   it from actual sparse profile coordinates remains required.
   `CompactDescriptorCompile` now executes compact expansion, actual descriptor
   table compilation and dense-selector erasure, restoring every non-output tape
   with all phases charged. This removes prepared dense selector frames from
   that table-level execution contract, but still requires compact input.
   `SparseSelectorRun.compress_length_le` bounds compact entries by the number
   of nonzero reads plus one final zero entry, including all-zero tables.
   `CompactPatternTable` proves the executed optional-source table contract;
   `RepairCompactPattern` instantiates it for every actual repair descriptor,
   identifies its output with `repairDescriptorWord` and charges all phases.
   These per-table executions still require compact input and are not yet
   assembled into the concrete eleven-job shared bank. `CompactDescriptorJob`
   packages the complete initial readiness and alphabet-independent cost, and
   proves readiness survives other output writes. `CompactDescriptorBatch`
   executes any separated list of these jobs with shared workspace, derives
   every intermediate readiness condition from the original bank, restores all
   non-output tapes and sums the complete costs. The concrete eleven-job layout
   and its input-coordinate generator remain required. `CompactDescriptorLayout`
   now supplies three persistent inputs per job and one shared generation/compiler
   workspace, proving all register injections and separation from core outputs.
   `CompactDescriptorBank` derives every job's readiness from those concrete input
   words and shared blanks, and executes the complete finite bank with all costs
   summed. Specialization to the eleven repair jobs and input-coordinate
   generation remain required. `CompactDescriptorContents` now proves exact
   individual outputs and unchanged auxiliary tapes. `RepairCompactBank`
   instantiates the actual eleven repair jobs, executes the whole concrete bank
   from compact input words and shared blanks, and proves each output equals
   `repairDescriptorWord`. Connecting this bank to the header/placement repair
   execution and generating compact inputs from routing profiles remain open.
   `RepairCompactFrame` proves all descriptors are covered and every other raw
   input survives. `RepairCompactData` establishes the complete existing
   `RepairSetupData` from descriptor-free initial data. `RepairCompactInstall`
   executes compact compilation followed by the actual complete R2 installer,
   derives its intermediate readiness from the initial bank and sums both costs.
   Exact-repair execution, generated-descriptor cleanup and header/placement
   integration for this compact path remain required. `CompactDescriptorClean`
   and `RepairCompactClean` now erase generated tables after an arbitrary stream
   update, with exact cost and full restoration. `RepairCompactScratch` preserves
   all exact-repair scratch and installed destinations. `ExactSelectiveCompact`
   composes actual compact compilation, complete exact R2 execution and table
   erasure, restoring every nonstream tape and charging all phases. Width/mask
   and header/placement integration for this compact path remain required.
   `RepairCompactWidthData` now proves generated row/key-mask fields followed
   by compact compilation establish the full repair setup contract.
   `RepairCompactWidths` executes both width jobs inside the extended compact
   bank, with only those two outputs changed and all generation work charged.
   `RepairCompactWidthFrame` preserves compact inputs, installed destinations
   and exact-repair scratch. `ExactSelectiveCompactConfiguration` now composes
   width generation, actual compact exact repair and width cleanup, restoring
   every nonstream tape and charging all phases. Classifier-mask generation,
   header generation and placement integration for this compact path remain open.
   `RepairCompactInputFrame` supplies the compact core embeddings;
   `RepairCompactClassifierFrame` preserves compact inputs, width workspace,
   exact-repair scratch, installed targets and the stream under mask generation.
   `RepairCompactClassifierBank` connects the concrete sixteen-tape classifier
   workspace to the exact generated compact configuration bank. Composing actual
   classifier execution, compact repair and mask cleanup remains required.
   `ExactSelectiveCompactGeneratedClassifiers` now executes compact exact repair
   from the generated-mask bank, deriving every readiness condition from initial
   mask-free inputs. This theorem starts after mask generation and charges repair
   only. `ExactSelectiveCompactClassifiers` now composes actual binary-dimension
   mask generation, compact exact repair and final mask erasure, restoring every
   nonstream tape and charging the full execution. Header generation and
   forward/inverse placement integration for this compact path remain open.
   `RepairCompactHeaderLayout` and `RepairCompactSharedHeaders` now execute
   both header generators on the compact classifier bank with shared workspace.
   `RepairCompactHeaderData` and `RepairCompactHeaderDataExec` derive all
   dimensions/block readiness from header-free initial data and establish the
   complete mask-free input contract after generation, charging both swaps.
   `RepairCompactHeaderFrame` now preserves all compact input roles, classifier
   and width workspace, raw non-header inputs and repair scratch.
   `RepairCompactHeadersClean` erases all ten generated headers after an arbitrary
   stream update with exact canonical-length cost and complete restoration.
   `CompactConfigurationRepair` and `CompactClassifierRepair` name the complete
   compact repair programs and prices. `CompactClassifierRepairExec` verifies
   the named execution; `CompactClassifierRepairGeneratedHeaders` derives all
   repair readiness from the generated-header bank. `CompactHeaderRepairProgram`
   and `CompactHeaderRepair` now compose actual ten-header generation, compact
   classifier/width/descriptor repair and final header erasure, restoring every
   nonstream tape and charging all phases. Compact inputs and remaining raw
   dimensions are still supplied; placement integration remains open.
   `RepairCompactHeaderInputFrame` preserves header-free inputs under stream
   updates; `CompactHeaderPlacementLayout` separates placement from the complete
   compact header workspace. `CompactHeaderRepairMoved` now executes the full
   header-generating compact repair after any record permutation, deriving
   readiness from the original bank and preserving the complete cost/frame
   contract. `PlacedCompactHeaderRepair` now executes forward placement, full
   compact header-generating repair and inverse placement in an arbitrary larger
   bank. `JointBankCompactHeaderRepair` derives placement readiness from the
   concrete overlaid initial bank. Every phase is charged and every nonstream
   tape restored. Compact profile inputs and remaining scalar/dimension words
   are still supplied; profile generation, full matching/terminal scheduling and
   long/short-record amortization remain R3 gates. `SparseSelectorGaps` now
   identifies a whole zero interval with one compact gap update and proves
   exact live-entry and trailing-zero compression identities. These are
   specification lemmas for generating runs directly from sparse positions;
   no executed profile-coordinate generation is claimed. `SparseCoordinateEmit`
   now computes a compact gap by subtracting a live binary cursor from a live
   target, serializes that gap and a live selector, then clears the gap scratch.
   Its fixed program restores all inputs and scratch, changes only the compact
   output stream and has exact cost `16 * coordinateWidth + 6 * selectorWidth + 25`.
   Position traversal, cursor advancement and source-selector arithmetic remain
   required before this is a complete profile generator. `SparseCursorAdvance`
   now executes cursor replacement by the live target plus one, retaining target,
   reusable binary one and arithmetic scratch, with exact cost
   `10 * coordinateWidth + 10` under the explicit nonoverflow bound. Composition
   with pair emission and target traversal remains required. `SparseCoordinateStep`
   now composes computed gap/selector emission with cursor advancement, changing
   only cursor and compact output and restoring all other tapes. Its exact cost
   is `26 * coordinateWidth + 6 * selectorWidth + 35`. Loading and traversing
   successive targets and generating source-selector coordinates remain open.
   `SparseCoordinateCall` now executes one complete streamed iteration: load
   target/selector frames into an archive, compute and emit the compact gap,
   advance the cursor and erase loaded operands. Only input/archive, cursor
   and compact output change, with exact cost
   `32 * coordinateWidth + 12 * selectorWidth + 52`. The full traversal loop,
   final rewind/cursor restoration and source-coordinate generation remain open.
   `SparseCoordinateLoop` now traverses arbitrary ordered absolute-coordinate
   streams with one fixed program, derives each iteration's readiness and proves
   exact cost `entries * (32 * coordinateWidth + 12 * selectorWidth + 54) + 1`.
   Its trace bank records the executed archive/cursor/output updates; closed
   final-bank algebra, rewind and cursor restoration remain required.
   `SparseCoordinateFrame` now proves the trace has exhausted input, archived
   every original frame exactly in reverse, computed the explicit compact output,
   reached the final target-plus-one cursor and preserved every spectator tape.
   `SparseCoordinateCompile` now executes the initial test, full coordinate
   traversal and final input rewind. The complete input/archive and all spectator
   tapes are restored; only compact output and advanced cursor change. Its exact
   total cost includes every loop iteration and rewind symbol. Saving/restoring
   the original cursor and matching output to the compact compiler remain open.
   `SparseCursorRestore` now restores a saved forward cursor and erases its copy.
   `SparseCoordinateGenerate` composes cursor save, complete coordinate traversal,
   input rewind and cursor restoration, changing only the compact output with
   exact cost including every phase. Identifying this output with the compiler
   input, generating target/source coordinates for actual profiles and handling
   the terminal zero suffix remain required. `SparseCoordinateRuns` now proves
   generated coordinate output is exactly `selectorRunFrames` in reverse run
   order, has one compact entry per coordinate and satisfies compiler gap bounds
   from ordered-coordinate readiness. Executed generation/compiler composition
   and actual profile-coordinate correctness remain required.
   `SparseCoordinateCoverage` proves dense expansion covers exactly the interval
   from the initial cursor through the last target, including all gaps, and proves
   a final zero-selector coordinate closes a terminal suffix at the exact width.
   `CoordinateSelectorGenerate` now executes coordinate-to-compact generation,
   dense selector expansion and intermediate compact-stream erasure, restoring
   every non-output tape and charging all phases. Absolute coordinates are still
   supplied; actual profile lookup correctness, terminal suffix integration and
   descriptor compilation from these generated selector frames remain required.
   The next selector gates are:
   (a) execute a streaming gap/entry expander from sparse positions, generating
   the distinguished absent-source selector in gaps and charging every output;
   (b) generate each actual offset's source coordinates from live dimensions and
   sparse profile data, including inactive slots, repeated reads and spectator
   sources; (c) identify reverse emitted order with `repairDescriptorIndices`
   for all eleven jobs and derive their width inputs; (d) compose generation,
   descriptor compilation, repair and selector cleanup in the shared bank.
   The expander must use a fixed loop, not unroll the profile in program code.
   Generating selector tables from sparse profiles and the complete R2
   configuration compiler remain open.
   `SparsePatternCoordinates` represents sparse patterns by mirrored absolute
   coordinates, proving strict order and exact target/zero-gap lookup against
   reversed descriptor indices. `SparsePatternReadiness` derives all traversal
   readiness from strict position order, bounds and one binary width bound.
   This covers inactive zero entries and repeated sources; terminal suffix
   completion and actual repair-pattern instantiation remain required, along
   with executed generation of the absolute-coordinate input itself.
   `SparseCoordinateTerminal` conditionally adds one final zero-selector entry,
   proves no duplicate target is introduced, preserves order and bounds, derives
   traversal readiness and proves the final cursor equals the exact requested
   dense width. It adds at most one entry. Pattern lookup preservation through
   this completion and actual repair-pattern instantiation remain required.
   `SparsePatternComplete` now proves terminal-completed mirrored sparse
   coordinates expand to the exact reversed pattern-index list.
   `RepairKeyCoordinates` instantiates this for the actual key-source descriptor,
   deriving ordered traversal readiness and exact selector equality. Remaining
   rotation patterns and executed generation of these coordinate words remain
   required; no free coordinate-input oracle is discharged by these lemmas.
   `RepairRotationCoordinates` now supplies the actual sparse position/source
   formulas for all ten rotation descriptors, proves equality with existing R2
   patterns, exact reversed descriptor indices, traversal readiness and a bound
   of sparse slot count plus one terminal entry. Together with the key result,
   all eleven descriptor coordinate specifications are covered. Executed
   coordinate-word generation and shared-bank execution integration remain open.
   `RepairDescriptorCoordinates` unifies all eleven coordinate specifications,
   proving traversal readiness, sparse entry-count bounds and exact final table
   equality with `repairDescriptorWord` over any alphabet. Machine generation of
   the coordinate words and integration into the shared repair bank remain open.
   `SparseSourceCoordinateEmit` now generates a mirrored target and present
   source-selector frame directly from live binary position/source operands,
   computing selector `wire + 1`, erasing temporaries and restoring every input.
   Its exact cost is `16 * coordinateWidth + 16 * selectorWidth + 35`.
   Absent-source handling, generating positions/source operands from dimensions
   and profiles, and repeated coordinate-frame emission remain required.
   `SparseAbsentCoordinateEmit` now generates mirrored-target frames with a
   zero selector from a live operand's width, restoring all inputs/scratch and
   charging exactly `16 * coordinateWidth + 12 * selectorWidth + 31` steps.
   Both present and absent source arithmetic are executed; live activity
   selection, operand generation and repeated profile emission remain open.
   `SparseOptionalCoordinateEmit` now reads a live activity bit without consuming
   it and executes present-source or absent-source coordinate emission through
   one fixed conditional program. Only the coordinate output changes; its bound
   includes the test, branch and all arithmetic/cleanup. Operand generation and
   repeated profile emission remain required.
   `BinaryAffinePosition` now executes offset-plus-index-times-stride from live
   binary operands, reuses multiplication scratch for addition, erases the
   product and restores every non-output tape under an explicit nonoverflow
   bound. This supplies the arithmetic for selected/control slot positions;
   profile iteration and quotient/remainder positions remain required.
   `AffineSourceCoordinate` now composes actual affine slot generation,
   mirrored present-source emission and position cleanup, restoring every input
   and scratch tape with the full cost charged. No prepared position/selector
   word is supplied. Activity selection for this combined path and repeated
   profile iteration remain required; temporary-bit positions still require
   their group/within-group arithmetic.
   `AffineOptionalCoordinate` now combines affine position generation with a
   live activity test, emitting either a computed source selector or zero and
   erasing the generated position. All inputs and scratch are restored, and the
   bound charges arithmetic, branching and cleanup. Repeated profile execution
   and group/within-group temporary positions remain open.
   `RepairCoordinateDescriptor` now executes the coordinate compiler for any
   of the eleven actual descriptors, deriving readiness and the exact output
   word from the profile specification. Its dense compilation cost uses the
   actual row count; compact/dense intermediates are erased and only descriptor
   output changes. Coordinate frames are still supplied: repeated profile
   generation and shared-bank composition remain required.
   `AffineProfileCall`, `AffineProfileLoop`, `AffineProfileFrame`,
   `AffineProfileCompile` and `AffineProfileGenerate` now execute a fixed loop
   over live activity/source frames, generate each affine position from an
   internal index, archive and restore the complete profile, restore the index
   and erase all temporary operands. Only coordinate output changes, with every
   phase charged. `AffineProfileCoordinates` and `AffineSourceProfileGenerate`
   identify that output with the sparse-pattern coordinate specification and
   derive recursive readiness from dimension/source bounds.
   `AffineProfileComplete` and `RepairAffineProfileGenerate` specialize this
   execution to the six Y/YZ/X descriptors for positive slot counts: their first
   physical slot is zero, so the generated coordinates already contain the
   required mirrored terminal entry. `SparseTerminalCoordinateEmit` separately
   constructs and erases position zero to emit an absent terminal frame from
   live widths. `AffineProfileTerminal` now executes terminal emission followed
   by full live-profile generation for strictly positive physical positions,
   including empty profiles with positive target width. It proves the complete
   output word and restores all non-output tapes, charging both phases.
   `BinaryZeroTest` and `AffineProfileClosedGenerate` now use live tests of the
   offset and profile to choose terminal completion in one fixed program. This
   covers zero offsets, positive offsets and empty profiles whenever target width
   is positive, restores every non-output tape and charges all tests/branches.
   `RepairKeyProfileGenerate` and `RepairZProfileGenerate` now cover any reservoir
   offset; their earlier positive-offset restriction is removed.
   `AffineProfileDescriptor` composes this generator with actual coordinate,
   compact-selector and dense-descriptor compilation, then erases the generated
   absolute-coordinate stream. Its exact output is the sparse pattern's table;
   only descriptor output changes, with setup, tests, compilation and cleanup
   charged. `RepairAffinePattern` and `RepairAffineDescriptor` instantiate this
   path for all nine non-A repair descriptors, deriving slot bounds and exact
   descriptor words from the actual repair formulas. No coordinate/descriptor
   input is supplied to this path. Zero-width cases, both temporary-bit A
   descriptors, shared-bank execution, and source-profile/scalar-dimension
   generation remain open; full R3 and kappa are unchanged.
   `BinaryGroupedPosition` now executes the temporary-slot arithmetic
   `floor(index / group) * stride + index % group + base` from live binary
   dimensions. It reuses the existing bounded `bdivmod`, widens the remainder,
   composes affine arithmetic and erases quotient/remainder/offset scratch; only
   the generated position changes. Its cost is quadratic in binary widths, as
   is the existing affine multiplication path, so no new division algorithm or
   nested group-counter implementation is required for this setup path.
   `GroupedOptionalCoordinate` composes this arithmetic with live activity/source
   selection and erases the generated position. `GroupedProfileCall` and
   `GroupedProfileLoop` load activity/source frames, compute each grouped position
   from the internal counter, emit coordinates, erase loaded operands and advance
   the counter through one fixed loop. `GroupedProfileFrame` proves exact emitted
   coordinates, complete archived input, final counter and unchanged spectators.
   `GroupedProfileCompile` and `GroupedProfileGenerate` now rewind the entire
   grouped profile archive, restore the initial index and erase its saved copy;
   only generated coordinate output changes. `GroupedProfileCoordinates` and
   `GroupedSourceProfileGenerate` identify that output with the mirrored sparse
   coordinates and derive traversal readiness from source/dimension bounds.
   `GroupedProfileTerminal` composes this execution with generated terminal-zero
   emission, restoring all non-output tapes. `RepairAProfileGenerate` instantiates
   both actual A profiles and proves the exact completed coordinate streams.
   `RepairADescriptor` composes their generation with actual descriptor compilation
   and erases all coordinate, compact and dense intermediates, charging each phase.
   All eleven individual descriptor pipelines now have executed live-profile
   contracts for positive target widths. Zero-width branching, source-profile and
   scalar generation, shared-bank composition and the remaining R3 gates stay open;
   full R3 and kappa are unchanged.
   `RepairDescriptorGuard` proves that a zero-row actual descriptor word is empty
   and executes a live binary row-count test. Empty tables take a no-output branch;
   the positive branch invokes a proved backend contract from the unchanged tape
   bank. The test/branch cost is charged and backend scratch readiness survives.
   This guard is now instantiated with the concrete shared layout and all eleven
   live backends by `LiveDescriptorExec`; empty and positive tables share one path.
   `ProfileSharedRegisters` now embeds all affine-profile register roles into
   the grouped engine's roles, proving injectivity and their common output tape.
   `LiveDescriptorLayout` provides per-job source/dimension/row-count tapes and
   shared profile, coordinate and compiler workspaces, with fixed symbolic aliases
   independent of dimension values. Core outputs are disjoint from every auxiliary
   tape. `LiveDescriptorSeparation` proves the concrete compiler alias/separation
   conditions and that arbitrary core-output writes preserve every auxiliary value.
   `LiveDescriptorMode`, `LiveDescriptorData` and `LiveDescriptorWorkspace` now
   specify one concrete auxiliary bank with uniform binary widths, prove it is
   inhabited over any core bank, and derive all per-job compiler/scratch readiness.
   Core-output writes preserve the full readiness contract. `LiveAffineDescriptor`
   and `LiveGroupedDescriptor` instantiate the actual backends from that bank;
   `LiveDescriptorExec` adds the live empty-row guard without execution premises.
   `LiveDescriptorBatch` proves sequential job execution and exact outputs while
   carrying readiness across every write. `RepairLiveDescriptorBank` instantiates
   all eleven actual jobs, and `RepairLiveDescriptorData` establishes the existing
   full R2 setup-data contract from their generated tables. `LiveDescriptorClean`
   and `RepairLiveDescriptorScratch` charge erasure and restore blank descriptor
   destinations while retaining an arbitrary disjoint stream change.
   `ExactSelectiveLive` now composes the full live-profile batch, embedded exact
   R2 and descriptor cleanup: only the repaired record stream changes, and every
   compilation/installation/repair/cleanup phase is charged. It still starts from
   supplied scalar/profile inputs and the pending-descriptor canonical-header
   contract. Executed input generation, integration with generated headers and
   placement, uniform setup/amortization bounds, and all remaining R3 gates remain
   open; full R3 and kappa are unchanged.
   `EmbeddedRepairHeaders`, `EmbeddedRepairHeaderData` and
   `EmbeddedRepairHeaderClean` now reuse the existing executed header generator
   over any injectively embedded repair core, transport all non-header pending
   descriptor data and erase the ten generated headers with their exact price.
   `RepairLiveHeaderFrame` proves that these writes preserve the full live-bank
   readiness, descriptors, repair targets, scratch and record stream.
   `LiveHeaderRepairGenerated` executes exact live repair on that generated bank;
   `LiveHeaderRepair` composes actual header generation, all eleven live descriptor
   compilers, exact R2 and complete generated-table cleanup. Its initial ten header
   tapes are blank, every phase is charged, and only the repaired stream changes.
   The composed proof uses explicit header-map types and the proved embedded-user
   projection, preserving default elaboration limits and a narrow import closure.
   Canonical headers are no longer supplied on this path. Scalar/profile inputs,
   classifier masks and width fields remain supplied; their executed generation,
   uniform setup bounds and all remaining R3 gates are open.
   `LiveHeaderInputFrame` and `LiveHeaderRepairMoved` transport the initial live
   inputs across a record permutation. `PlacedLiveHeaderRepair` composes executed
   forward reservoir placement, generated-header live repair and inverse placement
   in a larger bank, charging both exchange chains and restoring every non-stream
   tape. `LiveHeaderPlacementLayout` separates placement metadata from the whole
   inner bank, including header workspace. `JointBankLiveHeaderRepair` derives
   exchange readiness from concrete shared-bank words, so the composition no longer
   assumes ready exchange calls. Placement metadata words and live scalar/profile
   inputs remain supplied; their generation, routing schedules and uniform
   setup/amortization bounds remain open.
   `LiveHeaderWidths` now executes row-zero and key-mask field generation from
   binary width operands in an outer six-tape workspace. `LiveHeaderWidthFrame`
   proves preservation of every live descriptor input, header work tape, repair
   target, descriptor destination and blank register, and derives the pending
   descriptor contract from pending configuration. `LiveWidthRepairGenerated`
   connects that generated bank to the full header/live-descriptor repair proof.
   `LiveWidthRepair` executes width generation, full live repair and width cleanup:
   the two raw field tapes initially are blank, all phases are charged, and only
   the record stream changes. Binary width operands and classifier/profile inputs
   remain supplied. Composition of this outer width workspace with placement,
   classifier generation, remaining input generation and uniform cost bounds
   remain open; full R3 and kappa are unchanged.
   `LiveHeaderConfigurationFrame`, `LiveClassifierFrame` and `LiveClassifierBank`
   now supply a concrete classifier workspace around the live width/header bank.
   Executed classifier writes preserve live-profile readiness, header workspace,
   width operands, repair scratch and descriptor/installation destinations.
   `LiveClassifierRepairGenerated` derives the complete width/header/live repair
   contract from pending mask data. `LiveClassifierRepair` composes the existing
   binary classifier generators, the full live repair path and classifier cleanup:
   both classifier output tapes initially are blank, every phase is charged and
   only the stream changes. Classifier masks and raw row/key-mask fields no longer
   need to be supplied on this composed path. Binary scalar/profile inputs remain
   supplied; placement integration of this enlarged bank and uniform total-cost
   bounds remain open. R3 and kappa are unchanged.
   `LiveClassifierRepairMoved` now transports the entire generated-input path
   across record placement, preserving pending mask data, live-profile readiness,
   width and classifier operands, header workspace and every blank destination.
   `PlacedLiveClassifierRepair` composes actual forward reservoir placement,
   classifier/width/header/descriptor generation, exact repair, cleanup and inverse
   placement in an arbitrary larger bank. Both exchange chains and every inner
   phase are charged; every non-stream tape is restored. A concrete joint-bank
   readiness wrapper for this enlarged workspace remains to be supplied, along
   with source/scalar generation, routing schedules and uniform total-cost bounds.
   `LiveClassifierPlacementLayout` now separates the full enlarged repair bank
   from placement metadata, sharing only the stream. `JointBankLiveClassifierRepair`
   derives actual exchange calls and readiness from concrete shared-bank words
   and executes forward placement, the full generated-input live repair and inverse
   placement. Ready exchange calls are no longer an input to this concrete path;
   every phase is charged and all non-stream tapes are restored. Placement words,
   binary scalar operands and source profiles remain supplied. Their executed
   generation, complete routing schedules and uniform setup/amortization bounds
   remain open; full R3 and kappa are unchanged.
   `LiveDescriptorCanonicalWidths` chooses logarithmic common widths from a
   finite maximum of the live descriptor scalars and proves all seven fit
   conditions for every job, including empty families and zero dimensions.
   Its canonical-bank readiness theorem has no separate numeric-fit assumptions.
   This fixes mathematical width selection only; executing the scalar/profile
   input generation and proving its uniform cost remain open.
   `BinaryInactiveProfileFrame` generates an inactive frame from a binary
   selector-width operand. `BinaryInactiveProfile` generates its temporary frame,
   repeats it a binary-specified number of times and erases the template, restoring
   every tape except the profile output and charging every phase.
   `RepairInactiveProfileGenerate` identifies this output with the exact second-pass
   Z, Y and X source-profile inputs. Those three profiles can therefore be produced
   without supplied profile words. Installing this generator in the live batch,
   generating active/selected profiles and the remaining scalar operands remain
   open; full R3 and kappa are unchanged.
   `LiveInactiveProfileLayout` gives a fixed seven-tape extension sharing the
   live bank's selector-width operand and one profile destination. Its core,
   count and scratch separation is proved structurally. `LiveInactiveProfile`
   executes the inactive generator directly into a blank live input and proves
   full `LiveDescriptorReady` from the other initial live inputs. The count and
   six outer work tapes are preserved; no generated profile word is supplied.
   This closes single-profile installation; batching the three inactive jobs,
   composing generation/descriptor execution/cleanup, and generating the remaining
   active/selected profiles and scalars remain open.
   `LiveInactiveProfileBatch` executes any distinct inactive-job list with one
   binary count and shared workspace, derives all later readiness from initial
   inputs, and proves the final live-bank contract. `RepairLiveInactiveProfiles`
   specializes this to actual jobs 4, 6 and 10 (second-pass Z, Y and X), with all
   three profile tapes initially blank. It preserves raw repair configuration and
   outer count/scratch. `LiveInactiveProfileClean` erases the generated profiles
   after any disjoint stream update, restores the original bank and gives the
   closed cleanup cost. Composition with executed descriptor/repair programs,
   active/selected profile generation and remaining scalar generation stay open.
   `InactiveProfileRepairGenerated` now executes the actual live descriptor batch
   and exact repair on the generated three-profile bank, deriving configuration,
   scratch and descriptor readiness from the original bank.
   `InactiveProfileRepair` composes executed three-profile generation, the embedded
   full live repair program and profile erasure. All three profile inputs initially
   are blank; generation, descriptor/repair execution and cleanup are charged,
   and only the repaired stream changes. Canonical headers and row/classifier
   fields are still supplied on this particular seam; combining its seven-tape
   extension with the generated-header/classifier placement path remains open,
   together with active/selected profile generation, scalar generation and the
   uniform total-cost/amortization gates. Full R3 and kappa are unchanged.
   `InactiveProfileHeaderFrame` now embeds the inactive-profile bank under the
   executed header generator and proves preservation of all live auxiliary inputs
   and the seven profile-generation tapes. `InactiveProfileHeaderGenerated`
   derives the full inactive-profile/repair contract after header generation.
   `InactiveProfileHeaderRepair` composes actual header generation, three-profile
   generation, descriptor compilation, exact R2, profile cleanup and header cleanup.
   Headers and all three inactive profile tapes initially are blank, every phase
   is charged and only the record stream changes. Explicit header-map interfaces
   and a structural intermediate-state rewrite keep default elaboration limits.
   Classifier/width generation and placement integration around this enlarged
   bank, active/selected profiles, remaining scalars and total-cost bounds remain
   open; full R3 and kappa are unchanged.
   `EmbeddedRepairWidths` now reuses row/key-mask generation over any injectively
   embedded repair core and derives pending descriptor data from pending
   configuration. `InactiveProfileWidths` specializes its frame to the enlarged
   header/inactive-profile bank, preserving live inputs, profile count/workspace
   and header operands. `InactiveWidthRepairGenerated` derives the complete
   header/profile repair contract on that generated-width bank.
   `InactiveWidthRepair` composes actual width, header and three-profile generation,
   descriptor compilation, exact R2 and all corresponding cleanup. Raw row/key-mask
   fields, headers and the three inactive profiles initially are blank; only the
   repaired stream changes and every phase is charged. Classifier generation and
   placement around this enlarged bank, active/selected profiles, remaining scalars
   and uniform total-cost/amortization bounds remain open; R3 and kappa are unchanged.
   `InactiveClassifierFrame` and `InactiveClassifierBank` now extend the enlarged
   inactive-profile/header/width bank with executed classifier generation, proving
   all live, profile, header and width inputs survive the mask writes.
   `InactiveClassifierRepairGenerated` derives the complete repair contract on
   that generated-mask bank from pending mask data. `InactiveClassifierRepair`
   composes actual classifier, width, header and three-profile generation, full
   descriptor/repair execution and every cleanup phase. All those generated inputs
   initially are blank; every phase is charged and only the stream changes.
   Placement integration around this enlarged bank, active/selected profile and
   remaining scalar generation, routing schedules and uniform total-cost bounds
   remain open; full R3 and kappa are unchanged.
   `InactiveClassifierRepairMoved` transports every input and readiness condition
   across record placement through all four bank layers. `PlacedInactiveClassifierRepair`
   composes actual forward placement, classifier/width/header/inactive-profile
   generation, exact descriptor/repair execution, all cleanup and inverse placement.
   `InactiveClassifierPlacementLayout` separates the enlarged bank from placement
   metadata. `JointBankInactiveClassifierRepair` derives exchange calls and readiness
   from concrete shared-bank words, without supplied ready calls. Every phase is
   charged and all non-stream tapes are restored. Placement words, binary scalar
   operands and the remaining active/selected profiles still are supplied; their
   generation, full routing schedules and uniform total-cost/amortization bounds
   remain open. R3 and kappa are unchanged.
   `BinaryActiveProfileFrame` emits an enabled frame from a live binary selector,
   restoring its operand and copy scratch. `AffineSourceFrame` computes that
   selector from live index/stride/offset operands, emits the frame and erases the
   computed selector. `AffineSourceStep` adds the internal index advance; each
   primitive has an explicit execution cost and spectator frame.
   `RepairYSourceProfile` identifies the actual first-pass Y input with this
   affine counter stream, independently of activity/source choices. The counted
   generator still needs its loop, frame-order correction (stack prepending
   reverses successive frames), index/count restoration and live-bank installation.
   Activity-dependent and selected-source profiles and the remaining R3 gates
   remain open; full R3 and kappa are unchanged.
   `AffineSourceReverseStep` now emits each computed frame through a temporary
   tape into a reversed accumulator while advancing the index and restoring the
   frame tape. `AffineSourceLoop` executes a fixed loop over count symbols, archives
   them for restoration and computes every selector from live operands. Its cost
   is bounded per iteration. `AffineSourceLoopFrame` proves the exact accumulated
   output is the reverse of the specified affine source-profile word and preserves
   every spectator tape. Final reversal, count/index restoration, binary-count
   setup, width adaptation and live-bank installation remain to close the generator.
   Full R3 and kappa remain unchanged.
   `AffineSourceTrace` now proves the complete closed bank after traversal:
   empty count, reversed count archive, advanced index, reversed profile and
   unchanged spectators. `AffineSourceCompile` restores the count and reverses
   the accumulator into the correctly ordered output. `AffineSourceGenerate`
   saves and restores the original index as well: only the profile output changes,
   every temporary tape is restored, and all costs are charged. This generates
   affine source frames from a count tape and scalar operands without a supplied
   profile. Binary-count setup, selector-width adaptation and live-bank installation
   remain open, as do activity-dependent/selected profiles and the other R3 gates.
   Full R3 and kappa remain unchanged.
   `BinaryAffineSourceGenerate` now generates and erases its unary count from a
   binary operand, restoring the binary dimensions, index and complete workspace.
   `RepairYSourceGenerate` instantiates this with the actual first-pass Y selectors
   and discharges their arithmetic range using the proved target-wire bounds.
   The exact Y profile is generated without supplied profile/unary-count words;
   only its output changes and every phase is charged. Selector-width adaptation
   and installation into the live bank remain open, along with activity-dependent
   and selected-source profiles, remaining scalars and all other R3 cost gates.
   Full R3 and kappa are unchanged.
   `LiveDescriptorArithmeticWidths` now chooses compatible logarithmic widths
   with selector width equal to arithmetic width and proves every fit condition,
   avoiding a separate profile-width conversion pass. `LiveYSourceLayout` borrows
   existing live arithmetic scratch, the key job's K/rho operands and the same
   seven outer profile tapes. `LiveYSourceGenerate` executes the actual first Y
   generator directly into live input 5 from a blank tape, restoring every borrowed
   tape and scalar operand, and supplies the resulting `LiveDescriptorReady`
   contract. Joint sequencing with the three inactive profiles, full repair/cleanup
   integration and the other active/selected profiles remain open, along with
   scalar generation and the uniform R3 cost gates. Full R3 and kappa are unchanged.
   `LiveProfileBatchFrame` composes partial profile-bank contracts independently
   of profile contents. `RepairLiveGeneratedProfiles` sequences the three inactive
   generators and actual Y generator using the same seven outer tapes, with all
   four profile inputs initially blank and full live readiness derived afterward.
   `RepairGeneratedProfileClean` proves exact restoration after disjoint stream
   updates and the closed four-profile cleanup cost.
   `GeneratedProfilesRepairGenerated` derives the existing exact-repair inputs
   from that generated bank. `GeneratedProfilesRepair` executes four-profile
   generation, all eleven descriptor compilers, exact R2 and complete cleanup:
   no four-profile words are supplied, every phase is charged and only the stream
   changes. `GeneratedProfilesHeaderGenerated` and `GeneratedProfilesHeaderRepair`
   add actual header generation and erasure, using the existing embedded header
   frame. `GeneratedProfilesWidthGenerated` and `GeneratedProfilesWidthRepair`
   further generate and erase the raw row/key-mask fields. The full composed path
   starts with those fields, headers and all four profile inputs blank and restores
   every tape except the repaired stream. `GeneratedProfilesClassifierGenerated`
   and `GeneratedProfilesClassifierRepair` add executed classifier generation and
   cleanup. `GeneratedProfilesClassifierMoved` transports all readiness across
   stream placement; `PlacedGeneratedProfilesRepair` composes both exchange chains
   with the full generated-input path. `JointBankGeneratedProfilesRepair` derives
   exchange readiness from actual shared-bank words using the existing layout.
   Classifiers, raw width fields, headers and four profiles now start blank in
   this placed composition, with every phase charged and all non-stream tapes
   restored. The other seven active/selected profiles, remaining scalar/placement
   setup, complete routing schedules and uniform R3 cost/amortization gates remain open.
   Full R3 and kappa are unchanged.
   `OptionalAffineSourceGenerate` now executes activity-gated affine source
   generation directly from raw activity bits and binary operands. Its loop
   archives and restores the activity tape, advances inactive slots, reverses
   the profile accumulator and restores the original index; only the profile
   output changes, with explicit execution costs. `RepairZSourceProfile` and
   `RepairZSourceGenerate` identify and execute the actual first Z profile.
   `LiveZSourceLayout` and `LiveZSourceGenerate` reuse existing bank operands and
   outer scratch, reading activity from a restored core tape. The raw activity
   word is still a caller input. `RepairLiveActivityProfiles` generates five
   initially blank profiles in one bank; `ActivityProfilesRepair` composes these
   with all descriptor compilers, exact repair and five-profile cleanup, charging
   every phase and restoring all non-stream tapes. `ActivityProfilesHeaderRepair`,
   `ActivityProfilesWidthRepair` and `ActivityProfilesClassifierRepair` now add
   executed header, row/key-mask and classifier generation with full cleanup.
   `ActivityProfilesClassifierMoved` transports all readiness, including the
   activity tape, across stream placement. `PlacedActivityProfilesRepair` and
   `JointBankActivityProfilesRepair` compose both exchange chains and derive
   readiness from actual shared-bank words. The activity tape must be disjoint
   from the stream and generated raw fields. All five profile inputs, headers,
   raw width fields and classifiers start blank in this path; every phase is
   charged and every non-stream tape is restored. Six other source profiles, raw activity
   production, scalar/placement setup, complete routing schedules and uniform
   cost/amortization gates remain open. Full R3 and kappa are unchanged.
   `RepairYZSourceProfile` identifies both YZ source streams: the target stream
   reuses the first-Y selector sequence, while the control stream is affine and
   activity-gated. `LiveYZControlOffset` computes its base from the existing
   target/control row counts; `LiveYZControlSourceCompile` generates the profile
   and erases that temporary base. Both YZ generators restore every borrowed tape.
   `LiveYZSourceBatch` and `RepairLiveYZProfiles` generate seven initially blank
   profile inputs in the same workspace, deriving full descriptor readiness.
   `YZProfilesRepair` executes exact repair and seven-profile cleanup with a
   combined cost bound. The header/width/classifier wrappers and
   `JointBankYZProfilesRepair` carry all seven through actual shared-bank forward
   placement, repair, cleanup and inverse placement, restoring all non-stream
   tapes and charging every phase. The key, both A and first X source profiles
   remain supplied, as do raw activity, scalar and placement inputs. Complete
   routing schedules, uniform setup/amortization and the executed short-record
   fallback remain open. Full R3 and kappa are unchanged.
   `CounterSourceStep` through `BinaryCounterSourceGenerate` directly enumerate
   consecutive selectors by copying and incrementing a binary counter, avoiding
   affine multiplication and constant-operand setup. Count, index and scratch
   are fully restored; per-selector work is linear in the selector width.
   `RepairATemporarySourceGenerate` identifies this stream with the second A
   profile. `LiveATemporarySourceGenerate` uses the existing full-width zero
   cursor and control-row count, with no added scalar input.
   `RepairLiveTemporaryProfiles` generates eight initially blank profiles.
   `RepairTemporaryProfileClean` charges the longer A profile separately;
   `JointBankTemporaryProfilesRepair` carries all eight through generated
   classifiers/widths/headers, both placement exchanges, exact repair and cleanup.
   Every phase is charged and all non-stream tapes are restored. The key,
   first A and first X source profiles remain supplied. Raw activity/scalars,
   placement-input production, full routing schedules, uniform setup/amortization
   and the executed short-record fallback remain open. Full R3 and kappa are unchanged.
   `RepairAControlSourceProfile` identifies the first A stream as one
   activity-gated control selector repeated for each temporary wire in its group.
   `OptionalAffineSourceGroupGenerate` computes each selector once, repeats its
   frame using the live binary group count, archives/restores raw activity and
   restores the original index and all scratch. `LiveAControlSourceGenerate`
   installs this actual profile using the existing group-size operand and seven
   outer tapes. `RepairLiveControlProfiles` now generates nine initially blank
   source profiles in one bank. `RepairControlProfileClean` separately charges
   both longer A profiles; `JointBankControlProfilesRepair` composes all nine with
   executed classifier/width/header generation, exact repair, both shared-bank
   placement exchanges and complete cleanup. Every phase is charged and every
   non-stream tape restored. Only key and first X source profiles remain supplied;
   raw activity/scalars, placement inputs, full routing schedules, uniform setup
   and amortization and the executed short-record fallback remain open.
   Full R3 and kappa are unchanged.
   `LiveSelectedXSourceGenerate` and `LiveSelectedKeySourceGenerate` now execute
   the two remaining individual profiles on the concrete shared bank. Their fixed
   interpreters read raw region tags and local coordinates, compute physical wire
   addresses, and gate key frames by activity; they restore the complete raw input
   and every non-output tape with explicit total step bounds. The layout reuses
   existing zero/rho/stride operands and blank arithmetic scratch. `LiveSourceBases`
   now computes the other two region bases from the existing
   live count, stride, rho and Y/control row counts. `LivePreparedXSourceGenerate`
   and `LivePreparedKeySourceGenerate` compose this setup, actual profile generation
   and complete base cleanup, restoring every tape except the profile output and
   charging all phases. `RepairAllSourceProfiles` now executes all eleven
   profile generators in one shared bank, including region-base setup and cleanup,
   with a summed step bound and every non-profile tape restored. It establishes
   descriptor readiness without any supplied completed profile. `AllSourceProfilesRepair` composes
   this eleven-profile generation with exact repair and complete profile cleanup:
   only the repaired stream changes and every phase is charged.
   `JointBankAllSourceProfilesRepair` now composes executed classifiers, widths,
   headers, all eleven profile generators, exact repair, forward/inverse placement,
   and complete cleanup. Placement readiness is derived from the concrete
   shared-bank words; every phase is charged and every non-stream tape restored.
   Canonical raw source records, scalars and placement words remain
   inputs. `RepairRawSourceLayout` identifies six unused physical key-field
   aliases as concrete raw-input storage, proving separation from all setup
   sources/targets, the main stream and required blank scratch. Their input
   production, complete routing schedules, and all remaining
   routing/amortization/fallback gates remain open. `SharedSelectedSourceGenerate`
   now emits the X profile from the same activity-bearing raw format used for
   keys, archiving the activity bit without gating the X frame. This shared format
   is installed throughout the concrete placed-repair path; `liveSharedSourceProfiles_exec`
   explicitly runs both profile generators sequentially on one restored raw tape.
   `SourceActivityGenerate` now extracts the activity word from canonical records
   and restores the entire input. `RepairSourceRecordProfiles` installs it in the
   live bank, runs all eleven profiles from that same raw stream, and clears the
   temporary activity tape with every phase charged. `SourceRecordProfilesRepair`
   composes this with exact repair and profile cleanup, requiring one canonical
   source stream and no supplied activity. The concrete placed path now uses
   this stronger contract throughout classifiers, widths, headers, all profiles,
   exact repair and both placement exchanges. Its activity tape starts and ends
   blank; every phase is charged and all non-stream tapes restore.
   Schedule-to-record production, scalar/placement setup, full schedules and
   uniform cost/amortization/fallback gates remain open. Full R3 and kappa are unchanged.
   `SourceCoordinateRecord` now converts one live physical Y coordinate and
   activity bit into exactly the canonical record of `sourceOfY`. A fixed program
   executes low/high boundary comparisons, quotient/remainder decoding for digit
   sources, numeric width conversion, tag and record writing, and full scratch
   cleanup. Only the record destination changes; the total cost is explicit.
   `ProfileSourceRecords` identifies the canonical record stream for a logical
   bulk profile and proves exact source-coordinate reconstruction and length.
   Full source-stream loading/compilation, caller-derived coordinates/activity,
   scalar/placement setup and the remaining schedule/amortization/fallback gates
   remain open. These single-record theorems do not complete R3 or change kappa.
   `SourceCoordinateGenerate` now scans a framed coordinate/activity stream,
   compiles every record with the fixed decoder, archives and restores the entire
   original input, and returns canonical records in forward order. All setup and
   scratch tapes restore; only the final output changes, with an explicit summed
   cost. `ProfileCoordinateGenerate` specializes this execution to the logical
   bulk profile and proves its output is exactly `profileSourceRecords`.
   Concrete live-bank installation/composition, production of physical coordinates
   and activity from the matching/reservoir schedule, scalar/placement setup and
   uniform full-router cost/amortization/fallback gates remain open. R3 and kappa
   are unchanged.
   `LivePreparedCoordinateSourceGenerate` now installs physical-coordinate
   stream compilation in the existing live bank, including boundary generation
   and cleanup. `LiveCoordinateProfiles` composes it with all eleven profile
   generators, activity extraction and erasure of the intermediate canonical
   source stream. `CoordinateProfilesRepair` executes exact repair and profile
   cleanup on this output: only the repaired stream changes, with every phase
   charged. Its input is a framed physical-coordinate/activity stream, rather
   than predecoded source records. `JointBankAllSourceProfilesRepair` now
   threads this stronger input through executed headers, widths, classifiers,
   forward placement, exact repair and inverse placement, deriving all intermediate
   readiness and restoring every non-stream tape. Matching-derived input
   production, remaining scalar
   setup and full-router cost/amortization/fallback gates remain open. R3 and
   kappa are unchanged.
   The full placed-repair composition now has a geometry-independent theorem,
   `jointBankAllSourceProfilesRepairOfGeometry_exec`. Its chain generates source
   profiles, headers, widths and classifiers, executes placement and exact repair,
   and restores every non-stream tape, under explicit guards and density bounds.
   Existing spacing-specific theorems instantiate the generic chain. Reservoir
   spacing is instantiated by `reservoirAllSourceProfilesRepair_exec`, using
   `routerParameters_guards` and `routerParameters_radices`; bridge lemmas also
   establish these guards for `routerProfileParameters`. Complete scheduling,
   input production, uniform amortization and short-record fallback remain open.
   `RouterProfileSchedule` connects the common-width geometry to the logical
   schedule: residue-profile targets are exactly their bulk congruence classes,
   and all residue shears followed by the elementary suffix equal the requested
   shear. It reuses `RouterTerminal`’s suffix bound (fewer than `131 * G` calls
   under reservoir spacing). These are logical coverage and call-count results;
   executed composition and matching-derived input production remain open.
   `ProfileIdealShear` identifies the all-address exact-repair destination map
   with the logical shear on selected profile targets, including exceptional
   addresses and arbitrary initial borrowed fields. `profileIdealPerm_shear`
   states this directly for the finite rank permutation used by execution;
   `routerProfilePassTargets` identifies its selected targets with one bulk
   residue class. Matching-derived input production and executed schedule
   composition still remain open.
   `RouterProfileRank` transports targets and source coordinates into each residue
   geometry and proves source allowance from the global target-set condition.
   Every residue's exact rank map acts on the same physical target-field bits;
   their structural composition performs the complete bulk shear and preserves
   every borrowed/spectator bit outside that field. These are destination-map
   composition results, not yet a uniform tape loop or a total-cost bound.
   `ShiftedElementarySchedule` places the existing elementary rank permutations
   directly above the common low borrowed field; it proves the exact local
   shear, low-bit restoration and unchanged upper rows. `RouterDirectionalRank`
   composes terminal and bulk maps into the full requested shear, with restored
   low/high borrowed fields and spectators, a finite bound and an involutive
   `routerDirectionalPerm`. This closes the directional destination-map
   composition, not the executed uniform tape schedule or its cost bound.
   Uniform call loading has begun. `DelimitedConfigurationLoad` generalizes the
   existing loader to a caller-chosen frame delimiter, allowing ordinary binary
   separators inside metadata words; the old loader instantiates this theorem.
   `DelimitedBankLoad` executes a fixed destination bank from successive frames,
   sharing one scanner and archive with exact linear costs. Its code depends
   only on the fixed destination list. `DelimitedBankTrace` proves exact frame
   lengths, loading cost, complete rewind archive and spectator preservation.
   `DelimitedBankReady` identifies every loaded word, the advanced input cursor
   and restored scratch; clearing the metadata bank restores every other register.
   `DelimitedBankCall` executes load/call/cleanup around a supplied stream-only
   call theorem, with overhead at most six times the frame length plus twice
   the destination count plus two.
   `DelimitedCallLoop` and `DelimitedScheduleExec` execute a fixed call loop,
   sum all stage costs and restore the complete metadata input from its archive.
   `DelimitedBankSchedule` instantiates this with actual bank loading, stream-only
   calls and cleanup on one fixed destination list. The final state changes only
   the routed stream, independently of the number of calls. Generated/placed
   readiness/invariant instantiation and matching-derived metadata production
   remain open; the generic loop does not yet close R3 or its total-cost gates.
   `RepairFramedConfig` identifies the fixed 34-source raw R2 bank and derives
   `RepairSetupData` from actual loaded words. `RepairConfigLoaderLayout` places
   input, scanner scratch and archive in three unused key-field aliases, with
   no new tapes, preserving every repair target, required blank and stream.
   `FramedExactSelective` executes actual density-priced exact repair between
   loading and raw-bank erasure, deriving its readiness rather than assuming
   an execution callback. The raw configuration words remain supplied; lifting
   the complete generated/placed pipeline remains open, along with metadata
   production and full-router amortization. Repeated raw-R2 calls are composed
   below.
   `RepairPriceFrame` proves the exact-repair price is determined by raw source
   words under the required blank-scratch invariant, independently of current
   record order and unrelated loader tapes. `RepairScheduleReady` supplies the
   concrete between-call invariant: raw inputs, installed targets, scratch and
   left stacks are restored, and arbitrary rank permutations preserve the fixed
   record count, width and symbol bounds. These feed the concrete repeated
   schedule below.
   `RepairScheduleStage` packages actual R2 data with variable geometry and a
   common record count/width. `RepairScheduleStep` discharges the fixed loop's
   execution, price and invariant premises using real framed exact repair.
   `FramedRepairSchedule` now executes arbitrarily many such concrete calls on
   one fixed bank, sums every stage price and rewinds the complete input; only
   the routed stream changes. Its stream effect is the composed finite rank
   permutation. Raw configuration words remain supplied. This completes repeated
   raw-R2 scheduling, while generated/placed-call scheduling, matching-derived
   metadata production and full-router amortization/fallback remain open.
   Generated/placed-call loading now has a whole-bank boundary.
   `FramedCoreBank` serializes every non-stream core register, including empty
   scratch, with a destination list independent of word values. `FramedCoreLayout`
   executes that loader using three fixed auxiliary tapes outside the core;
   their number is independent of geometry and call count. Its exact embedded
   stack identity retains the live record stream and supplies every other raw
   core word, allowing generated-call readiness to be transported together.
   Its single-call execution and price instantiation follows below; composing
   the repeated generated schedule remains open.
   `FramedCoreCall` now executes full-core loading, an embedded stream-only core
   execution and full raw-bank erasure with linear framing overhead. It uses
   the whole-stack identity to transport the existing core theorem and preserves
   all outer tapes except the input cursor/archive and routed stream. The core
   execution theorem is still a premise of this adapter; instantiation with
   generated/placed repair and stream-independent generated prices remain open.
   `repairRawPrice_updateStream` supplies the exact-R2 price frame needed by that
   next price proof.
   `LiveDescriptorBankFrame` and `LiveProfileBankFrame` prove descriptor/profile
   generation commutes with record-stream updates. `LiveRepairPriceFrame` factors
   live-profile repair through the raw-R2 price and proves its stream invariance;
   `LiveHeaderPriceFrame` extends this through executed header-bank generation.
   These price results retain the actual blank-scratch premises. Their outer
   classifier/width/placement extension follows below; concrete generated-call
   loading instantiation remains open.
   `GeneratedRepairBankFrame` names the actual classifier/width/header/profile
   preparation stages, proves their stream-update commutation and transports
   blank-scratch readiness from the original bank. `GeneratedRepairPriceFrame`
   gives the complete generated-core budget, including every generation and
   cleanup term, and proves stream invariance. `GeneratedPlacedPriceFrame` joins
   it to both executed-placement budgets and proves the full price is unchanged
   by updates to either physical or projected stream. This supplies a fixed
   per-stage price. Its actual framed execution is instantiated below; the
   repeated generated schedule remains open.
   `JointBankAllSourceProfilesPriced` now applies the actual generated/placed
   execution theorem with its complete fixed price evaluated before forward
   placement; the price comparison uses an isolated preparation-bank identity
   to avoid deep expansion in the execution context. `FramedGeneratedPlacedRepair`
   discharges the whole-core loader's execution premise with that theorem. It
   executes metadata loading, coordinate-driven profiles, classifiers, widths,
   headers, forward placement, exact repair, inverse placement and raw-bank
   erasure on a fixed core plus three shared loader tapes. No execution callback
   is assumed. The encoded coordinate/scalar/placement input bank remains supplied;
   repeated generated-call scheduling, matching-derived input production and
   full-router amortization remain open. The uniform code identity follows below.
   `BinaryExchangeFixedProgram` and `BinaryScheduleFixedProgram` erase all
   geometry, row-count and binary-width annotations from placement code;
   `FieldPairFixedProgram` does the same for generated widths.
   `GeneratedPlacedFixedProgram` proves the entire placed pipeline is one
   `allSourcePlacedFixedProgram`, depending only on fixed registers, alphabet,
   control-state bounds and procedure embedding. `FramedGeneratedPlacedRepair`
   now states actual execution of that same program for every stage. This closes
   uniform single-call code and pricing; repeated generated-call readiness and
   composition, input production and global cost/fallback gates remain open.
   `FramedCoreMetadata` proves the encoded full-core bank is unchanged by stream
   updates and has a nonempty destination bank when the core has at least two
   registers. `FramedCoreReady` provides the concrete between-call invariant:
   all non-stream core tapes and shared scanner scratch are restored, left
   stacks stay blank, and record permutations preserve count/width/symbol bounds.
   `GeneratedPlacedInput` packages the actual placed-call data and readiness
   equations without any execution fields; its execution theorem derives the
   fixed-program run from the existing concrete proof. `GeneratedPlacedInputTransport`
   now transports every readiness fact to arbitrary replacement records of the
   same count, width and symbol bounds, while preserving geometry and code. Its
   metadata theorem proves the encoded full-core jobs are identical after this
   replacement; `sharedScheduleInputBank_updateStream` preserves placement inputs.
   `GeneratedPlacedInputSemantics` identifies the actual call with its placed
   finite rank permutation and proves its full price is unchanged by replacing
   records or external input/output cursors. Its `exec_on` theorem runs the
   packaged call on the scheduler's current bank. `GeneratedPlacedInputFramed`
   supplies actual framed loading, generated/placed execution and erasure for
   arbitrary current records of the same shape, charging the fixed stage price
   plus framing overhead. `GeneratedRepairScheduleStage` now discharges the
   concrete step and between-call invariant for a common record count/width.
   `FramedGeneratedRepairSchedule` executes arbitrarily many generated/placed
   calls with varying geometry on one fixed bank and program, sums their actual
   fixed prices and framing overhead, and charges the final complete input rewind.
   Only the composed finite-rank stream effect remains; all other tapes are
   restored. Per-stage premises contain pure program identities and supplied
   readiness data, never execution callbacks. Matching-derived coordinate/scalar/
   placement input production, complete bulk/terminal/shear schedule instantiation
   and uniform global amortization/fallback remain open. Full R3 and kappa are
   unchanged.
   `MatchingProfileInputs` now identifies both matching directions' profile input
   with a comparison of each target and its mate, selecting the mate when active
   and the target itself otherwise. Fixed points are inactive and both directions
   satisfy source preservation. `MatchingCoordinateDispatch` executes this
   comparison; `MatchingCoordinateEmit.matchingCoordinateInput_exec` selects and
   emits the exact physical-coordinate/activity frame from two live binary
   endpoints in at most `14 * (Li + Lk) + 16` steps. Only output changes; all
   endpoint and workspace tapes restore. `MatchingCoordinateStep`,
   `MatchingCoordinateLoop` and `MatchingCoordinateTrace` now scan arbitrary
   bounded endpoint-entry lists with fixed code, archive the full input, restore
   endpoint and shared scratch tapes, and accumulate the exact reversed output.
   `MatchingCoordinateGenerate` rewinds the complete entry table and emits
   forward-order physical-coordinate/activity frames; its bound includes every
   comparison, load, copy, cleanup and final move. `MatchingProfileGenerate`
   specializes this to the exact profile input consumed by generated repair,
   with sources and activity derived from matching endpoints. Endpoint entries
   are still supplied in profile order for that specialization. `ResidueDispatch`
   now executes division, residue comparison and full arithmetic cleanup.
   `ResidueEntryEmit`, `ResidueEntryStep`, `ResidueEntryLoop` and
   `ResidueEntryTrace` filter an arbitrary common endpoint table by its live
   target-coordinate residue, with exact stable-filter output and full input
   archive. `ResidueEntryGenerate` restores the common table and every workspace
   tape and emits the selected entry stream, charging division, copying,
   scanning and both final moves. The common-table-to-router-profile order
   identity is now proved by `ResidueEntryOrder`: stable filtering enumerates
   `rho + c*K` in increasing profile order. `MatchingProfileGather` identifies
   the actual gathered stream with `matchingProfileEntries` for every profile
   with `rho < K`. `MatchingProfileProduction` composes gathering, physical-source/
   activity generation and gathered-table erasure from the common bulk endpoint
   table, restoring every tape except the exact profile input and charging all
   three phases. `BinaryPrefixExtract` now builds a unary traversal count
   from a live binary length, copies an arbitrary prefix and erases that count,
   preserving source and scratch. `MatchingTablePrefix` proves the full table
   splits at the exact bulk-entry boundary and executes extraction with its
   complete binary-count/copy/cleanup price. The binary byte-count scalar is
   still supplied. `MatchingFullProfileProduction` now composes extraction,
   residue gathering, coordinate/activity generation and both temporary-table
   erasures directly from the full matching table. Only the exact profile-input
   output changes. `RouterMatchingTable` proves that every router residue uses
   identical full-table values and an identical setup budget; local matching
   orientation agrees with the global direction after coordinate casts.
   `MatchingProductionCost` gives the exact polynomial and the uniform bound
   `160 * (digits * stride + digits + 1) * (s + 1)^2` when all binary widths
   are at most `s`. This includes executed count construction and all cleanup.
   `GeneratedPlacedCoordinateInput` identifies the exact coordinate tape through
   every core embedding and proves installing it completes the declared bank.
   `MatchingProductionSetup` packages only pure layout/readiness facts; its
   execution theorem invokes actual full-table production.
   `MatchingGeneratedPlacedRepair` now produces that initially blank coordinate
   tape, runs the complete generated/placed core, and erases the coordinate
   input afterward. Only the rank-permuted record stream changes; production,
   core and final erasure are all charged. `MatchingProductionLayout` provides
   36 fixed external production tapes with the required sharing and separation,
   independent of geometry and call count. `MatchingProductionBank` declares
   this workspace with just four external inputs: byte count, full matching
   table, stride and residue. `MatchingFixedSetup` derives every producer
   readiness fact from those contents. `MatchingFixedPlacedRepair` now executes
   the actual matching-produced generated/placed call on that concrete bank.
   `MatchingPlacedFrame` proves record replacement preserves the fixed code,
   total price and encoded non-stream metadata; only the physical stream word
   changes. `MatchingPlacedCurrent` runs the concrete call on arbitrary current
   records at its original price. `MatchingPlacedFramed` loads matching-table/
   scalar metadata, executes actual input production and the generated/placed
   core, and erases the loaded bank. `MatchingRepairScheduleStage` derives the
   between-call invariant. `FramedMatchingRepairSchedule` now executes any
   finite sequence on one fixed extended core plus three loader tapes, composes
   its rank permutations, sums all stage/framing costs and charges complete
   metadata rewind. Only the routed stream changes; no execution callback is
   assumed. Remaining scalar/placement production, initial matching-table
   production/accounting, full bulk/terminal/18-shear schedule instantiation
   and uniform full-router amortization/fallback remain open.
   `MiddleMatching` now restricts a physical matching fixing the surrounding
   fields to an explicit involution on the middle field, using coordinate
   subtraction. `MiddleMatchingShears` proves its three lifted shears give
   the complete physical matching after placement is undone.
   `ReservoirMiddleMatching` discharges the outside-field fixing premise for
   actual reservoir placement and every reservoir class, and identifies the
   restricted source with its original physical mate. This bridges reservoir
   class semantics to middle-field matching; executed table transformation and
   concrete profile/terminal schedule instantiation remain open.
   `BinaryCoordinateTranslate` executes interval-base translation with restored
   arithmetic scratch. `BinaryBlockCoordinateLayout.binaryBlockCoordinate_exec`
   reuses the region dispatcher and that translation to compute the literal
   `blockExchange` on a live binary coordinate, preserving every tape except
   its output, in at most `50 * width + 54` steps. This is scalar metadata
   transformation, not record routing or complete matching-table conversion.
   `MatchingLookupCall` executes query equality and conditional mate copying.
   `MatchingTableLookup` now instantiates the existing framed bank scheduler
   directly on the common matching-table encoding, derives unique-row output,
   and restores the entire table, query and workspace. Its complete bound is
   `coordinateCount * (30 * width + 39) + 4` steps, including loading, cleanup
   and rewind. No new scanner-loop or archive engine is used.
   `matchingTableLookupInPlace_exec` installs the looked-up mate into the
   query register and erases its temporary output, at an additional
   `10 * width + 10` steps. It shares `coordinateReplace_exec` with the
   in-place block exchange, avoiding duplicate bit-order and cleanup proofs.
   `BinaryCoordinateSchedule` reuses that same scheduler to compose live
   scalar block exchanges, restoring its complete metadata input and scratch.
   `ReservoirCoordinateExec` specializes it to forward and inverse reservoir
   placement in at most `276 * width + 328` steps. The forward scalar order
   is the reverse of the record-routing order. In-place binary updates use
   preserving copy and erasure, since a direct stack move reverses the bits.
   The restriction lemmas also expose the scalar lookup/subtraction formula
   and prove that inverse placement keeps each mate inside the middle field.
   `ReservoirMatchingLookup` now executes forward coordinate placement,
   in-place lookup in the physical table and inverse coordinate placement.
   Only its coordinate register changes, to the conjugated physical mate;
   both schedule inputs, the entire physical table and all scratch restore.
   Its full bound is `n * (30 * width + 39) + 562 * width + 670`.
   The two placement schedules may use separate metadata tapes while sharing
   the coordinate register.
   `ReservoirMiddleLookup` adds both executed middle-offset translations on a
   fixed 33-tape bank, deriving every readiness fact from that bank. Its only
   matching input is the physical table; the coordinate becomes exactly
   `reservoirMiddleMatching q`, with every other tape restored, within
   `n * (30 * width + 39) + 618 * width + 726` steps. The closed program also
   embeds into a larger bank with arbitrary spectator tapes, without an
   execution callback.
   `ReservoirMiddleEntry` saves and restores the query, serializes its local
   mate with the existing configuration writer, and emits a reversed row.
   `ReservoirMiddleTableScan` instantiates the existing bank scheduler on
   consecutive-selector frames, rewinds the complete selector input and
   reverses the accumulator once. Its full-selector theorem emits exactly
   the common local matching-table encoding, with bound
   `(n - 3*w) * (n * (30*width + 39) + 662*width + 799) + 6`.
   The selector format is proved equal to `counterSourceWord width 0 (n-3*w)`.
   `ReservoirMiddleTableProduction` now generates that input from a live
   binary middle width, using `toUnary` and the existing counter producer;
   it executes the full scan and erases selectors and the unary count.
   Its fixed 44-tape bank restores every tape except the local table output,
   including the physical matching table, binary count and zero index.
   Its complete bound is
   `(n - 3*w) * (n * (30*width + 39) + 682*width + 842) + 35*width + 46`.
   Placement metadata and the binary middle width are still supplied live
   operands.
   `ReservoirClassDispatch` now classifies both live endpoints against `3*H`
   and `6*H`, proving its first-available choice equals `reservoirChoice`.
   `ReservoirClassEntry` serializes the original mate or the fixed coordinate
   accordingly. `ReservoirClassTableProduction` reuses the framed scheduler
   to transform the original physical table into the exact common encoding
   of any chosen `matchingClass`, restoring the original table and scratch,
   within `n * (68*width + 85) + 6` steps. This transformation is pointwise
   and needs no involutivity premise.
   `ReservoirClassLocalTable` now composes both producers on one fixed
   57-tape bank. Its only matching input is the original physical table;
   it generates a chosen class, converts it into the exact local matching
   encoding and erases the intermediate class table. Only the local table
   output changes. Its full bound is
   `(n-3*w) * (n*(30*width+39) + 682*width+842) + n*(72*width+89) + 35*width+54`.
   The resulting `reservoirClassLocalMatching` is proved involutive.
   `OriginalMatchingPlacedRepair` now connects the executed table producer
   directly to one complete generated/placed repair. An explicit width equality
   and coordinate cast identify its source with the generated local matching;
   the source table starts blank and is erased again after repair. Only the
   rank-permuted record stream changes, with producer, repair and table erasure
   all charged. `OriginalMatchingRepairBank` gives a concrete layout sharing
   only this table register, and `OriginalMatchingFixedRepair` derives both
   readiness contracts from one bank on the placed core plus 93 tapes.
   `OriginalMatchingRepairCurrent` proves record replacement preserves the
   original-matching program, full stage price and every nonstream bank field.
   `FramedOriginalMatchingSchedule` now repeats actual calls for a fixed
   original matching, reservoir class and direction on one shared bank.
   Each stage generates and erases its class/local tables; the existing
   framed loop charges all loading, cleanup and complete metadata rewind.
   Its result is the composed finite record action, and its hypotheses are
   pure stage facts and code identities, with no execution callback. Tape
   count and stream definitions keep expanded layout abbreviations out of
   the scheduler interface; proof limits remain unchanged.
   `ProfilePlacedMatching` now identifies the selected physical coordinates
   with the placed image of `profilePassTargets`; for actual router parameters
   these are exactly one bulk residue, and the full record width is `n` when
   `X = 0`. Its source intertwining theorem connects local table coordinates
   to original physical class mates. `OriginalMatchingRepairBits` applies this
   to the actual `GeneratedPlacedInput.perm`: the rank action is the intended
   physical class shear, with all unselected bits fixed. This requires explicit
   alignment of placement slot width with `p.wc`, the middle-field width with
   `recordWidth - 3*p.wc`, and the source with the generated local class.
   Source-table agreement alone does not discharge these geometry conditions.
   Concrete input construction has now started: `CanonicalRepairInput` builds
   the raw bank from scalar dimensions and records, derives
   `RepairPendingMaskData`, and proves installed destinations, descriptors
   and required scratch are empty. Concrete profile registers use the key
   and bad-classifier state tapes plus the empty spectator-width input when
   `X = 0`; installing the source-coordinate word preserves all setup and
   scratch facts. `CanonicalLiveInput` extends that core through the actual
   descriptor layout, supplies scalar operands and the count, and keeps all
   eleven profile streams empty. `CanonicalOuterInput` constructs the header,
   width and classifier extensions with exact stack projections and blank
   scratch. `CanonicalPlacementInput` constructs the final shared placement
   bank with an empty legacy swap bank and preserves the complete core stack.
   `CanonicalGeneratedInput` now constructs a complete `GeneratedPlacedInput`
   from arithmetic bounds, allowed sources and records, with no caller-supplied
   bank/readiness object. Every procedure type is `Empty`; code-table premises
   are vacuous. `canonicalGeneratedInput_program` proves the generated core
   program is identical across all these configurations. `CanonicalStageWidths`
   and `CanonicalStageArithmetic` now derive all scalar and descriptor widths.
   `CanonicalRouterArithmetic` supplies explicit gap `6 + 4*clog 2 (n+2)` and
   stride `64*gap`, discharging the density bounds. `CanonicalRouterInput` and
   `CanonicalRouterStage` construct actual residue inputs from the original
   matching and prove stage data, common code and every metadata symbol bound.
   `CanonicalRouterBulk.canonicalRouterBulk_exec` executes any residue list for
   a fixed class and direction, prices framing, repairs and cleanup, and restores
   every tape except the record stream. Its effect is the composition of actual
   generated rank permutations. It assumes the initial framed metadata input;
   it does not execute its generation or prove a uniform amortized bound.
   `CanonicalRouterBits` now identifies every actual residue with its physical
   class shear in one common embedding, proves source separation, and composes
   all residues in execution order into the exact bulk shear. The execution
   theorem now returns this composed rank permutation directly; the generic
   stream-composition lemma connects it to actual output records.
   `CanonicalRouterTerminal` constructs the physical suffix coordinate table,
   proves source separation and fewer than `131*gap` entries, and identifies
   the existing compiler's output with the exact terminal shear.
   `CanonicalTerminalBank`, `CanonicalTerminalReady` and `CanonicalTerminalLayout`
   construct compatible binary operands and blank workspace on one fixed finite
   layout. `CanonicalTerminalRouting.canonicalRouterTerminal_exec` now executes
   shared-counter generation, coordinate compilation, routing and all cleanup,
   with an explicit cost and only the record stream changed. It assumes the raw
   coordinate table and binary dimensions, requires `n ≤ B`, and still takes
   canonical row bits and numeric fit proofs. The compilation-only intermediate
   wrapper was superseded before commit by this complete terminal execution.
   `CanonicalTerminalCore` and `CanonicalTerminalWords` now give a fixed terminal
   output permutation, a record-independent price, admissible metadata and live
   stream replacement. `FramedCanonicalTerminal` executes the existing loader,
   core and bank erasure with every step charged. `CanonicalRouterBank` shares
   exactly the record stream between disjoint bulk and terminal workspaces;
   its stream-update law preserves both projections. `CommonBankTerminal` and
   `CommonBankBulk` transfer the actual executions onto that common framed bank,
   preserving the other phase's workspace and sharing the three loader tapes.
   `CommonBankDirectional.commonBankDirectional_exec` now executes terminal then
   bulk on one bank with summed prices and only the record stream changed.
   `canonicalRouterDirectionalPerm_bits` proves its full-residue output is the
   complete physical directional class shear. This still assumes installed
   terminal metadata and the framed bulk input; it does not generate them.
   `CanonicalRouterClass` now composes three directional rank permutations into
   each physical matching class, then all three classes into the original
   coordinate involution, preserving outer record rows throughout. The generic
   `matchingRankSchedule` proves the composition before instantiating the
   canonical programs, avoiding expansion of their implementations. The tape
   execution is established separately below. `CanonicalDirectionalBank` constructs
   the inner bank from the original matching and records, proves its terminal
   projection and bulk readiness, and executes terminal then bulk without
   supplied readiness. Its words are below nine, including inner delimiter
   eight. `CanonicalDirectionalExec` uses outer delimiter nine and the existing
   framed core loader to install that concrete bank, run both phases and erase
   all inner metadata, including the bulk schedule input. The three fixed outer
   loader tapes retain the unused input suffix and rewind archive; all loading
   and erasure costs are charged. The actual outer frame
   is still supplied. `canonicalDirectional_ready` preserves the complete
   reusable-bank invariant after each call, and full-residue directional rank
   permutations are now proved independent of record payload and order.
   `CanonicalDirectionalPair` executes two consecutive calls with both metadata
   reloads and erasures charged, an arbitrary unused input suffix and readiness
   after the second call. The intermediate records are identified with the
   first call's actual permutation output. `CanonicalClassExec` now executes
   the complete false/true/false class schedule on the same bank, charges all
   three metadata reloads and cleanups, preserves readiness and identifies the
   final records with `canonicalRouterClassPerm`. Intermediate record lists
   carry exact equalities to the preceding call's output; no execution is
   supplied as a premise. The generic `delimitedCallAdvanced_comp` now collapses
   consecutive call boundaries into one cursor/archive update; class execution
   exposes that compact final state, with the concatenated frame and arbitrary
   unused suffix. Class rank permutations are also independent of live record
   payload and order, so later classes can consume earlier classes' outputs.
   `CanonicalClassInput` packages the three pure record lists, their shapes and
   exact intermediate-output equalities, without execution fields.
   `CanonicalMatchingExec` now executes all three classes in order two/one/zero,
   hence all nine directions, with every metadata reload and cleanup charged.
   Its final records are exactly `canonicalRouterMatchingPerm` of the original
   records, and its compact bank retains the unused input suffix, accumulated
   rewind archive and readiness. The class-link hypotheses are pure record
   equalities. `CanonicalMatchingInput` now constructs every intermediate
   record list and both class links from the original matching and records;
   its execution theorem requires no supplied intermediate witnesses.
   `CanonicalMatchingRestore` executes the final outer-input rewind, charges
   its linear cost and returns exactly the original bank with only the record
   stream updated by the matching permutation. The complete explicit metadata
   frame is still supplied. Executed frame production, arbitrary permutation
   decomposition, uniform total-cost bounds and the other R3 gates remain open.
   `CanonicalPermutationRank` now instantiates the existing two cycle reflections
   with the actual matching rank permutations, constructs the intermediate
   records, and proves the resulting rank action is the original arbitrary
   coordinate permutation while preserving outer rows. This closes the rank
   composition. `CanonicalPermutationExec` now joins the two matching tape
   executions in the reflection order, using the actual intermediate records,
   and executes all eighteen directions with summed setup/routing/cleanup costs.
   Its final charged outer-input rewind restores the entire bank except the
   stream, whose rank permutation has the requested coordinate-bit action and
   preserves outer rows. The complete explicit frame is still supplied;
   executed cycle-decomposition/table and frame production, uniform pricing,
   long-record amortization and short-record fallback remain open.
   `canonicalDirectionalPrice_uniform_overhead` now applies the uniform
   metadata/frame bounds to the actual directional ledger, bounding loader
   overhead and terminal routing while retaining bulk execution explicitly.
   `canonicalPermutationBudget_le` bounds the final restoration rewind by the
   complete uniform metadata budget. The bulk repair/table-production runtime
   still needs a uniform bound.
   `matchingFullProfileProductionCost_le_bound` now bounds extraction, residue
   dispatch, coordinate production and temporary erasure by a common
   polynomial ledger. `canonicalRouterProfileProductionCost_le` instantiates
   it for actual canonical calls with uniform logarithmic word widths.
   `reservoirClassLocalTableCost_le` and
   `canonicalRouterTableConversionCost_le` now bound original-to-local table
   conversion uniformly. `canonicalRouterMatchingPrice_le` bounds the actual
   matching call by its repair price plus polynomial production and coordinate
   cleanup overhead, reusing the concrete input-word bound. Repair execution
   and full bulk-ledger composition remain in the runtime gate.
   `canonicalRouterOriginalPrice_le` now combines conversion, profile
   production and both temporary erasures around the actual original-matching
   call. Its bound is the repair execution price plus one explicit
   `canonicalRouterOriginalSetupBudget`, uniform across residues and matchings.
   `originalMatchingStepPrice_le` charges the actual loader from frame size;
   `canonicalRouterStepPrice_le` now bounds each complete framed residue stage
   by its repair price plus `canonicalRouterStageSetupBudget`. Structural
   `delimitedSchedulePrice_le` and `delimitedScheduleInput_length_le` support
   summing actual call ledgers and frame lengths with loop overhead included.
   `commonBankBulkPrice_le` now composes those bounds for the actual complete
   bulk schedule, including loop overhead and final metadata rewind. Its
   result is the sum of actual repair execution prices plus one uniform
   polynomial setup budget times the number of stages. A uniform bound on
   that repair-price sum and long/short-record amortization remain open.
   `repairDensityScanCost_le` now bounds exceptional classification, scanning
   and sorting by `repairUniformDensityScanCost` using total address width.
   It retains the physical `5 / (128 * scale³)` exceptional-density factor
   exactly; no worst-case replacement of the sparse sort term is used.
   `canonicalRouterDensityScanCost_le` now specializes it to every actual
   canonical residue with scale `n + 1`, the common address width and the
   dimension-derived complete-rank key width. Selective passes, key emission
   and descriptor/setup costs still need bounds for the repair-price sum.
   `selectiveKeyEmitterCost_eq` and `selectiveKeyEmitterCost_le` now give an
   exact emitter ledger and a quadratic address-width bound.
   `selectiveKeyPassCost_eq` and `selectiveKeyPassCost_le` lift this to the
   complete executed keying pass, including record copies, stream restoration
   and counter reset, using `selectiveUniformKeyPassCost`. Canonical keying
   instantiation and the selective/descriptor costs remain open.
   Structural `fieldRun_length` and `higherFields_length` now bound header
   field counts. `selectiveRotationCost_le` gives a common quadratic header
   budget, and `selectiveRotationPassCost_le` includes both actual class scans,
   forward-order restoration and counter cleanup in
   `selectiveUniformRotationCost`. Swap-bank costs and composition of the
   full selective instruction schedule remain open.
   `selectiveSwapCost_le` now retains the compact-width exponent while
   bounding borrowed swap-bank lengths. `selectiveCost_sum_le` composes the
   actual twelve rotations and twelve swaps. `repairDensityCoreCost_le`
   combines complete keying, that selective schedule and the density-priced
   scan/sort into one executed-core bound. The swap-bank bound is still an
   explicit premise; it must be discharged for the installed canonical bank,
   then combined with descriptor and metadata setup/cleanup prices.
   `SelectivePrepared.swapBank_length_le` now derives the bank-length bound
   structurally from the five header lengths, empty payload and blank private
   workspace. `repairSetup_swapBank_length_le` applies it to the bank produced
   by actual metadata installation. Bounding the canonical header lengths and
   supplying the generated setup data remain before discharging the canonical
   repair-core bank premise.
   `repairCanonicalHeaders_length_le` now bounds all ten canonical swap
   headers by total address length plus scalar widths for rows, triple keyed
   payload and compact width. It reuses the existing arithmetic-header identity
   and canonical binary-copy length theorem. Supplying the canonical numeric
   fits and generated setup data remains before the final bank instantiation.
   `canonicalRouterHeaders_length_le` now supplies every numeric header fit
   internally from canonical scalar widths and the common address/key length,
   uniformly across residues. Connecting the generated setup data to the
   installed-bank and repair-core cost bounds remains open.
   `liveRepairInstalledBank_length_le` now connects the actual pending
   descriptor data, generated descriptor bank and metadata installation to the
   swap-bank length bound, transporting blank-workspace and left-stack facts.
   Instantiating it for `allSourceRepairPrepared` and combining the descriptor,
   install/erase and core ledgers remain open.
   `repairCompactRows_le_fields` and
   `repairCompactSourceWidth_le_fields` now bound every descriptor dimension
   structurally by the complete address width. Descriptor generation now has
   structural runtime bounds: `selectorRunLoopCost_eq` separates per-entry and
   per-gap costs; `sparseCoordinateRuns_gap_sum` identifies their total coordinate
   extent; `coordinateSelectorCost_le` bounds generation and cleanup from that
   extent. `affineProfileDescriptorCost_le` bounds the complete affine pipeline
   independently of source values, stride and offset, including the terminal
   coordinate, dense compilation and cleanup. `repairCoordinateSelectorCost_le`
   specializes the bound to every actual repair descriptor;
   `repairADescriptorCost_le` now bounds the complete grouped pipeline independently
   of the live activity and source profile. `LiveDescriptorMode.backendCost_le`
   joins both cases; `liveDescriptorCost_le` includes live setup, and
   `liveDescriptorBatchCost_le` bounds any executed job list from a common
   backend budget, including its terminal step. Both backend bounds are now
   monotone in slot count, row count and source width.
   `LiveDescriptorMode.backendBound_uniform` gives a common polynomial budget
   from address width, a slot-count bound and the scalar widths;
   `liveDescriptorBatchCost_uniform` lifts it to the complete job list.
   `repairLiveBankCost_le` now prices the actual eleven jobs under their
   existing live fit conditions, including zero-width fields.
   `affineProfileDescriptorCost_le_of_positions` and
   `repairADescriptorCost_le_all` discharge empty cases by proving the relevant
   source-slot count is zero; no extra positive-target-width premise remains.
   `canonicalRouterSlots_le` proves both ordinary and grouped slot counts are
   at most the address width, using the actual borrowed-field identity.
   `canonicalRouterDescriptorBudget_le` now substitutes common logarithmic
   scalar widths into that budget, uniformly across residues.
   `canonicalRouterDescriptorCost_le` now bounds all eleven actual descriptor
   jobs by the resulting common polynomial, discharging slot counts and live
   fit conditions internally and covering zero-width fields. Combination
   with the full repair ledger remains open. `MetadataJob.cost_le` now bounds
   copy, zero and unary installation jobs from source-word, scalar-width and
   counter-value bounds; `metadataInstallCost_le` lifts a per-job bound to the
   complete structural installation loop. `repairSetupJobsCost_le` now
   instantiates the actual fixed 34-job list, with explicit source-word,
   scalar-width and unary-value bounds. Deriving those bounds from generated
   canonical inputs remains open. The existing `metadataCleanCost_le` now
   lives in `MetadataClean` rather than `ConfigurationSize`, avoiding duplicate
   proofs or a wider import closure. `metadataInstalled_cleanCost_le` bounds
   cleanup directly from installed contents; `repairMetadataCleanCost_le`
   specializes cleanup of all 34 repair destinations to their actual setup
   payloads. `repairDescriptorWord_length_le` now gives the shared quadratic
   descriptor bound; the exact descriptor-length lemma was moved into
   `RepairCompactPattern` so generation, payload and erasure proofs share it.
   `repairSetupPayload_length_le` bounds every installed payload from total
   address width, row-key width, payload size, record count and a common header
   bound, including all unary counters. `liveRepairMetadataCleanCost_le` now
   transports pending data through actual live descriptor generation and
   installation, deriving the cleanup bound on that actual bank.
   `repairSetupSource_length_le` derives all 34 source-word lengths from setup
   data and the common descriptor/header bounds; `repairSetupInstallCost_le`
   uses these to bound installation without a separate source-length premise.
   `liveRepairMetadataInstallCost_le` transports installation through actual
   live generation. `liveRepairPrice_le` now combines all five phases on that
   bank: eleven descriptor generators, all 34 installations, the density-priced
   core with its actual installed swap-bank bound, metadata cleanup and
   descriptor erasure. `liveRepairUniformOverhead` is independent of live
   source choices and record contents; the compact-width swap power and sparse
   physical density factor are preserved. Instantiation for
   `allSourceRepairPrepared`, canonical scalar substitution and the outer
   header/profile/placement ledgers remain open.
   `generatedRepairCoreInput_raw` centralizes preservation of every raw repair
   register through the complete source-profile batch.
   `generatedRepairCoreInput_data` transports pending setup readiness through
   that actual batch; the existing blank-workspace theorem now reuses the same
   preservation lemma. `allSourceRepairPrepared_data` now composes classifier,
   width, header and source-profile readiness from the initial bank.
   `allSourceRepairPrepared_left` and `allSourceRepairPrepared_descriptor_raw`
   transport left stacks and raw descriptor blanks.
   `allSourceRepairPrepared_price_le` applies the complete five-phase repair
   bound to that actual prepared bank using only initial pending-mask data and
   initial blank-workspace facts. Canonical numerical substitution and the
   outer header/profile/placement costs remain open.
   `liveRepairUniformOverhead_mono` now proves monotonicity in header, counter
   and descriptor scalar widths; `canonicalRouterRepairOverhead_le` replaces
   every residue-dependent scalar by the common logarithmic budgets, leaving
   only a supplied common canonical-header length bound. The outer execution
   ledgers and long/short-record amortization remain open.
   `repairHeaderErasePrice_le` bounds all ten generated-header erasures from
   the common header width. `repairAllSourceProfileClean_cost_le` bounds actual
   cleanup of all eleven source profiles after a disjoint stream update by
   common slot-count and selector-width limits.
   `binaryTemporaryMaskCost_le` and `binaryPhaseMaskCost_le` now bound both
   executed classifier generators by explicit polynomials in a common dimension
   limit and scalar widths; both uniform budgets are monotone in their scalar
   widths. Canonical classifier substitution, uniform source-profile generation
   and placement costs still need to be composed with these bounds.
   `liveCoordinateProfilesCost_mono` now compares the entire source-profile
   pipeline by slot count, group size and borrowed width;
   `liveCoordinateProfilesCost_widths_mono` compares all scalar widths, including
   gated/optional frames, grouped repetition and the counter/affine generators.
   These structural proofs reuse the actual cost definitions.
   `canonicalRouterProfileCost_le` now supplies one residue-independent profile
   generation budget by majorizing slots by address width, retaining the common
   gap and substituting logarithmic scalar widths.
   `canonicalRouterClassifierCost_le` bounds both classifier generators from
   address width alone; `canonicalRouterHeaderEraseCost_le` discharges the
   common header erasure width. Combining the full outer ledger and placement
   costs, followed by long/short-record amortization, remains open.
   `allSourceGeneratedRepairPrice_le` now combines classifier, width, header
   and source-profile generation, prepared repair and every cleanup into a
   bank-independent overhead plus the density-priced key/rotation/swap core.
   `allSourceGeneratedUniformOverhead` names that actual numerical ledger.
   `allSourceGeneratedUniformOverhead_le` now majorizes all physical field
   sizes, slot counts, selector widths and profile-cleanup terms together,
   accepting the already proved common classifier/profile budgets.
   `canonicalRouterGeneratedOverhead_le` now performs the remaining scalar
   and repair-overhead substitutions into `canonicalRouterGeneratedOverhead`,
   one numerical formula in the original dimensions, row count, payload size
   and a common header bound, independent of residue and live matching/source
   choices. `canonicalRouterInput_generatedCost_le` now substitutes this
   into every actual stage input, giving `canonicalRouterGeneratedCostBound`
   with the compact borrowed-width swap power and sparse physical density
   preserved. Uniform placement row-length substitution, the final combined
   stage budget and full-router summation remain.
   `binaryExchangeChainCost_le` now bounds any executed forward/reverse
   placement schedule from its call count and per-call price; bounding those
   actual call prices and composing placement remain open.
   `generatedExchangeBound_le` now bounds interval-dependent setup and cleanup
   from address width, scalar lengths and a supplied swap-bank size bound.
   `BinaryExchangeCall.cost_le` includes actual binary conversion and final
   cleanup for each placement call. Both retain the actual exchanged-width
   power rather than replacing it by the full address width. Canonical
   placement-bank/width substitution and schedule composition remain open.
   `canonicalPlacementInputStack_swapBank` and its length corollary now prove
   the actual shared placement swap bank is empty, independently of the repair
   core contents, so its initial size term is zero.
   `generatedExchangeUniformOverhead_mono` supports common scalar/row-length
   substitution. Connecting these facts to the actual schedule calls and
   composing forward/reverse placement still remain open.
   `BinaryExchangeCall.cost_uniform_overhead` now substitutes shared scalar
   budgets while preserving each actual exchanged-width power.
   `binaryExchangeChainCost_le_sum` retains the sum of those width powers over
   an arbitrary schedule. `binaryScheduleCalls_cost_le` applies the bound to
   actual shared-bank calls with a blank swap bank; scalar conversion, header
   generation and cleanup are included. Canonical schedule instantiation and
   composition with generated repair remain open.
   `binaryScheduleChainCost_le` now prices complete actual schedules by their
   width-power sum and call count.
   `canonicalPlacementInputStack_scheduleCost_le` instantiates that theorem on
   the actual canonical placement stack, discharging the blank swap-bank
   premise. `reservoirExchangeWidthPrice_sum` now evaluates both actual
   three-call directions for any numerical width price: one front exchange
   plus two compact-width exchanges. `reservoirExchangeWidthPrice_sum_le`
   removes the reservoir choice for any monotone price.
   `reservoirExchangeWidthPower_sum_le` specializes this to the actual swap
   exponent, including zero-width exchanges.
   `canonicalPlacementInputStack_reservoirCost_le` now prices either complete
   canonical placement direction with one common front-reservoir power, two
   actual compact-width powers, and three fully charged scalar/setup/cleanup
   calls. Canonical scalar substitution and composition with generated repair
   remain open. `GeneratedPlacedInput.configurationRaw`, `.configurationData`
   and `.configurationBlank` now recover the initial configuration readiness
   directly from the actual stage input. The existing canonical price
   independence proof reuses this transport instead of duplicating projections.
   `GeneratedPlacedInput.generatedPrice_le` now instantiates the complete
   generated-core ledger from stored input readiness.
   `.placementPrice_le` derives the actual shared-bank input and prices either
   direction when its supplied swap bank is blank. `.price_le` combines both
   placements and generated repair into one bound on the actual stage price;
   no bank-readiness or execution-oracle hypotheses remain beyond the input
   contract. The remaining premises are total address/slot bounds, a common
   header width and the blank placement bank, all available for canonical inputs.
   `canonicalGeneratedInput_price_le` now discharges the placement-bank
   premise for constructed inputs. `canonicalRouterInput_price_le` applies the
   combined stage bound to every actual router residue, discharging address
   width, both slot bounds and the common header width internally.
   `canonicalRouterInput_placementCost_le` now substitutes the common
   logarithmic row-counter length. `canonicalRouterInput_price_uniform`
   combines placement and generated repair into `canonicalRouterStageCostBound`,
   independent of residue, matching and live records.
   `canonicalRouterInput_prices_sum_le` sums any actual residue list, and
   `canonicalRouterBulkPrice_uniform` bounds the complete executed bulk ledger
   by stage count times that common budget plus the existing loader/frame
   budget. `canonicalRouterDirectionalPrice_uniform` adds terminal routing
   and directional setup. `canonicalRouterClassPrice_uniform`,
   `canonicalRouterMatchingPrice_uniform` and
   `canonicalRouterPermutationPrice_uniform` compose all eighteen directions.
   `canonicalPermutationBudget_uniform` includes the final metadata rewind,
   bounding the actual restored-permutation execution budget by one numerical
   expression independent of the permutation and live records, with no residue
   price sum. `canonicalPermutationBudget_canonical_le` now chooses canonical
   top-level scalar widths and bounds the row counter by `R.log2 + 1`.
   `canonicalPermutationCode_exec` uses this dimension-only
   `canonicalPermutationCostBound` for actual restored execution, replacing
   its earlier permutation-dependent budget statement without adding a parallel
   execution theorem. Long-record amortization, executed short-record fallback
   and compact-input metadata production remain open; R3 and kappa are unchanged. The accumulated
   cost-proof checkpoint passed the full guarded root build (15,302 jobs) and
   the axiom audit (351,694 declarations); R3 remains open. `liveDescriptorEraseCost_le`
   uses those bounds to price erasure of any actual descriptor job list by
   its length times a quadratic address-size cost, including loop overhead.
   Descriptor generation and metadata install/erase bounds still remain.
   `canonicalPermutation_canonical_exec` now chooses both scalar widths and the
   canonical binary row counter from the dimensions for the entire restored
   eighteen-direction program. Coordinate positivity, binary fit, canonicality
   and the row-counter value are discharged internally, retaining the existing
   positive row count, record shape, geometric stride and address-width gates. This selects explicit input words
   and does not execute their production or close the uniform-cost gates.
   `ConfigurationWrite` now has one caller-delimited serializer; its original
   separator interface and cost theorem specialize that implementation.
   `FramedCoreWrite` serializes exactly the nonstream bank words consumed by the
   framed loader, restores all sources and scratch, preserves any output suffix
   and charges at most seven steps per framed symbol plus one.
   `canonicalDirectionalFrameWrite_exec` instantiates it for the actual
   delimiter-nine directional frame. It assumes the live metadata bank;
   generating its scalar/table/nested-input words still needs executed
   composition. `framedCoreWriteClean_exec` now follows serialization with the
   existing metadata cleaner, clears exactly the nonstream source registers,
   retains the stream, unrelated tapes and output suffix, and charges at most
   nine steps per framed symbol plus two. The concrete
   `canonicalDirectionalFrameWriteClean_exec` instantiates that pipeline for
   the actual directional bank. Assembling successive generated frames and
   composing all upstream word producers remain open.
   `framedCoreWriteClean_ready` now proves that the cleared bank, unchanged
   records and blank loader scratch establish the actual router readiness
   invariant. `CanonicalDirectionalAssemble` executes serialization, source-bank
   cleanup, frame loading, terminal routing and bulk routing in one program,
   charges the extra serialization/cleanup cost and retains readiness afterward.
   It requires a live canonical metadata bank rather than an already serialized
   frame; producing that bank from compact operands remains open.
   `CanonicalInputStream` now proves stream-update transport through the repair,
   live-profile, header, width, classifier and placement extensions. Its complete
   `canonicalGeneratedInput_bank_updateStream` theorem changes only the physical
   stream register when the record payload or order changes; scalar/profile
   metadata are unchanged. This provides the bank-level independence needed to
   lift frame production and its price off the current payload. `CanonicalRouterMetadata` now transports this law through the actual
   matching-table producer/repair bank, proves every residue metadata frame
   independent of live records, and lifts it to the whole concatenated bulk
   input for any residue schedule. Scalar and matching-table words are therefore
   not copied from the record payload.
   The same module now transports the complete common directional bank and
   proves full directional, class, matching and arbitrary-permutation frames
   independent of record payload and order. `CanonicalPermutationMetadata`
   defines the complete frame from dimensions and the coordinate permutation,
   using a structural zero-record witness, and proves equality with the actual
   frame for every admissible live record stream. This removes payload data
   from the metadata interface; executed generation and uniform setup/pricing
   are still open. `CanonicalInputPrice` reuses the generic stream-update price
   theorem after transporting both complete canonical stacks.
   `CanonicalRouterPrice` lifts price independence through actual residue
   production, framing, bulk schedules, directions, classes, matchings and all
   eighteen directions. `canonicalPermutationBudget` now packages that price
   plus the final input rewind without live records, and
   `canonicalPermutationCost_eq_budget` identifies the actual restored-router
   ledger with it. `CanonicalRouterCode` also proves record independence of the
   actual bulk, directional, class, matching and eighteen-direction programs.
   Its bulk and directional geometry-independence theorems also show that
   dimensions, matching operands and scalar widths do not change directional
   code (with the class and direction fixed). The complete
   `canonicalPermutationCode_geometry_independent` theorem lifts this to all
   eighteen directions: dimensions and the coordinate permutation change
   operands and the ledger, but not the executed schedule code.
   `canonicalPermutationCode` removes live records from the code interface,
   with equality to the executed program for every admissible stream.
   `canonicalPermutationCode_exec` combines these equalities into the actual
   restored execution contract, using dimension-derived scalar operands and
   the record-independent metadata and budget; metadata is still supplied.
   The budget still depends on dimensions and the coordinate
   permutation; a worst-case asymptotic bound, executed metadata generation and
   the remaining R3 acceptance gates are unproved. Canonical terminal scalar
   widths and row-counter words are now selected from dimensions; executing
   their production remains open. Original
   permutation decomposition/table generation, remaining scalar metadata setup,
   `canonicalTerminalPrice_le` now replaces the matching-dependent terminal
   instruction count by the geometric bound `131 * canonicalRouterGap n`;
   `canonicalDirectionalPrice_le` applies it to the actual directional ledger.
   Reusing the existing exact `elementaryCoordinateFrames_length` formula,
   `canonicalRouterTerminalFrames_length_le` bounds the terminal table by
   `131 * canonicalRouterGap n` padded coordinate pairs.
   Generic `delimitedBankFrames_length_le` and `framedCoreFrames_length_le`
   now bound serialization by word count times maximum word length plus one
   delimiter. `canonicalTerminalRoutingBank_length_le` bounds every nonstream
   terminal word by the scalar widths, row-counter length and coordinate-table
   size, with structural register cases. Concrete nested bulk-word length
   bounds are still required. `middleLookupMetadata_length` gives the exact
   three-exchange frame size. `reservoirMiddleLookupBank_length_le`,
   `reservoirMiddleProductionBank_length_le` and
   `reservoirClassLocalBank_length_le` now bound every matching-table producer
   input word by `n * (2 * L + 2) + 12 * L + 12`, independently of matching
   values. Repair-bank word bounds and their complete frame composition remain
   open. `canonicalRepairPayload_length_le`, `canonicalRepairInput_length_le`
   and `canonicalProfileCoreBank_length_le` now bound the initial repair scalar
   operands and source-coordinate core, excluding the live record stream.
   `canonicalDescriptorOperands_length_le` now bounds all canonical profile
   operands by their scalar widths, and `canonicalLiveInputBank_length_le`
   transports a nonstream core bound through the complete live-profile bank.
   One shared `addCases_word_length_le` lemma now transports nonstream bounds
   through appended scalar banks. `canonicalHeaderInputBank_length_le`,
   `canonicalWidthInputBank_length_le` and
   `canonicalClassifierInputBank_length_le` instantiate it for all three outer
   extensions. `canonicalPlacementInputStack_length_le` now handles the
   placement overlay, including stream exclusion and blank swap workspace.
   `canonicalGeneratedInput_length_le` composes all these bounds for every
   nonstream word of the actual generated repair input, using dimensions and
   scalar widths only. `matchingProductionBank_length_le` and
   `matchingInitialBank_length_le` transport bounds through the matching
   workspace with explicit padded table and scalar sizes.
   `originalMatchingInputBank_length_le` joins producer and repair bounds,
   excluding the physical stream and accounting for the cleared shared table.
   `matchingPlacedInputBank_length_le` and
   `originalMatchingPlacedInputBank_length_le` instantiate those overlays;
   `originalMatchingFrame_length_le` bounds their actual serialized frame
   from the core bound and dimension-derived scalar/table sizes.
   `canonicalGeneratedMetadataWidth` now names the
   shared dimension-only expression; `canonicalRouterInput_length_le`
   instantiates it for actual canonical residues. `canonicalRouterFrame_length_le`
   bounds each serialized residue frame by `canonicalRouterFrameWidth`, with
   no matching or record arguments in that budget.
   `canonicalDirectionalBulkInput_length_le` sums those budgets over the actual
   residue schedule. `canonicalRouterCommonBank_length_le` excludes the shared
   stream while joining metadata bounds. `canonicalDirectionalBank_length_le`
   then combines terminal word sizes and the complete bulk-input budget;
   `canonicalDirectionalFrame_length_le` bounds the actual outer frame using
   those dimensions alone. `CanonicalClassInput.frame_length_le`,
   `canonicalMatchingFrame_length_le` and `canonicalPermutationFrame_length_le`
   lift the bound through all eighteen directions.
   `canonicalPermutationMetadata_length_le` exposes the resulting bound on the
   record-independent metadata interface. Simplification of the residue sum
   to a uniform polynomial bound remains open.
   `liveDescriptorMagnitude_le` now bounds every descriptor mode family by a
   polynomial in profile dimensions, and
   `liveDescriptorCanonicalWidths_indexBits_le` derives a uniform logarithmic
   index-width bound. `canonicalRouterDescriptorMagnitude_le` specializes the
   magnitude to `4 * n + 1` for every canonical residue.
   `canonicalRouterIndexBits_le` and `canonicalRouterCoordinateBits_le` then
   give common logarithmic index and affine-coordinate widths independent of
   the residue. `canonicalRouterCountWidth_le` now bounds the actual matching
   byte-count header uniformly, using the coordinate bound and the fact that
   all profile slots fit inside the address width. Remaining scalar widths
   still need to be substituted into the full residue/frame budgets.
   `canonicalScalarWidth_mono` and `canonicalScalarWidth_add_le` now support
   shared scalar estimates. `canonicalRouterBlockWidth_le` and
   `canonicalRouterKeyWidth_le` bound the actual keyed-payload and complete
   address-key headers by logarithmic address, row-count and payload widths,
   uniformly across residues. `canonicalRouterDimensionWidths_le` bounds all
   seven geometry/classifier/placement dimension headers by the common address
   scalar width. `canonicalRouterRecordWidths` identifies the remaining
   record-count and payload widths and bounds the row-counter word
   logarithmically, independently of the residue.
   `canonicalRouterDescriptorWidths_le` collects all six descriptor-width
   bounds without expanding the full arithmetic record.
   `canonicalRouterMetadataWidth_uniform` now combines all scalar, descriptor
   and row-counter estimates into `canonicalRouterUniformMetadataWidth`, one
   explicit polynomial in address size and logarithmic scalar widths valid for
   every residue. `canonicalRouterFrameWidth_uniform` now bounds every
   serialized residue frame by `canonicalRouterUniformFrameWidth`.
   `canonicalRouterFrameWidths_sum_le` replaces the residue sum by stage count
   times that common polynomial budget.
   `canonicalDirectionalFrameBudget_uniform` now substitutes it into the
   outer loader budget. `canonicalPermutationMetadata_length_uniform` bounds
   the complete eighteen-direction frame without a residue sum, and
   `canonicalPermutationMetadata_canonical_length_le` selects scalar widths
   and bounds the row counter from dimensions alone. This closes the explicit
   uniform metadata-size bound; executed production, the full runtime ledger,
   long-record amortization and short-record fallback remain open.
   Bulk setup and complete frame-size bounds, uniform amortization and short-record
   fallback remain open. R3 and kappa
   are unchanged.
5. Amortize setup for long records and supply the executed short-record fallback,
   preserving spectators in both regimes.
   `selectiveUniformKeyPassCost_amortized` now absorbs complete-rank key
   generation, record traversal and counter cleanup into `188 * M * B` when
   there is at least one record and payload width is at least the square of
   address-plus-row-key width plus one. This is the first local long-record
   amortization bound. `selectiveUniformRotationCost_amortized` uses the same
   payload threshold to absorb both scans and descriptor computation into
   `400 * M * B` per rotation. `repairDensityCoreCost_amortized` now combines
   keying and all twelve rotations inside the actual core into
   `4988 * R * 2^n * B`, retaining the exact compact-width swap and physical
   exceptional-repair terms. `selectiveUniformSwapCost_amortized` absorbs key
   fields and fixed bank overhead into record volume while retaining the actual
   compact-width supplier power. `repairDensityCoreCost_amortized_swaps` applies
   this to all twelve swaps: the core is bounded by a linear-volume term plus
   the compact-width supplier term and the physical exceptional-repair ledger.
   It requires the shared long-payload threshold and fixed bank/setup cost at
   most total record volume.
   `repairUniformDensityScanCost_amortized` now bounds all exceptional scans
   and sorting by a linear-volume term plus the explicit physical correction
   `(n + rb) * 155 / (128 * scale^3)` times volume.
   `repairDensityCoreCost_long_records` combines the complete actual core into
   linear volume, the compact-width supplier power and that sparse correction.
   `repairDensityCoreCost_long_records_density` absorbs the sparse correction
   when the cube of the density scale dominates address-plus-row-key width.
   `repairUniformDensityScanCost_canonical_amortized` discharges this for the
   existing canonical scale `n + 1` when row-key width is at most `n`, giving
   a complete scan bound of `391 * R * 2^n * B`. Both are checked; the latter
   does not cover arbitrarily wide row keys. Controlling the remaining row-key
   regimes, outer metadata amortization and the executed short-record fallback
   remain open. The wide-row obstruction is specifically the complete-rank
   exceptional sort: its key includes the row identifier, although
   `selectiveIdealIdx_lt` already uses preservation of the quotient by the
   address-block size. A row-at-a-time implementation is a candidate for removing
   this identifier from repair keys without changing the density geometry.
   `SelectiveRows` now proves exact row preservation, injectivity of the
   address-only destination key within each row, and the restricted row
   permutation. It also proves equality of source observations modulo a row
   and the exact row-offset endpoint: the global destination is the original
   row offset plus the one-row destination. Its guarded check passed at about
   1.19 GiB. This justifies the shorter key logically; it still needs an executed block driver, endpoint
   composition on record lists, restored shared metadata and a bound for
   per-row setup. `SelectiveRowRecords.moveRecs_selective_rows` now identifies
   the complete global record endpoint with the concatenation of row-local
   endpoints, preserving row order; its guarded check passed at about 1.17 GiB.
   No shape assumption or concrete enumeration is needed for this identity.
   `RowTransfer.rowTransfer_exec` now extracts one counted row in forward
   order, preserving the unread suffix and restoring counter/buffer scratch,
   in exactly `6 * rowLength + 6` steps. `rowRoutingCall_exec` composes extraction,
   a priced stream-only row call and reversed output archiving, restoring the
   work tape with additional cost `8 * rowLength + 8`. Its guarded check passed
   at about 1.71 GiB. The call hypothesis still needs instantiation with actual
   one-row routing. `RowRoutingLoop.rowRoutingLoop_exec` now proves the fixed
   counted outer loop under a priced invariant-preserving step contract: it
   consumes exactly the row count, preserves the unread suffix, archives routed
   output in reverse stream order and costs at most the row count times
   `(stepPrice + 2)`, plus one. Its guarded check passed at about 1.76 GiB.
   `RowTransfer.countedRowRoutingCall_exec` now supplies the concrete counter
   advance plus row-call execution, with additional cost `8 * rowLength + 9`.
   `rowRoutingRewind_exec` restores the original count word, empties both
   archives and prepends routed output before the untouched input suffix in
   exactly `2 * countLength + 2 * outputLength + 4` steps. Their guarded check
   passed at about 1.73 GiB. `RowRoutingLoop.rowRoutingProgram_exec` now
   composes initial count testing, the full loop and both rewinds: only the
   routed input prefix changes, the suffix and every other register are
   restored, and the cost is bounded by `rowCount * (stepPrice + 4)` plus
   twice the routed output length plus six. Its guarded check passed at about
   1.77 GiB. Instantiating the loop's invariant-preserving step contract with
   the counted wrapper, actual one-row routing and metadata invariants remains
   open; the counted step still has an explicit inner-call premise.
   `CanonicalRowCall.canonicalRowRoutingCall_exec` now embeds the actual
   one-row canonical coordinate router in any injective larger tape bank,
   preserving every external driver register and restoring its supplied
   metadata frame. Its dimension-only cost bound uses row count one and its
   guarded check passed at about 2.56 GiB. This is the concrete inner execution
   available for the driver, not yet a discharge of the driver's readiness
   invariant or compact-input metadata-production gate.
   `CanonicalRowBankReady` now states the reusable scratch/metadata invariant
   without constraining the work stream. Its preservation is proved for every
   external driver-tape update and every work-stream update. `with_records`
   derives the actual router's `FramedCoreReady` from a loaded row's shape;
   the concrete row-call theorem now uses this bank invariant directly.
   The guarded check passed at about 2.57 GiB. `RowDriverLayout` now supplies
   seven concrete external driver tapes and proves their joint disjointness
   from the embedded work stream and the complete router bank; its guarded
   check passed at about 1.19 GiB. Applying the bank invariant across the
   concrete counted loop and aligning its row effects with the global
   coordinate-permutation endpoint remain open.
   `canonicalPermutationRank_records_independent` now proves the actual rank
   permutation is independent of live records for arbitrary outer row count,
   using its coordinate-bit action and preserved row. `canonicalRowEffect`
   therefore names one fixed stream effect; `canonicalRowEffect_records`
   connects it to actual moved records, and the embedded row-call theorem now
   returns that fixed effect directly. The guarded check passed at about
   2.57 GiB. This removes the payload-dependent endpoint from the inner-call
   boundary; it does not yet discharge the complete outer-loop contract.
   `CanonicalCountedRow.canonicalCountedRow_exec` now discharges the counted
   wrapper's inner-call premise with the actual canonical one-row router.
   It transports reusable bank readiness through count/archive/input updates,
   loads the live row, proves output length preservation and charges the
   one-row dimension-only router cost plus `8 * rowLength + 9`. Its guarded
   check passed at about 2.56 GiB. No abstract router-execution assumption
   remains in this step theorem; assembling its preserved driver invariant
   across the complete outer loop remains open.
   `CanonicalRowDriver.canonicalRowDriver_exec` now completes that loop
   composition with actual canonical routing: it derives each inner readiness
   condition, preserves the scratch/metadata invariant, routes every supplied
   row, restores all driver registers and metadata, and preserves an arbitrary
   unread suffix. Its bound is row count times the one-row router price plus
   linear extraction/archive/rewind overhead; its guarded check passed at
   about 2.57 GiB. It still assumes the reusable metadata and unary count/width
   words are supplied. Identifying the concatenated row effect with the global
   coordinate rank, amortizing the one-row price, and producing compact-input
   metadata/counters remain open. `canonicalRowEffect_records_length` now
   proves that every valid routed row has exactly `2^n * B` output symbols.
   The driver bound consequently charges the final rewind by total record
   volume, with no payload-dependent output-length term. The updated driver
   passed its guarded check at about 2.57 GiB.
   `CoordinateRowRank` now proves forward and inverse row-offset identities
   for arbitrary permutations with the same coordinate-bit action and preserved
   outer row. `moveRecs_coordinate_rows` lifts these to the complete global
   record-list decomposition. Its guarded check passed at about 2.44 GiB.
   `CanonicalRowEndpoint.moveRecs_canonical_rows` now instantiates this
   identity with the actual global canonical rank and a payload-independent
   one-row canonical rank. Its guarded check passed at about 2.55 GiB;
   a structural cast lemma avoids reducing the concrete rank construction.
   `canonicalRowRecords_shape` now proves the exact record count and payload
   shape of every structural row slice. `canonicalRowEffect_localRank` connects
   its stream effect to local record movement, and `canonicalRowEffects_global`
   identifies the concatenated row effects with the actual global canonical
   endpoint. The guarded check passed at about 2.57 GiB.
   `canonicalRowRecords_reassemble` and `canonicalRowRecords_stream` now
   reconstruct the original records and flat input from those slices.
   `CanonicalRowDriver.canonicalRowDriver_global_exec` applies both endpoint
   bridges to actual execution: its input is the original record stream and
   its output is the canonical global permutation, with full driver/bank
   restoration and an arbitrary suffix preserved. Its guarded check passed
   at about 2.58 GiB. Supplied metadata/counter production, one-row price
   amortization and the short-record regime remain open. Do not impose a
   permanent bound on row count to bypass these obligations.
   The accumulated dimension-only execution and local long-record cost chunk
   passed the full guarded root build (15,302 jobs, peak 29.6 GiB) and axiom
   audit (351,747 declarations, peak 4429.5 MiB) on 2026-10-24. These checks
   validate the stated conditional bounds, not the remaining R3 acceptance gates.
   The accumulated row-driver execution and global endpoint chunk passed the
   full guarded root build (15,312 jobs, peak 4.8 GiB) and axiom audit
   (351,823 declarations, peak 4428.5 MiB) on 2026-10-24. These checks cover
   supplied-metadata row execution, not the remaining R3 acceptance gates.
   `CanonicalRouterPrice.canonicalRouterGeneratedCostBound_amortized` now
   applies the key/rotation/swap/density estimates to the actual canonical
   generated-stage budget, retaining its outer metadata overhead and compact
   supplier power. `canonicalRouterGeneratedCostBound_one_row` specializes it
   to the row driver: payload at least `(n + 2)^2` and setup at most row volume
   absorb the sparse repair term without restricting the total row count.
   Both passed a guarded check at about 2.65 GiB. Outer metadata, placement
   and terminal amortization, input generation and the short-record regime
   remain open; this does not yet bound the entire router asymptotically.
   The outer metadata bottleneck includes `MetadataJob.cost` charging binary
   to unary conversion by width times final value, although `toUnary` already
   uses Horner doubling. `Host/EachSymPrice` now executes the existing symbol
   loop with individual iteration prices and a telescoping doubling bound;
   its guarded check passed at about 1.20 GiB.
   `Host/BinArith.toUnary_exec_linear` applies this to actual Horner prefix
   sizes and proves execution in at most `6 * value + 11 * width + 6` steps,
   with identical output and restored scratch. The old bound is a short
   compatibility corollary; duplicate conversion proofs and unused preliminary
   sum lemmas were removed. The consolidated module passed its guarded check
   at about 1.23 GiB. `MetadataJob.cost` now uses the linear-value unary price,
   and its actual installation theorem calls `toUnary_exec_linear`. The
   metadata job module passed its guarded build. Repair setup, compact repair,
   live generated overhead and shared elementary/terminal setup budgets have
   been updated to sums of value and width, removing the former product.
   The affected routing dependency build is in progress; full caller validation
   and final outer-overhead amortization remain open. The rebuild identified
   two shared-routing callers carrying the old numeric setup formula; both
   have been updated and the caller rebuild is continuing.
   `LiveRepairAmortized` proves exact separation of live setup into scalar
   metadata work plus `272 * (B + R * 2^n)`, bounded by `544` times record
   volume. `CanonicalRouterAmortized` lifts this to canonical generated setup
   and proves its scalar part is affine in header width and binary payload
   width, with coefficients `292` and `1260`. Both guarded checks passed,
   peaking at about 2.56 GiB. The corrected caller build through
   `CanonicalRouterPrice` passed (8,924 jobs, peak 5.1 GiB).
   `canonicalRouterGeneratedOverhead_one_row` now absorbs all payload-width
   and actual header-width dependence into linear row volume, leaving an
   additive setup budget depending only on address dimension.
   `canonicalRouterGeneratedCost_one_row_amortized` combines this with the
   actual core ledger: dimension setup plus `8887` times row volume, the
   compact-width supplier term and one step. Long-payload and fixed-bank
   setup hypotheses remain explicit. The guarded check passed at about
   2.59 GiB. Placement/terminal amortization, global asymptotic comparison,
   compact-input generation and short-record execution remain open.
   `canonicalRouterPlacementCostBound_split` now separates the actual
   placement ledger into its two physical supplier-width powers, dimension
   setup and scalar/volume terms. `canonicalRouterPlacementCostBound_amortized`
   absorbs the binary payload width into `306` times record volume, leaving
   the supplier powers and additive dimension setup explicit. Its guarded
   check passed at about 2.61 GiB.
   `canonicalRouterStageCost_one_row_amortized` now combines both placement
   directions with generated execution: a complete residue stage is bounded
   by dimension-only setup, `9499` times row volume and the actual reservoir/
   compact supplier terms. Its guarded check passed at about 2.62 GiB.
   `canonicalTerminalPrice_split` now separates the complete terminal ledger
   into dimension setup, physical stream work and binary payload width.
   `canonicalTerminalPrice_one_row_amortized` absorbs its payload terms into
   linear row volume per coordinate instruction, using only positivity of
   payload size. The exact ledger needs no extra address-times-payload-width
   estimate; unused preliminary quadratic-width lemmas were removed.
   The guarded check passed at about 2.63 GiB. Combining the terminal and bulk
   bounds with schedule/frame amortization remains open.
   Exact split lemmas now isolate binary payload width in uniform metadata,
   residue frames, residue setup and outer directional frames.
   `canonicalRouterDirectionalSetupBudget_amortized` combines their full
   schedule/frame ledger into dimension-only setup plus a tape/count-dependent
   coefficient times record volume. Its guarded check passed at about 2.65 GiB.
   `canonicalRouterDirectionalCost_one_row_amortized` now combines that
   ledger with actual terminal and residue-stage bounds into one complete
   directional-pass bound. Its guarded check passed at about 2.65 GiB.
   `canonicalPermutationCost_one_row_amortized` now lifts the result through
   all eighteen directions and charges the final metadata rewind, yielding
   `canonicalPermutationAmortizedBound`. Its guarded check passed at about
   2.65 GiB. `CanonicalRowDriverAmortized` now applies the complete budget
   to actual global row-driver execution, retaining its exact canonical
   permutation endpoint, restored bank/counters and arbitrary suffix.
   Its guarded check passed at about 2.57 GiB. Dimension/supplier-width
   asymptotic comparisons, supplied metadata/counter generation and the
   short-record regime remain open; the long-payload and fixed-bank setup
   hypotheses are still explicit.

   The accumulated sharp unary pricing and full amortized row-driver chunk
   passed the guarded root build (15,316 jobs, peak 32.4 GiB) and axiom audit
   (351,887 declarations, peak 4429.5 MiB) on 2026-10-24. These verify the
   explicit conditional execution/cost bounds; R3 and kappa remain unchanged.
   `CanonicalRouterSupplier` now bounds both physical reservoir and compact
   supplier widths by the routed address width under canonical geometry.
   `canonicalRouterStageAmortizedBound_supplier_le` consequently bounds all
   supplier contributions in a residue stage by one fixed coefficient times
   row volume times `n^tau`. The guarded check passed at about 2.59 GiB.
   `canonicalRouterDirectionalAmortizedBound_supplier_le` now lifts that
   simplification through the complete directional ledger, explicitly separating
   dimension-only setup from volume times the address-width supplier power
   and the remaining tape/count coefficient. Its guarded check passed at about
   2.60 GiB. `canonicalPermutationAmortizedBound_width_le` now lifts the
   comparison through all eighteen passes and metadata rewind, leaving one
   coefficient times row volume times `n^tau`, plus dimension-only setup.
   Its guarded check passed at about 2.60 GiB.
   `canonicalPermutationSupplierCoefficient_log_le` now bounds the complete
   supplier/volume coefficient by one fixed constant times
   `Nat.clog 2 (n + 2) + 1`. A structural affine identity over arbitrary tape
   counts avoids kernel expansion of concrete router constants, reducing the
   check from about 5.6 GiB to 2.61 GiB. The final guarded check passed.
   `canonicalPermutationAmortizedBound_log_le` now combines logarithmic
   geometry and supplier width into one bound: dimension-only setup plus a
   fixed constant times row volume times `n^tau` times
   `Nat.clog 2 (n + 2) + 1`. Its guarded check passed at about 2.61 GiB.
   `CanonicalRouterSetup.canonicalRouter_one_row_setup_le` also derives the
   fixed-bank inequality for long records beyond an explicit fixed
   supplier-dependent dimension threshold. Its guarded check passed at about
   2.59 GiB. It does not assume the supplier's noncomputable tape count fits a
   small numeric threshold. Dimensions below that threshold, dimension-only
   setup absorption, metadata/counter generation and short-record execution
   remain open; the full R3 scope is unchanged.
   `CanonicalRowDriverLogBound.canonicalRowDriver_global_log_exec` now applies
   the logarithmic/address-power comparison to actual global execution and
   derives bank setup from the fixed supplier-dependent dimension threshold.
   Its guarded check passed at about 2.57 GiB. The output/restoration contract
   is unchanged; its cost still contains repeated dimension-only setup, and
   the metadata and unary driver inputs remain supplied rather than generated.
   `SetupAbsorption.repeatedPolynomialSetup_eventually_le_volume` reuses the
   existing exponential-growth theorem to absorb any polynomial dimension
   setup repeated per row, uniformly in row count and positive payload width.
   Its guarded check passed at about 1.62 GiB. The concrete routing dimension
   budget still needs an explicit polynomial majorant before this theorem
   can remove its repeated setup term; that obligation is not assumed solved.
   `CanonicalRouterDimension` now identifies the actual terminal dimension
   setup with a natural-number ledger and proves a fixed-coefficient cubic
   bound in `n + 1`. The cubic proof is structural over arbitrary tape counts,
   instantiated only afterward; its guarded check passed at about 2.63 GiB.
   `canonicalRouterUniformMetadataWidth_polynomial` now bounds canonical
   one-row metadata by `64 * (n + 1)^2`.
   `canonicalRouterUniformFrameWidth_polynomial` bounds each residue frame
   quadratically with a fixed tape-count coefficient. Both passed the guarded
   check at about 2.65 GiB.
   `canonicalDirectionalUniformFrameBudget_polynomial` now bounds the full
   outer directional frame cubically. `canonicalMatchingProfileProduction_polynomial`
   bounds matching-profile production by a fixed degree-six majorant, using
   a structural cubic bound before substituting actual scalar widths.
   The guarded check passed at about 2.66 GiB.
   `canonicalReservoirTableCost_polynomial` now bounds reservoir class-table
   conversion cubically. `canonicalRouterOriginalSetupBudget_polynomial`
   combines conversion, matching profiles, metadata copying and cleanup into
   one fixed degree-six majorant; its guarded check passed at about 2.67 GiB.
   `canonicalRouterStageSetupBudget_polynomial` now gives a degree-six
   bound, and `canonicalRouterDirectionalSetupBudget_polynomial` gives a
   degree-seven bound for actual directional setup. Generic coefficient
   definitions keep concrete tape-count arithmetic out of kernel comparisons;
   the complete file passed at about 2.62 GiB.
   `canonicalRouterPlacementDimensionOverhead_eq` identifies actual placement
   setup with an abstract-bank scalar ledger, and
   `canonicalRouterPlacementDimensionOverhead_polynomial` bounds it quadratically.
   The guarded file check passed at about 2.62 GiB.
   `liveCoordinateProfilesCost_uniform_cube` now proves a structural cubic
   bound for arbitrary uniform coordinate/profile widths, instantiated by
   `canonicalCoordinateProfilesCost_polynomial` at canonical routing geometry.
   `uniformBackendBudget_le_cube` bounds both descriptor backends;
   `canonicalLiveRepairOverhead_polynomial` includes complete canonical repair
   setup. `canonicalRouterGeneratedScalarOverhead_polynomial` combines masks,
   profiles, scalar conversion, repair and cleanup into one cubic bound for
   the actual generated residue scalar ledger. The guarded file check passed
   at about 2.69 GiB.
   `canonicalRouterStageDimensionOverhead_polynomial` combines generated work
   and both placements cubically. `canonicalPermutationDimensionCost_eq`
   identifies the complete eighteen-pass real setup price with an integer
   ledger; `canonicalPermutationDimensionBudget_polynomial` bounds that ledger
   by a fixed degree-seven polynomial. The guarded check passed at about 2.69 GiB.
   `CanonicalRouterDimensionAbsorption` now absorbs repeated complete setup
   into total routed volume, uniformly in row count and positive payload width,
   beyond one fixed dimension threshold. Its guarded check passed at about 2.50 GiB.
   `CanonicalRowDriverAbsorbed.canonicalRowDriver_global_absorbed_exec` now
   applies this bound to actual restored-bank global row execution; no separate
   repeated dimension-cost term remains. The guarded check passed at about 2.51 GiB.
   This remains the large-dimension, long-record, supplied-metadata case. Small
   dimensions, executed short-record fallback and compact-input metadata/count
   production remain open; R3 and kappa are unchanged. The complete chunk
   passed the full guarded root build (15,323 jobs, peak 4.5 GiB) and the
   axiom audit (351,964 declarations, peak 4429.6 MiB).
   `BinaryCounterScope.binaryCounterScope_exec` now executes binary-to-unary
   conversion, an exactly framed call and unary-counter erasure, restoring the
   binary source and all scratch with additive price `8 * value + 11 * width + 8`.
   Its guarded check passed at about 1.17 GiB.
   `CanonicalRowDriverBinaryCount.canonicalRowDriver_binary_count_exec` now
   applies that scope to actual global routing: the outer row count starts in
   binary and its unary tape starts and ends blank. The exact global permutation,
   unread suffix and all nonstream registers are preserved by the existing
   endpoint contract; the conversion/erasure price is added once to total cost.
   Its guarded check passed at about 2.51 GiB.
   `CanonicalRowDriverBinaryCounters.canonicalRowDriver_binary_counters_exec`
   now generates and erases both unary driver tapes from binary row count and
   binary row length, with the exact same global endpoint contract.
   `BinaryScaleScope.binaryScaleScope_exec` prices shifted binary copying,
   a framed call and erasure by `8 * (dimension + payloadBits) + 14`.
   `CanonicalRowDriverScaledWidth.canonicalRowDriver_scaled_width_exec` uses
   actual scaling to calculate the row length from payload width and unary dimension.
   `CanonicalRowDriverCompactCounters.canonicalRowDriver_compact_counters_exec`
   now starts with only binary dimension, binary payload width and binary row count
   for the outer counters. The dimension counter, scaled binary row-length word,
   unary row count and unary row width all start and end blank; the three binary
   inputs and all scratch restore, and every generation/cleanup phase is charged.
   The final caller passed its guarded check at about 2.52 GiB; the generic scaling
   scope passed at about 1.16 GiB. Metadata generation, small dimensions and
   short records remain open. The complete counter pipeline passed the full
   guarded root build (15,329 jobs, peak 4.5 GiB) and axiom audit (351,977
   declarations, peak 4430.0 MiB). R3 and kappa remain unchanged.
   `DelimitedBankCopy.delimitedBankCopy_exec` now executes the inverse-format
   serialization needed by metadata-bank loaders: a fixed register list is copied
   into consecutive delimited words, with arbitrary destination suffix preserved,
   every source restored and both scratch tapes blank again. Repeated sources are
   allowed; code depends only on register locations, never word data. Its exact
   price is six times encoded frame length plus register count plus one.
   `FramedCoreCopy.framedCoreCopy_exec` instantiates this encoder at the fixed
   nonstream core register list. `framedCoreCopyCost_le` bounds serialization
   linearly in the uniform bank size; live payload is excluded. Guarded checks
   passed at about 1.17 GiB and 1.15 GiB respectively. These encode an already
   generated bank; calculating canonical permutation/matching fields from compact
   inputs remains open. The encoder additions have not yet had a full root build
   and axiom audit, and are being held for a larger metadata-generation chunk.
   `PermutationTableIterate.permutationTableIterate_exec` now executes any
   counted iterate of an arbitrary coordinate map from its compact key/value table,
   reusing `matchingTableLookupInPlace_exec` and the existing priced symbol loop.
   Only the query changes to the requested function iterate: the table, unary
   iteration counter, table archive, loop archive and lookup scratch restore.
   The proved bound is `iterations * (N * (30 * L + 39) + 10 * L + 19) + 4`;
   the program contains no coordinate-map data or unrolled iteration count.
   Its guarded check passed at about 2.46 GiB. This supplies executed bounded
   orbit traversal for cycle-reflection generation, but orbit minima, return
   exponents, reflection table production and complete canonical frame generation
   remain open. No full root build or axiom audit yet for this metadata chunk.
   `BinaryMinimum.binaryMinimum_exec` now executes a running binary minimum
   update in at most `16 * L + 17` steps, preserving its input coordinate and
   all comparison/copy scratch. `PermutationOrbitMinimum.permutationOrbitMinimum_eq_base`
   proves that scanning one full coordinate count gives exactly the existing
   `permutationBase`, including fixed points and shorter cycles; the invariant
   records both a visited iterate and a lower bound on all visited coordinates.
   `PermutationOrbitStep.permutationOrbitStep_exec` composes actual table lookup
   and minimum update in at most `N * (30 * L + 39) + 26 * L + 31` steps,
   changing only query and minimum. The minimum primitive and invariant checked
   at about 1.15 GiB and 0.84 GiB; the executed step checked at about 2.46 GiB.
   Counted scan composition, reflection exponents/table generation and complete
   canonical metadata calculation remain open. These additions remain in the
   pending metadata chunk, without a full root build or axiom audit yet.
   `PermutationOrbitScan.permutationOrbitScan_exec` now composes the lookup/minimum
   step with the existing priced symbol loop, restoring its complete arbitrary
   counter word and archive. Only query and running minimum change, at price
   `iterations * (N * (30 * L + 39) + 26 * L + 36) + 4`.
   `permutationBaseScan_exec` initializes a blank minimum register from the live
   query and executes exactly one full coordinate-count scan to compute the
   existing `permutationBase`. No orbit data or semantic execution premise is
   supplied; the exact final query is also tracked, and the table and all scratch
   restore. Its guarded check passed at about 2.48 GiB. Reflection exponents,
   reflection table production and full canonical metadata generation remain open.
   The accumulated metadata serialization and orbit/base-scan chunk passed the
   full guarded root build (15,336 jobs, peak 4.5 GiB) and axiom audit (352,035
   declarations, peak 4430.4 MiB). The constant-price loop identity is shared by
   traversal and minimum scanning. This supersedes the pending verification notes
   above; R3 and kappa remain unchanged.
   `PermutationReturn.boundedReturnSteps` now specifies a bounded search that
   freezes on reaching its target. Its checked recurrence supports one machine
   step per outer iteration, and `boundedReturnSteps_reaches` proves success
   whenever a target occurs within the fuel bound. `permutationReturn_reaches_base`
   supplies that witness within one full coordinate count.
   `permutationReflection_of_return` proves that reusing any forward return count
   from a query to its cycle base, starting at the base, computes exactly the
   existing canonical reflection. This avoids executing an unbounded exponent search.
   The guarded file check passed at about 0.84 GiB.
   `PermutationReturnStep.permutationReturnStep_exec` now executes equality testing,
   conditionally advances through the preserved table and appends exactly one unary
   marker per real advance. Once at the target it changes no registers. The bound
   is `N * (30 * L + 39) + 18 * L + 24`; its check passed at about 2.45 GiB.
   Counted bounded-search composition, reflected-coordinate execution, table production
   and full canonical metadata generation remain open. These return-search additions
   are uncommitted and have not yet had a full root build or axiom audit.
   `PermutationReturnScan.permutationReturnScan_exec` now composes the bounded
   search using the existing priced symbol loop. It generates exactly the unary
   `boundedReturnSteps` word, tracks the final query, and restores its arbitrary
   fuel tape, table and scratch. The guarded check passed at about 2.47 GiB.
   `PermutationReflectionExec.permutationReflection_exec` now executes canonical
   reflection from a live permutation table and supplied cycle base: bounded
   return search generates the unary count, a second actual table traversal reuses
   that count, and final erasure restores the counter. Only the query changes;
   the table, target base, fuel, archives and scratch restore exactly. Its bound
   is `N * (2 * N * (30 * L + 39) + 28 * L + 50) + 10`; the guarded check passed
   at about 2.47 GiB. Composing this with base generation to remove the supplied
   base, generating the complete reflection tables, and canonical metadata assembly
   remain open. The return/reflection chunk has not yet had a full root build or
   axiom audit and is being held for a larger standalone commit.
   `PermutationReflectionGenerate.permutationReflectionGenerate_exec` now removes
   the supplied-base premise entirely. It saves the original query, computes the
   canonical base with the actual orbit scan, restores the query, executes bounded
   return/reflection generation and erases the base. Only the query changes; base,
   saved query, return count, archives and all scratch start/end blank, and the
   compact permutation table and arbitrary coordinate-count fuel word restore.
   The price is `N * (3 * N * (30 * L + 39) + 54 * L + 86) + 24 * L + 38`.
   `PermutationMatchingGenerate.permutationSecondMatchingGenerate_exec` composes
   one further table lookup to compute `f (permutationReflection f query)`, with
   the same exact frame and explicit polynomial price. Thus both coordinate maps
   from `permutation_two_matchings` now have executed generators from the compact
   permutation table, with no supplied orbit/base/return information. Guarded checks
   passed at about 2.47 GiB and 2.46 GiB respectively. Enumerating all coordinates
   into complete matching tables and assembling canonical metadata remain open;
   R3 and kappa are unchanged. The accumulated return/reflection chunk passed
   the full guarded root build (15,342 jobs, peak 4.5 GiB) and axiom audit
   (352,067 declarations, peak 4432.8 MiB), superseding the pending verification
   notes above.
   `MatchingEntryEmit.matchingEntryEmit_exec` now wraps a framed coordinate
   generator with actual key/value emission in the existing matching-table format.
   It saves the original query, copies both delimited fields through the checked
   bank encoder, reverse-accumulates the complete entry, restores the query and
   erases temporary frame/index words. The additional price is `32 * L + 37`.
   `matchingEntryEmit_fold_reverse` proves that final accumulator rewind gives
   exactly `matchingEntryWords` in chronological coordinate order, preserving
   both delimiters. The guarded check passed at about 2.47 GiB without raised
   proof limits. This wrapper still takes the coordinate-call contract; its
   instantiation with the checked matching generators and complete counted table
   enumeration remain open. This new emission work is uncommitted and has not
   yet had the full root build or axiom audit.
   `PermutationMatchingEntry.permutationMatchingEntry_exec` now discharges the
   emitter's coordinate-call contract with actual canonical reflection/second-map
   generation, for either matching choice. Only the reverse entry accumulator
   changes: the original query and every generated base/count/index/frame restore.
   No orbit, matching value or coordinate execution oracle is supplied.
   `permutationMatchingEntryAdvance_exec` adds the actual fixed-width cursor
   increment needed by table enumeration. Its bound is
   `N * (3 * N * (30 * L + 39) + 84 * L + 125) + 70 * L + 94` per emitted entry.
   Both passed the guarded file check at about 2.47 GiB. The remaining table gate
   is composing this step over all coordinates with the counted loop and final
   accumulator rewind. Entry emission/advance remains uncommitted pending that
   larger chunk and its full root build/axiom audit.
   `PermutationMatchingTable.permutationMatchingTable_exec` now executes the
   entry/advance step uniformly across every coordinate using the existing
   priced symbol loop. It restores both independent unary count/fuel words and
   their archives, tracks an exact ascending-key prefix, and rewinds the complete
   reverse accumulator into the matching-table format consumed by lookup.
   `BinaryReset.binaryReset_exec` resets a binary word at its existing width in
   exactly `14 * L + 14` steps with all scratch restored.
   `permutationMatchingTableClosed_exec` uses this reset to restore the cursor:
   only the output table changes, for either canonical matching map. The compact
   permutation input, original zero cursor, both counters, base, return count,
   saved indices, frame accumulator and lookup scratch all restore exactly.
   Its bound is `N * (N * (3 * N * (30 * L + 39) + 84 * L + 125) + 74 * L + 103)
   + 14 * L + 20`. The guarded file check passed at about 2.49 GiB; reset checked
   at about 1.15 GiB. Initial binary-zero cursor and the two unary coordinate-count
   tapes are still supplied at this interface. Generating those inputs, arranging
   both completed tables for the canonical metadata compiler, and full metadata
   assembly remain open. R3 and kappa are unchanged. The complete entry/table
   chunk passed the full guarded root build (15,346 jobs, peak 4.5 GiB) and
   axiom audit (352,086 declarations, peak 4433.5 MiB), superseding the pending
   verification notes above.
   `BinaryZeroScope.binaryZeroScope_exec` now generates and erases a zero word
   at the width of a preserved source, with additive cost `6 * L + 6` and no
   unary width input. `PermutationMatchingTableInput.permutationMatchingTableInput_exec`
   applies this to actual table generation; the cursor now starts/ends blank.
   `BinaryCounterPairScope.binaryCounterPairScope_exec` generates and erases two
   independent unary counters from one preserved binary operand.
   `PermutationMatchingTableBinary.permutationMatchingTableBinary_exec` composes
   both scopes: complete canonical matching tables now generate from a binary
   dimension and the compact permutation table alone. Only the output table changes;
   cursor, both coordinate-count tapes, bases, return counts, archives and every
   scratch register start/end blank. The guarded check passed at about 2.47 GiB.
   Its reusable cost is `N * (N * (3 * N * (30 * L + 39) + 84 * L + 125)
   + 74 * L + 119) + 42 * L + 42`.
   `PermutationMatchingTableCost.permutationMatchingTableBinaryCost_le_fourth`
   proves the actual cost is at most `693 * (n + 1)^4` for compact dimension
   widths bounded by `n + 1`. The eventual volume-absorption theorem pays this
   even when repeated per row, uniformly in row count and positive payload width.
   Its guarded check passed at about 2.45 GiB. This supersedes the supplied
   cursor/count gate above. Feeding generated matching tables into the canonical
   metadata compiler and complete metadata assembly remain open, as do small
   dimensions and short records; R3 and kappa are unchanged. This binary-input
   compiler chunk passed the full guarded root build (15,351 jobs, peak 4.4 GiB)
   and axiom audit (352,100 declarations, peak 4432.5 MiB).
   `PermutationReservoirTable.permutationReservoirTable_exec` now feeds the actual
   generated original matching into the existing fixed-bank reservoir-class/local
   converter. It proves the generated input establishes that converter's bank,
   executes the embedded conversion and erases the original matching table.
   Only the local matching-table output changes. The two generated matching maps'
   involution proofs come from `permutation_two_matchings`; scalar reservoir inputs
   remain explicit in the initial bank. The guarded check passed at about 2.46 GiB.
   Connecting local tables to the canonical profile/metadata bank, generating
   remaining scalar fields and assembling the complete metadata frame remain open.
   `PermutationReservoirProfile.permutationReservoirProfile_exec` now composes
   the generated original matching, actual reservoir-class/local conversion and
   actual full profile compiler, erasing both generated tables. The local coordinate
   cast is transported through `matchingMateCoordinate_cast`; profile input readiness
   is proved from the generated table and the explicit register join. Only the
   profile output changes, and every phase has its actual cost. Scalar reservoir
   bank and profile controls remain explicit pure readiness inputs. The guarded
   check passed at about 2.46 GiB. The unused direct-original-profile wrapper was
   removed before committing; the canonical router needs this localized path.
   These compiler-connection additions are uncommitted and have not yet had the
   full root build or axiom audit; R3 and kappa remain unchanged.
   `CoordinateExchangeFrame.coordinateExchangeFrame_exec` now computes both
   interval endpoints from live binary starts/span, emits the exact four-field
   delimited exchange frame and erases the endpoints in exactly `44 * L + 49`
   steps. Input operands and arithmetic/copy scratch restore; only the frame
   destination changes, preserving any suffix. The guarded check passed at
   about 2.40 GiB.
   `CoordinateExchangeFrameSchedule.middleLookupMetadata_generate_exec` now
   composes three such encoders into the exact forward/backward
   `middleLookupMetadata` words already consumed by reservoir conversion.
   The fixed three-stage programs are independent of dimension and payload;
   their exact cost is `132 * L + 148`, and all operands/scratch restore.
   The guarded check passed at about 2.46 GiB. Per-exchange binary starts/spans
   are still supplied; deriving those from compact dimension/reservoir inputs,
   completing scalar bank setup and full canonical frame assembly remain open.
   The accumulated compiler/metadata-frame chunk passed the full guarded root
   build (15,355 jobs, peak 5.0 GiB) and axiom audit (352,131 declarations,
   peak 4432.7 MiB), superseding the pending verification notes above.
   R3 and kappa remain unchanged.
   `BinaryFixedScale.binaryDoubleCopy_exec` now copies and doubles a padded
   binary operand in exactly `10 * L + 14` steps, preserving its source and
   both scratch tapes. The guarded file check passed at about 1.16 GiB.
   `ReservoirScalarMultiples.reservoirScalarMultiples_exec` now generates twice,
   three times and six times the reservoir width from one live padded binary
   input in exactly `28 * L + 36` steps. Only the three declared scalar outputs
   change; the input and every scratch register restore. The guarded check passed
   at about 1.16 GiB. Remaining starts/spans require compact-dimension subtraction
   and the final exchange-operand/frame assembly. These scalar additions are
   uncommitted and have not yet had the full root build or axiom audit.
   `ReservoirIntervalScalars.reservoirIntervalScalars_exec` now derives doubled
   span, dimension minus doubled span, dimension minus span and a padded zero
   from the two live binary inputs. Its exact cost is `30 * L + 34`; only the
   four scalar destinations change, and all arithmetic scratch restores. Its
   guarded check passed at about 1.16 GiB. Reservoir multiples were simplified
   to reuse the doubled value in the triple addition, removing duplicate
   arithmetic and the unused standalone fixed-triple helper. Exchange-operand
   placement, metadata-frame assembly and generated-scalar cleanup remain next;
   these scalar changes are being held for that larger standalone chunk.

6. Compose the full arbitrary-coordinate router and audit its total cost and
   exact restored-bank contract. R3 remains open until all these gates pass.

The older Balanced design's rotation counts and minimal parameter choices are
historical; use the proved R1 schedule and the reservoir-compatible spacing above.
Raw descriptor/header generation, sparse-profile compilation, physical placement
and short-record fallback remain R3. Layout/support integration
remains R4. Completing R2 does not change the current multiplication kappa.

Generated exchange operands checkpoint: `ReservoirExchangeOperands` now executes
all starts/spans needed by the three reservoir exchanges from binary `n`, `H`
and `w`, including distinct copies required by frame-register separation, in
exactly `82 * L + 94` steps. `ReservoirExchangeOperandFrames` proves the fixed
placements injective, identifies every generated start/span with the existing
exchange specification, and proves frame scratch remains blank. The operand
build passed (2.9 GiB combined peak); the final frame-readiness check passed
(2547.4 MiB). `ReservoirMetadataGenerate.reservoirMetadata_generate_exec` composes operand
generation, the three frame encoders and cleanup into the exact forward or
backward metadata from binary `n`, `H`, `w`. Only the metadata destination
changes, preserving its arbitrary suffix; all generated operands and scratch
restore. The exact total cost is `236 * L + 265`. Its guarded check passed
(2539.7 MiB). Remaining scalar/control bank production, canonical assembly
and the other R3 gates remain open. No kappa change.
The full guarded root build passed (15,361 jobs, 4.5 GiB combined peak);
The root axiom audit passed for 352,194 declarations (4437.3 MiB peak).
These checks supersede the pending verification notes for the scalar additions above.

`ReservoirProductionScalars.reservoirProductionScalars_exec` extends the generated
operand bank with `n - 3*w`, reusing `n - 2*w` and the original span. Its exact
cost is `90 * L + 102`; source inputs and scratch restore. The guarded check
passed at 2526.0 MiB. `ReservoirMetadataPair.reservoirMetadataPair_exec` generates
both forward and backward exchange words on one reusable scratch bank in exactly
`472 * L + 530` steps. Only the two output words change, preserving arbitrary
suffixes; the guarded check passed at 2522.3 MiB. These additions await the
larger scalar-bank assembly chunk before commit and full root verification.
Complete reservoir-class bank preparation and canonical assembly remain open;
R3 and kappa are unchanged.

`ReservoirScalarExport.reservoirScalarExport_exec` now copies the six generated
scalar inputs (two zeros, span, surviving dimension, triple and sextuple reservoir
width) into separate converter destinations using the structural metadata installer.
Only those six outputs change; source and scratch tapes restore, with total cost
at most `36 * L + 43`. The guarded check passed at 1189.3 MiB.
`reservoirProductionScalars_clean` proves that erasing the surviving dimension
and all exchange operands restores the original bank (guarded check 2518.8 MiB).
Execution composition of scalar generation/export/cleanup and the final physical
placement with both metadata outputs remain next. This is uncommitted work;
full R3 acceptance and kappa remain unchanged.

`ReservoirScalarPrepare.reservoirScalarPrepare_exec` now composes actual scalar
generation, six-output export and complete generated-operand cleanup. From
binary dimension, reservoir width and span it produces exactly the six converter
scalar inputs, changing only their destinations and restoring all production
scratch and input tapes. The total step bound is `150 * L + 170`, including
cleanup bounded structurally by `24 * L + 25`. The guarded check passed at
2545.2 MiB. This closes the scalar execution-composition item above; joining
both metadata words to the converter's physical bank and then connecting the
matching-table producer remain open. The chunk remains uncommitted pending
that assembly; R3 and kappa are unchanged.

`ReservoirBankPrepare.reservoirBankPrepare_exec` now joins both metadata directions
and complete scalar setup on a shared production bank. Only the eight converter
input fields change, with total cost at most `622 * L + 700`; all production
scratch and compact input tapes restore. The guarded check passed at 2518.6 MiB.
`ReservoirBankPlacement.reservoirBankPrepared_classLocal` proves the fixed
78-register placement supplies exactly the existing 57-register class/local
converter bank, with only its original matching-table field left blank for the
separate executed table producer. Placement injectivity and the exact bank
identity passed at 2597.6 MiB. This closes the scalar/metadata assembly items
above. Connecting this executed setup to matching-table production/conversion,
erasing the eight generated converter inputs after use, and generating the
remaining profile controls/canonical frame are still open; full R3 and kappa
remain unchanged. The accumulated bank-setup chunk passed the full guarded
root build (15,367 jobs, 4.5 GiB combined peak) and root axiom audit
(352,253 declarations, 4433.9 MiB peak), superseding the pending verification
and uncommitted-status notes above.

`ReservoirBankClean` now executes complete eight-field converter-input cleanup
in exactly `60 * L + 65` steps, proving restoration of the original bank.
Its guarded check passed at 2537.9 MiB. `ReservoirPreparedClassTable` composes
actual setup, embedded class/local conversion and cleanup, preserving the original
matching table and changing only local-table output. Its cost is bounded by the
existing conversion cost plus `682 * L + 765`; the guarded check passed at
2531.2 MiB. `PermutationReservoirTable` now connects actual canonical
matching-table generation from the compact original permutation to this generated
setup/conversion, then erases the original generated matching table. Every
register except local-table output restores. No scalar bank or exchange metadata
is supplied; the binary dimension/reservoir/span inputs and original permutation
table remain explicit. Its guarded check passed at 2522.1 MiB. Connecting this
version to profile compilation, generating the remaining profile controls and
assembling the canonical frame remain open, along with all other R3 gates.
These changes remain uncommitted pending that larger compiler chunk and full
root verification; R3 and kappa are unchanged.

`PermutationReservoirProfile.permutationReservoirProfile_exec` now uses the
generated-bank table producer: canonical matching generation, compact-input
reservoir setup/conversion, full profile compilation, and both intermediate-table
erasures execute in one proof. Only profile output changes. The setup/conversion
cost adds `682 * (Li + Lk) + 765` to the previous explicit compiler ledger.
The supplied-bank wrappers were replaced in place after confirming they had no
other callers, rather than retaining duplicate execution paths. The updated table
and profile modules passed their guarded build (2.8 GiB combined peak).
`MatchingProductionSetup` still supplies the binary prefix byte count, stride,
residue and pure scratch/register readiness; generating those controls and the
full canonical frame remains open. The accumulated compiler/cleanup chunk passed the full guarded root build
(15,369 jobs, 4.4 GiB combined peak) and root axiom audit (352,265 declarations,
4434.6 MiB peak), superseding the pending verification notes above.
R3 and kappa are unchanged.

`MatchingEntryWidth.matchingEntryWidth_exec` derives the matching-entry byte
width `2*L+2` from binary `L`, erasing its successor temporary in exactly
`22 * Le + 27` steps (guarded check 1181.2 MiB). `MatchingPrefixCount` executes
two binary multiplications to form row count times stride times entry width,
erasing the intermediate slot count (guarded check 1194.0 MiB).
`MatchingPrefixCountFromWidth.matchingPrefixCountFromWidth_exec` composes these
operations from binary rows, stride and coordinate width; only the prefix-count
output changes. Its cost is at most `matchingPrefixCountCost Ln Lk Le + 24*Le+29`.
`matchingPrefixCountScope_exec` additionally proves a framed compiler call can
borrow the generated count and then erase it, restoring every tape except the
call output. The combined guarded check passed at 1202.3 MiB. Instantiating this
scope with the actual profile compiler and generating its stride/residue controls
remain open. These additions are uncommitted pending that integration; R3 and
kappa remain unchanged.

`MatchingProfileGeneratedCount.matchingProfileGeneratedCount_exec` now instantiates
the generated-count scope with actual full-table profile compilation. A common
`MatchingProductionFrame` carries layout, matching input, stride/residue and
scratch readiness without a supplied prefix count or count-fit hypothesis.
`MatchingProductionFrame.with_count` derives the ready producer after the actual
count is installed; the count-fit inequality follows from the compact operand
bounds. Only profile output changes after count cleanup, with the explicit
arithmetic/compiler/cleanup ledger. The guarded check passed at 2511.9 MiB.
`MatchingProductionSetup` now extends this shared frame, preserving existing
ready-count callers; its fixed-layout constructor was adjusted for inherited-field
proof ordering. Connecting the generated-count version into the permutation/
reservoir profile wrapper and producing stride/residue controls remain next.
This count/compiler chunk is uncommitted and awaits full-root verification;
R3 and kappa remain unchanged.

`PermutationReservoirProfile.permutationReservoirProfile_exec` now calls the
generated-count profile compiler in place. Its readiness input is the count-free
`MatchingProductionFrame`; binary rows, stride and coordinate width generate
the prefix byte count, and all count arithmetic scratch and the count itself
restore. The local matching table is still generated, consumed and erased by
the full pipeline; only profile output changes. The explicit ledger now includes
count generation and cleanup. The guarded check passed at 2535.2 MiB.
This closes the count-wrapper integration items above. Compact stride/residue
production, canonical-frame assembly and the remaining R3 gates stay open.
The accumulated count/compiler chunk passed the full guarded root build
(15,373 jobs, 7.4 GiB combined peak) and root axiom audit (352,324 declarations,
4434.5 MiB peak), superseding the pending verification and uncommitted-status
notes above. R3 and kappa remain unchanged.

`MatchingControlScope` now installs compact binary stride/residue words into
the compiler bank and erases them after a framed call. Inputs and scratch
restore; the full install/cleanup overhead is at most `16 * Lk + 20` (guarded
check 1190.8 MiB). `MatchingProfileCompactControls` instantiates this scope with
the actual generated-count profile compiler and derives both installed-word
readiness facts from the execution output (guarded check 2498.2 MiB).
`PermutationReservoirProfile.permutationReservoirProfile_exec` now uses this
version in place: generated matching/local tables, reservoir metadata/scalars,
prefix count and installed stride/residue controls all restore; only profile
output changes. Its guarded check passed at 2538.3 MiB. The compact binary
values themselves remain inputs. Deriving canonical geometry from dimension
and gap/stride, iterating residues and assembling the complete canonical frame
remain open; this does not close R3. These changes are uncommitted pending a
larger assembly chunk and full-root verification; kappa is unchanged.

`RouterGeometryDivisor.routerGeometryDivisor_exec` now generates `K + 3*G`
from binary stride and gap, erasing doubled/tripled gap temporaries in exactly
`30 * L + 34` steps (guarded check 1200.2 MiB).
`RouterGeometryDigits.routerGeometryDigits_exec` composes this with actual
`n-K` subtraction and division, producing exactly `routerDigits n K G` and
`(n-K) % (K+3*G)`. Only those two outputs change; numerator, divisor and
all arithmetic scratch restore. Its total bound is `12*L*L + 97*L + 82`, and
the guarded check passed at 1228.8 MiB. Binary dimension/stride/gap remain
compact inputs with explicit fit and positivity bounds. Borrowed-width and
tail generation, canonical gap/stride derivation, residue iteration and complete
frame assembly remain open. This geometry work is being grouped with the
uncommitted compact-control chunk; no R3 completion or kappa change is claimed.

`RouterGeometryDigitTail.routerGeometryDigitTail_exec` now composes digit/remainder
generation with the exact tail addition and erases the division remainder.
Only digit count and `routerTail n K G` change; its total bound is
`12*L*L + 107*L + 92` (guarded check 1198.2 MiB).
`BinaryLowCopy` specializes the existing executed binary prefix extractor to
fixed-width low-bit copying, preserving its wide source and scratch (1667.8 MiB).
`RouterBorrowedWidth.routerBorrowedWidth_exec` multiplies a generated digit count
by the gap, exports the required padded `routerBorrowed n K G` word using a
compact binary width operand, and erases the wide multiplication result. Only
borrowed-span output changes, with an explicit quadratic arithmetic/prefix-copy
bound (guarded check 1712.0 MiB). Composing digit/tail and borrowed-span producers
into one geometry bank, deriving the canonical gap/stride and residue-dependent
parameters, and full frame assembly remain open. This work remains uncommitted
with the compact-control chunk; R3 and kappa are unchanged.

`RouterGeometryGenerate.routerGeometryGenerate_exec` now composes actual digit/tail
production and fixed-width borrowed-span multiplication on one shared bank.
From compact binary dimension, stride, gap and word width, only the three
geometry outputs change; all input words and arithmetic/prefix-copy scratch
restore. Its total bound is `36*L*L + 177*L + 136 + M*(4*L+11)`; the guarded
check passed at 1707.9 MiB. This closes the common geometry-bank composition
item above. Canonical reservoir-width derivation (a second division using
`(n/(64*G)+1)*G`), gap/stride generation, residue-dependent tail subtraction,
residue iteration and complete canonical-frame assembly remain open, as do
all other R3 gates. The accumulated compact-control/common-geometry chunk passed the full guarded
root build (15,381 jobs, 4.5 GiB combined peak) and root axiom audit
(352,362 declarations, 4435.2 MiB peak), superseding the pending verification
and uncommitted-status notes above. Kappa remains unchanged.

`BinaryWordWidth.binaryWordWidth_exec` now counts a preserved tape's length
into a binary word, generating and erasing its own width reference. Only the
width output changes, at cost at most `4*L*L + 22*L + 16` (1192.3 MiB).
`RouterGeometryCompact.routerGeometryCompact_exec` uses this to remove the
supplied width operand from common geometry production, then erases that word.
Only digit count, tail and borrowed span change; total cost is at most
`44*L*L + 212*L + 154` (guarded check 1709.3 MiB).
The fixed-width multiplication proof was factored into `BinaryProductLowCopy`
and reused by the unchanged borrowed-width contract. `ReservoirWidthGenerate`
now executes division, quotient increment, fixed-width multiplication and cleanup
to produce `(n/K+1)*G`. `routingReservoirWidth_generate_exec` specializes
`K=64*G` and identifies the exact existing `routingReservoirWidth n G` word.
All inputs and scratch restore; only reservoir-width output changes. Its bound
is `36*L*L + 133*L + 89 + M*(4*L+11)` (generic guarded check 1717.8 MiB).
Joining reservoir width to the generated common geometry bank, canonical gap/
stride derivation, residue-dependent geometry and full frame assembly remain
open. These changes are uncommitted pending the larger geometry assembly and
full-root verification; R3 and kappa remain unchanged.

`RouterReservoirGeometry.routerReservoirGeometry_exec` now shares one generated
word-width operand and scratch bank across common geometry and canonical
reservoir-width production. From binary dimension, chosen stride `64*G` and
gap it changes exactly digit count, terminal tail, borrowed span and reservoir
width, with bound `84*L*L + 356*L + 243`. Exact bank reads, preservation outside
those four outputs and cleanup are proved; cleanup costs exactly `8*L+9`.
`routerReservoirGeometryScope_exec` additionally composes setup, a framed call
and complete geometry erasure, restoring every tape except call output, with
setup/cleanup overhead bounded by `84*L*L + 364*L + 252`.
The standalone bank/read/cleanup check passed at 1734.8 MiB. The compact binary
gap and its chosen stride remain inputs. Canonical gap/stride generation,
residue-dependent geometry, connection around full profile compilation and
canonical-frame assembly remain open; full R3 and kappa remain unchanged.
The accumulated width/reservoir geometry chunk passed the full guarded root
build (15,386 jobs, 4.5 GiB combined peak) and root axiom audit
(352,401 declarations, 4438.2 MiB peak), superseding the pending verification
and uncommitted-status notes above. The complete setup/call/cleanup check
passed at 1736.6 MiB.

`BinaryCeilLogData.canonicalBinary_length_clog` identifies canonical bit length
with the ceiling logarithm of one more than the represented value, including
zero (guarded check 1162.8 MiB). `BinaryCeilLog.binaryCeilLog_exec` now executes
`clog 2 (n+2)` from the preserved binary dimension: copy with one extra high bit,
increment, canonicalize, count the remaining bits, and erase that temporary.
Only the logarithm output changes; total cost is at most `4*L*L + 34*L + 48`
(guarded check 1201.7 MiB). `BinaryShiftBits` supplies a structural executed
fixed-bit shift circuit and width-derived literal construction, for the gap's
constant six and the fixed power-of-two stride scaling (1190.6 MiB).
Composing these into actual canonical gap/stride production remains next;
residue-dependent geometry, profile/frame connection and all other R3 gates
remain open. This logarithm/control chunk is uncommitted pending that composition
and full-root verification; R3 and kappa remain unchanged.

`CanonicalGapGenerate.canonicalGapGenerate_exec` now generates the exact
`canonicalRouterGap n` word from dimension, using the executed logarithm,
two shifts, a width-derived constant six and addition; logarithm, scaled value
and constant are erased. Its bound is `4*L*L + 78*L + 115` (2568.8 MiB).
`CanonicalStrideGenerate` preserves that gap and produces `canonicalRouterStride n`
by six fixed shifts, with total bound `4*L*L + 108*L + 170` (2549.1 MiB).
`CanonicalGeometryGenerate.canonicalGeometryGenerate_exec` composes these with
shared geometry/reservoir production. From only binary dimension it produces
the six exact canonical controls: gap, stride, digits, tail, borrowed span and
reservoir width. Input and all other scratch restore, with total bound
`88*L*L + 464*L + 413`. The framed `canonicalGeometryScope_exec` additionally
erases all six outputs after use; cleanup costs exactly `12*L+13`, so the
setup/cleanup overhead is at most `88*L*L + 476*L + 426`. The combined guarded
check passed at 2571.6 MiB. Explicit large-dimension and scalar-fit hypotheses
remain; residue-dependent geometry, actual profile/frame integration, complete
frame generation, small dimensions and short-record fallback are still R3 gates.
The accumulated logarithm/gap/stride/geometry chunk passed the full guarded
root build (15,392 jobs, 4.5 GiB combined peak) and root axiom audit
(352,447 declarations, 4436.9 MiB peak), superseding the pending verification
and uncommitted-status notes above. R3 and kappa remain unchanged.

`RouterResidueTail.routerResidueTail_exec` now subtracts the live binary residue
from the common terminal tail, producing exactly the `.m` field of
`routerProfileParameters`; the natural subtraction is justified by the residue
bound and common geometry. Only terminal output changes, in `8*L+8` steps
(guarded check 1188.6 MiB). `CanonicalResidueGeometry` composes this with the
actual dimension-only canonical geometry producer. From binary dimension and
current residue it produces all common geometry plus the residue-specific
terminal length, preserving both inputs and every other scratch register; its
bound is `88*L*L + 472*L + 421` (2556.0 MiB).
`canonicalResidueGeometry_parameters` identifies actual binary words for all
five profile parameters `K`, residue, digit count, gap and terminal length.
Residue iteration, canonical descriptor-width generation/operand resizing,
actual profile/frame integration, complete frame generation and the other R3
gates remain open. This residue-geometry chunk is uncommitted pending larger
assembly and full-root verification; R3 and kappa remain unchanged.

`BinaryScalarWidth.binaryScalarWidth_exec` now generates exact `clog 2 (x+1)`
from any preserved padded operand, including zero, with bound
`4*L*L + 26*L + 22` and complete temporary cleanup (1197.5 MiB).
`CanonicalDescriptorMagnitude` collapses the eleven-mode magnitude to scalar
maxima and proves that canonical routing geometry reduces it exactly to
`n - borrowedSpan + 1`. Consequently every residue shares the same descriptor
base width `W = clog 2 (n - borrowedSpan + 2)`: index width `W+1`, group/stride
width `W`, selector width `2*W+1`, and width-counter bits equal the canonical
scalar width of `2*W+1`. The numeric coordinate-width operand is bounded by the
canonical gap, providing a uniform fit bound without a new asymptotic gate.
`CanonicalDescriptorBase.canonicalDescriptorStrideWidth_exec` executes that
shared base-width calculation and identifies the result with the existing
canonical stage interface. It subtracts the borrowed span, executes the ceiling
logarithm and erases the subtraction word, changing only base-width output,
in at most `4*L*L + 44*L + 58` steps. Base and magnitude modules passed their
guarded build (2.9 GiB combined peak); the standalone base check before the
interface specialization passed at 2557.5 MiB.
Executing the remaining width formulas and operand resizing, residue iteration,
full profile/frame integration and the remaining R3 gates are open. This work
is grouped with the uncommitted residue-geometry chunk; kappa is unchanged.

`CanonicalDescriptorWidthsGenerate.canonicalDescriptorWidths_exec` now composes
shared base-width generation, successor, shifted coordinate width and canonical
width-counter bit generation on one scratch bank. Only four output operands
change: shared group/stride width, index width, selector/coordinate width and
width-counter bits. The bound is `8*L*L + 90*L + 105`.
`canonicalDescriptorWidths_canonical_exec` derives all additional fit conditions
from the existing canonical routing assumptions, and
`canonicalDescriptorWidthsBank_router` identifies every output with the exact
`canonicalStageWidths` fields for every residue. The guarded check passed at
2571.8 MiB. This closes remaining width-formula execution above; operand resizing
(to both narrower and wider descriptor fields), residue iteration, profile/frame
integration and all remaining R3 acceptance gates are open. The accumulated
residue-geometry/descriptor-width chunk passed the full guarded root build
(15,398 jobs, 4.5 GiB combined peak) and root axiom audit (352,493 declarations,
4437.8 MiB peak), superseding pending verification and uncommitted-status notes
above. Kappa is unchanged.

`BinaryResizeCopy.binaryResizeCopy_exec` now copies an operand into any live
target width, including narrowing and zero extension. It copies the source,
appends target-width zeros with the existing executed padder, extracts the exact
low-width word and erases the wide temporary. Source, width input and all scratch
restore; arbitrary output suffix is preserved. Its bound is
`2*M*(4*W+11) + 12*L + 26*W + 42` (guarded check 1706.6 MiB).
`BinaryResizeBatch.binaryResizeBatch_exec` installs a fixed bank of resized
operands with one structural list proof. Register separation, initial output
emptiness and compact source/width bounds establish exact installed words and
restored sources/scratch; every resize is priced. Numeric dimensions occur only
in the proof ledger, while the executed program depends on register maps and
fixed job order. The guarded check passed at 1693.4 MiB.
Instantiating the batch for generated canonical parameters, adding framed cleanup
and connecting resized inputs to actual profile/frame compilation remain next.
Residue iteration and all other R3 acceptance gates remain open. These changes
are uncommitted pending the larger compiler integration; kappa is unchanged.

`BinaryResizeBatchScope` now proves exact installed-word reads, restoration
of the original bank after erasure, and bounded cleanup for an arbitrary fixed
resize list. Setup, a framed compiler call and full cleanup compose with only
call output changed; the guarded check passed at 1683.2 MiB.
`MatchingControlScope` now uses two actual resize jobs in place of copy-only
installation. It accepts compact stride/residue words in their original scalar
width plus the generated target-width word, installs exact compiler-width
controls, and erases both after use. Its complete overhead is bounded by
`4*M*(4*Lk+11) + 24*Ls + 56*Lk + 90` (1702.3 MiB).
`MatchingProfileGeneratedCount` now separates the prefix multiplier's compact
stride-input width from the descriptor stride width. Thus prefix counting and
control resizing can share the original compact stride word without requiring
an additional pre-resized count input. `MatchingProfileCompactControls` and
`PermutationReservoirProfile` use the resized-control scope in place; the actual
full pipeline still restores all tables, controls and scratch except profile
output. The updated pipeline passed its guarded build (2.9 GiB combined peak).
Concrete canonical geometry/width-bank placement into that compiler, residue
iteration, complete frame generation and every remaining R3 gate stay open.
The accumulated resizing/compiler chunk passed the full guarded root build
(15,401 jobs, 4.5 GiB combined peak) and root axiom audit (352,534 declarations,
4439.9 MiB peak), superseding the pending verification and uncommitted-status
notes above. R3 and kappa remain unchanged.

**Fixed production-frame bridge (in progress):** `matchingFixedFrame` now derives
the fixed compiler frame from the matching table and resized controls without
requiring an already generated prefix count. `matchingFixedSetup` adds that count
as a short wrapper. `matchingProductionBank_update_controls` proves that installing
stride and residue in the two fixed gather slots gives exactly the declared
production bank; its guarded file check passed at about 2.47 GiB. `MatchingFixedControls` places three compact core inputs, the two gather outputs
and six reused generator scratch tapes on one concrete bank. Its injectivity,
blankness and bank identity are checked; `matchingFixedControlFrame` derives the
producer frame directly from that installed bank without a supplied count. The
guarded module check passed at about 2.53 GiB. `MatchingFixedCount` now supplies the concrete thirteen-register count map,
proves its injectivity and scratch readiness, and separates its output from all
gather/generator registers and both resized controls. Its guarded check passed
at about 2.56 GiB. `matchingFixedProfile_exec` now composes actual resizing, prefix-count
generation, full profile production and cleanup on this concrete bank. It derives
the frame from the bank instead of accepting one, gives an explicit total step
bound, and restores every register except the profile output. Its guarded check
passed at about 2.45 GiB. These modules are imported by the root. The accumulated chunk passed the full
guarded root build (15,404 jobs, combined peak 7.4 GiB) and axiom audit
(352,560 declarations, peak 4440.9 MiB). Connection to generated canonical geometry, the
permutation-to-matching producer and full residue iteration remain open.
Full R3 and kappa are unchanged.

**Canonical profile setup (in progress):** `canonicalProfileSetup_exec` composes
actual residue geometry and exact descriptor-width generation on a shared
28-register layout, starting only from binary dimension/residue and blank scratch
with arbitrary carry. Its cost is at most `96*L*L + 562*L + 526`.
`canonicalProfileSetup_parameters` identifies the exact stride, residue, row-count,
stride-width and coordinate-width words needed by the fixed profile compiler.
The guarded module check passed at about 2.53 GiB. `canonicalProfileScope_exec` now prices erasure of all eleven generated words
at exactly `22*L+23` steps and restores the entire original bank except the framed
call output, with total setup/cleanup overhead `96*L*L+584*L+549`. Its guarded
check and dependency build passed (module check about 2.50 GiB).
`canonicalProfileSetupBank_production` proves setup commutes with the fixed
production-bank embedding, preserving its matching table and compiler workspace;
its guarded check passed at about 2.48 GiB. `canonicalProfileFits` derives every compiler fit (including entry-byte count)
from the existing canonical large-dimension gate, with no additional threshold.
`canonicalPreparedProfile_exec` now instantiates the executed fixed compiler using
the generated bank and the concrete control/count inputs; no supplied production
frame or numeric-fit premises remain at this boundary. Both guarded checks passed
at about 2.49 GiB. `canonicalProfile_exec` now joins initial setup, actual fixed compilation and
final cleanup in one program, with an explicit summed cost and exact restoration
of every register except the appended profile output. The program depends only on
register placement, direction and output slot; dimension and widths remain tape
data. Its guarded check passed at about 2.50 GiB. The matching table remains an
input: permutation-table production and reuse across the residue loop remain open,
as do all other R3 acceptance gates. Root imports are added. The accumulated canonical setup/compiler/cleanup chunk
passed the full guarded root build (15,409 jobs, combined peak 4.5 GiB) and axiom
audit (352,593 declarations, peak 4440.1 MiB), superseding the pending verification
notes above. R3 and kappa are unchanged.

**Matching-table width bridge (in progress):** The permutation/reservoir table
producer emits the original scalar-width encoding, while canonical profile
compilation consumes the exact descriptor coordinate width. This requires executed
re-encoding, not a pure identification of the two words. `matchingEntryResize_exec`
now resizes both loaded endpoints into one delimited matching entry, preserving
both source operands and every arithmetic scratch tape. Its cost is at most
`4*M*(4*W+11)+24*L+52*W+86`; the program takes the target width from a live tape.
The guarded module check passed at about 2.48 GiB. `matchingResizeStep_exec` now loads one original entry into the resizer, archives
its complete original encoding, accumulates the resized encoding in reverse and
erases both loaded endpoints and the temporary output. Its bound is
`4*M*(4*W+11)+36*L+56*W+108`; the guarded check passed at about 2.47 GiB.
`matchingResizeLoop_exec` now scans an arbitrary endpoint list with one fixed
program, bounded by the entry count times the step bound plus loop overhead.
`matchingResizeTraceBank_eq` identifies its final bank exactly: empty source,
complete reversed original table in the archive, and complete reversed resized
table in the output accumulator. The guarded check passed at about 2.45 GiB.
`matchingTableResize_exec` now rewinds the complete original table and transfers
the resized output, restoring every register except the separate output. Its cost
is at most `entries*(4*M*(4*W+11)+40*L+60*W+118)+6`.
`matchingTableResizeScope_exec` additionally installs that table for a framed call
and erases it afterward, again leaving only the call output changed. Its overhead
is at most `entries*(4*M*(4*W+11)+40*L+64*W+122)+8`.
Both guarded checks passed (about 2.46 GiB); the converter dependency build also
passed. `MatchingFixedTableResize` now places the converter on two core inputs and the
existing fixed producer scratch, with output exactly at extractor slot 5. Its
injectivity, output separation and blank-workspace readiness are proved.
`matchingProductionBank_update_table` identifies the installed table with the
compiler's declared bank. The guarded check passed at about 2.57 GiB.
`matchingResizedProfile_exec` now composes actual table conversion, fixed profile
compilation and temporary-table erasure on that bank. The original scalar-width
table lives in the core; the compiler workspace starts entirely blank. It derives
entry bounds from the table domain and preserves every register except the appended
profile output, with an explicit total bound. Its guarded check passed at about
2.46 GiB. `canonicalPreparedProfile_exec` and `canonicalProfile_exec` now use this restored
conversion path in place of the supplied compiler-width table. They accept the
original scalar-width table in a core input and entirely blank compiler workspace;
target width, control operands and all fits are generated/derived internally.
No alternate canonical supplied-table implementation is retained. The guarded
canonical module check passed at about 2.50 GiB. The accumulated conversion/canonical integration chunk passed the full guarded
root build (15,416 jobs, combined peak 4.5 GiB) and axiom audit
(352,649 declarations, peak 4439.7 MiB), superseding pending verification notes.
Permutation/reservoir-producer composition and all remaining R3 gates stay open;
R3 and kappa are unchanged.

**Concrete permutation producer (in progress):** `permutationReservoirFixed_exec`
now instantiates permutation decomposition and reservoir class/local conversion on
one fixed 98-register bank. Register separation and every scratch-readiness fact
are derived from binary dimension/reservoir/span, the original scalar-width
permutation table, arbitrary carry tapes and blank remaining workspace. Execution
restores every register except local matching-table slot 34, with the producer's
full explicit cost bound. The guarded check passed at about 2.55 GiB. `CanonicalPermutationLayout` now embeds the producer and geometry into one
126-register core, sharing dimension/carry and placing generated reservoir/span
directly in the producer input slots. Both embeddings are injective;
`canonicalPermutationProducer_scalars` identifies the exact generated inputs and
`canonicalPermutationProducer_blank` derives all remaining producer scratch
readiness from the initial blank bank. No intermediate scalar copies are needed.
Its guarded check passed at about 2.51 GiB. `canonicalPermutationProduce_exec` now executes the embedded producer directly
on the generated canonical setup bank. It derives canonical reservoir fit/span
bounds, all three live scalar inputs and the entire producer readiness contract;
only original dimension/permutation input and initial blank-bank facts are supplied.
Its guarded check passed at about 2.48 GiB. `canonicalProfileSetupBank_update` now proves installing a table outside metadata
commutes with setup, providing the bank identity for the compiler handoff.
`permutationReservoirSource_involutive` preserves the generated matching's
involution through the exact profile-domain cast. Both guarded checks passed at
about 2.50 GiB. `permutationReservoirLocalWord_eq` now identifies the exact generated serialization
with the profile-domain matching table. `canonicalPreparedProfileCost` factors the
existing compiler ledger for composition without changing its bound.
`canonicalPermutationScope_exec` now lifts the actual producer onto the full
162-register compiler bank, executes a framed call, and erases the generated local
table. It restores every register except the call output and sums producer, call
and table-cleanup costs; its guarded check passed at about 2.50 GiB. The producer's initial blankness contract is now restricted to its actual
workspace below register 98, allowing accumulated output and other untouched tapes
outside it. `canonicalPermutationCompile_exec` instantiates the framed call with
the actual canonical compiler: original permutation table to local matching table,
executed width conversion, profile compilation and erasure of both temporary table
encodings. All scalar/frame readiness derives from prepared geometry; only the
profile output changes. The guarded module check passed at about 2.50 GiB.
`canonicalPermutationProfile_exec` now joins initial geometry/width generation,
actual permutation decomposition and reservoir localization, table-width conversion,
profile compilation, both table cleanups and final geometry cleanup. It starts from
binary dimension/residue, the original scalar-width permutation table and blank
workspace, allows accumulated output outside producer workspace, and restores every
register except the appended profile output. The program depends only on the fixed
direction/class and destination; dimensions/widths remain tape inputs. Its guarded
check passed at about 2.50 GiB. Root imports are added. The unused supplied-frame profile compiler was removed
(restore commit `89abda33`); its pure source/serialization helpers now support the
canonical path. The accumulated integration passed the full guarded root build
(15,422 jobs, combined peak 4.5 GiB) and axiom audit (352,685 declarations, peak
4444.3 MiB), superseding pending verification notes above. Residue iteration,
full canonical frame assembly and every remaining R3 acceptance gate remain open;
R3 and kappa are unchanged.

**Residue iteration (in progress):** `indexedCountLoop_exec` proves a fixed host
count-tape loop for an indexed bank family. Given executed transitions between
successive banks and a live count-tape termination invariant, it executes exactly
the required rounds with bound `N*(price+2)+2`. The numerical index/bank family
remain proof annotations; the program depends only on the count register and fixed
body. Its guarded check passed at about 1.16 GiB. `indexedCountStep_exec` now composes a framed call with an in-place binary index
increment and one archived count symbol, with overhead `4*L+6` and restored
arithmetic scratch. `canonicalResidueStep_exec` instantiates this with actual
original-permutation-to-profile compilation on a concrete 163-register bank:
count 107, archive 162, residue 116, output 98, temporary 126 and carry 70. The
count/output use unused core slots; archive is outside the compiler bank. Its
guarded check passed at about 2.87 GiB. `canonicalPermutationProfileCost` factors
the existing total ledger without changing its bound. `IndexedCountBank` now supplies the closed invariant: remaining count is
`drop i`, archive is reversed `take i`, residue is binary `i`, and output prepends
the first `i` generated profiles. Its step identity matches the executed round,
its count test is exactly `i < count.length`, and its output is proved to be the
flattened profiles in reverse iteration order. The guarded check passed at about
1.17 GiB. `canonicalResidueBank_projection` now proves the indexed loop bank projects
exactly to the fixed compiler bank each round, with only count 107, residue 116
and output 98 changed inside the core. `canonicalResidueCoreBank_blank` and
`canonicalResidueCoreBank_geometry` preserve all producer and geometry scratch
readiness under those updates. Its guarded check passed at about 2.50 GiB.
`CanonicalResidueWords` now defines the exact profile family and its existing
per-round cost ledger. `canonicalResidueLoop_exec` executes every actual residue
round with one fixed counted program, using the closed bank invariant and ready
compiler-bank projection. The guarded check passed at about 2.50 GiB. Its count
tape is still supplied and its cost is conditional on an explicit uniform round
bound; generating/restoring the outer count/index and discharging that bound, output
transfer/frame assembly and the remaining R3 cost/fallback gates stay open. Root imports are added. The accumulated indexed-bank/actual-round/all-residue
loop chunk passed the full guarded root build (15,429 jobs, combined peak 4.5 GiB)
and axiom audit (352,738 declarations, peak 4441.0 MiB), superseding pending
verification notes above. Full R3 and kappa are unchanged.

**Residue initialization/cleanup (in progress):** `IndexedCountClean` proves the
initial zero-index bank identity and exact restoration after count-archive rewind
and index erasure. `canonicalResidueProgram_exec` now executes binary residue-zero
initialization from the dimension tape, every actual residue round, count rewind
and final index erasure. It restores every register except accumulated output,
with bound `K*(price+4)+6*L+10`. The guarded check passed at about 2.51 GiB. `canonicalResidueCount_exec` now generates the unary count from binary dimension,
executes stride/gap arithmetic and conversion, then erases both temporary binary
words before the loop. Its bound is `4*L*L+123*L+180+6*K`.
`canonicalResidueCountScope_exec` executes a framed call and erases the generated
count afterward, restoring its original bank except call output, with overhead
`4*L*L+123*L+182+8*K`. Its guarded check passed at about 2.50 GiB. `canonicalResidueGenerated_exec` now places count generation on the actual
163-register bank, reusing blank compiler workspace and restoring it before the
loop. It composes dimension-to-count generation, all actual profile rounds, count
rewind, index erasure and count cleanup. No count/index tapes are supplied; both
start and end blank, and only compiled output changes. Its bound is
`K*(price+12)+4*L*L+129*L+192`, with the uniform round bound still explicit.
The guarded check passed at about 2.52 GiB. `canonicalPreparedProfileCost_le` and `canonicalResidueRoundCost_le` now derive a
uniform residue-independent arithmetic ledger from dimension and canonical gap,
using the actual full-profile production bound. `canonicalResidueUniform_exec`
applies it to generated-count execution: no supplied count/index words or round
price remain, and every register except compiled output restores. Its total cost
is the explicit `canonicalResidueTotalBound L n`. The guarded check passed at about
2.51 GiB. The accumulated generated-counter/restoration/uniform-cost chunk passed the full
guarded root build (15,434 jobs, combined peak 4.5 GiB) and axiom audit
(352,759 declarations, peak 4442.6 MiB), superseding pending verification notes.
Complete canonical-frame assembly, uniform setup absorption into the full-router price,
small-dimension/short-record fallback and all remaining R3 gates stay open;
R3 and kappa are unchanged.

**Canonical frame scalar assembly (in progress):** Auditing the canonical live
bank shows repeated descriptor operands can share stride/gap, residue/successor,
zero, target/borrowed widths, their last-row values and two source-width values.
The last-row operand is natural subtraction and must remain zero for empty rows.
`binarySaturatingSub_exec` now implements actual saturated subtraction of padded
binary inputs, preserving sources and all scratch, with bound `14*L+15`; it handles
zero-width/empty-row cases without new size assumptions. Its guarded check passed
at about 1.16 GiB. `RepairDescriptorScalarPalette` now identifies all 55 numeric descriptor fields
(stride, base, last row, rows and source width across eleven modes) with exactly
eleven shared scalar values. The static selection map and encoded-width identities
are proved; the guarded check passed at about 2.44 GiB. `descriptorLastRows_exec` now generates both shared last-row values from live
target/borrowed row counts, sharing one internally generated binary one and erasing
it afterward. Empty row counts produce zero, both inputs and all arithmetic scratch
restore, and only the two last-row outputs change. Its bound is `38*L+41`; the
guarded check passed at about 1.18 GiB. `descriptorSourceWidths_exec` now generates `2*borrowed+1` and
`rows+2*borrowed+1`, computing the shared double/sum once and erasing both
intermediates. Both input operands and scratch restore, and its exact cost is
`42*L+48`; its guarded check passed at about 1.17 GiB.
`repairDescriptorScalarPalette_fit` proves all eleven shared values fit the canonical
coordinate width from existing descriptor bounds and `rho < K`, with no new size
gate. Its guarded check passed at about 2.45 GiB. `descriptorScalarGenerate_exec` now combines last-row generation, both source-width
sums, residue successor and zero generation on one 17-register layout. It preserves
the five live geometric inputs and scratch, generates the six derived values with
bound `94*L+104`, and `descriptorScalarBank_palette` identifies the entire resulting
bank with the exact eleven-value palette. Its guarded check passed at about
2.45 GiB. `routerTargetWidthGenerate_exec` now derives the missing common target-width
operand `n-3*borrowed` from live dimension/span, erasing its doubled/tripled
intermediates in exactly `30*L+34` steps. The canonical specialization identifies
it with every residue's `p.wy`, deriving the subtraction bound from existing
geometry. Its guarded check passed at about 1.18 GiB. `descriptorScalarResize_exec` now executes a fixed five-job resize schedule into
the palette bank and all six derived-scalar generators. The target width and compact
input values are read from tapes; its bound is
`10*M*(4*W+11)+60*L+224*W+315`. `descriptorScalarResizedBank_palette` identifies every
output exactly with the shared palette. Its guarded check passed at about 2.49 GiB.
The accumulated scalar-generation/target-width/resizing chunk passed the full
guarded root build (15,441 jobs, combined peak 4.5 GiB) and axiom audit
(352,822 declarations, peak 4441.4 MiB), superseding pending verification notes.
Concrete placement
against the generated canonical geometry, descriptor-role installation and complete
frame serialization remain open, along with every remaining R3 gate; R3 and kappa
are unchanged.

**Canonical scalar placement (in progress):** `CanonicalDescriptorScalarLayout`
places geometry, target-width arithmetic and scalar resizing/generation on one
46-register scope. The five compact inputs alias generated stride, gap, residue,
target width and borrowed span directly; the target encoding width aliases the
exact generated coordinate-width word. All three maps are injective, remaining
palette scratch is proved blank, and the five original-width fits follow from
existing dimension/geometry gates. `canonicalDescriptorScalarInputBank_ready`
identifies every required input word exactly. The guarded check passed at about
2.53 GiB. `canonicalDescriptorScalarGenerate_exec` now executes geometry/width generation,
common target-width arithmetic, five-input resizing and all derived-scalar
arithmetic as one program from binary dimension/residue and blank workspace.
Every fit is derived from the existing canonical assumptions. Its bound is
`96*L*L+652*L+875+10*L*(4*W+11)+224*W`, where `W` is the generated canonical
coordinate width. The guarded check passed at about 2.52 GiB. `canonicalDescriptorScalarBank_keep/clean/cleanCost` now prove exact spectator
preservation, restoration after erasing all 23 generated words, and cleanup cost
`24*L+22*W+47`. `canonicalDescriptorScalarScope_exec` executes generation, a framed
call and cleanup with full restoration except call output; its overhead is
`96*L*L+676*L+922+10*L*(4*W+11)+246*W`. The guarded check passed at about 2.52 GiB.
Instantiating the call with actual descriptor-role installation, complete frame
assembly and the remaining R3 gates stay open. This work is uncommitted pending
that larger integration; R3 and kappa are unchanged.

`DescriptorScalarFields` now identifies all 55 selected palette words with the
actual canonical descriptor-role operands and proves the role placement injective.
The existing `binaryResizeBatchBank_at` supplies the installation lookup theorem;
the redundant new lookup was removed. `DescriptorScalarInstall` now executes the
55 resize jobs on a 101-register scope, sharing the canonical palette at 28–38,
width words at 21/26 and scratch at 39–43/45, with distinct destinations at 46–100.
It identifies every final field with `canonicalDescriptorOperands`, restores
scratch and proves the structural cost bound
`55*(2*M*(4*B+11)+12*W+26*B+42)+1` when destination widths are at most `B`.
The guarded check passed at about 2.57 GiB. Connecting this installation to the
executed canonical generator, complete frame assembly and remaining R3 gates
stay open; these additions are uncommitted with the scalar-placement chunk.

`CanonicalDescriptorInstallReady` now connects the generated palette and both
width words directly to that installation, and proves scratch/destinations blank.
`canonicalDescriptorInstall_exec` composes actual scalar generation and all 55
field installations from only binary dimension/residue and blank workspace.
It derives all fit conditions and bounds the combined cost by the scalar
generation price plus `55*(2*L*(4*W+11)+38*W+42)+1`, with canonical coordinate
width `W`. The guarded file check passed at about 2.51 GiB; the readiness
dependency build passed. Complete frame assembly, framed-call/cleanup composition,
router integration and all remaining R3 acceptance gates stay open. These changes
are uncommitted pending the larger frame integration and root validation.

`canonicalDescriptorScope_exec` now composes generation, all 55 installations,
an actual framed call, field cleanup and scalar/geometry cleanup. Its final
bank changes only the call output; every setup input, scratch tape and spectator
is restored. The explicit overhead is the scalar-scope price plus
`55*(2*L*(4*W+11)+38*W+42)+55*(2*W+2)+2`.
Common destination-width bounds and canonical width fits are factored into
`CanonicalDescriptorInstallReady` and reused by generation/installation and the
scope. The guarded scope check passed at about 2.52 GiB. Root imports are added;
the full guarded root build passed (15,449 jobs, peak 4.5 GiB), and the axiom
audit passed (352,898 declarations, peak 4443.7 MiB). This completed 768-line
generation/installation/restoration chunk supersedes the pending-validation
notes above. Frame serialization and
full-router integration remain open, along with every other R3 acceptance gate.

**Complete descriptor operand frame (verified checkpoint):**
`canonicalDescriptorGenerate_exec` generates all 61 nonempty descriptor scalars
from binary dimension/residue on a 108-register scope. Geometry, width words,
zero/one constants and every numeric fit are generated or derived internally.
`canonicalDescriptorGeneratedBank_operands` identifies the complete source
projection with `canonicalDescriptorOperands`; all other roles share one proved
blank source, including initially empty profiles and scratch.

`DescriptorOperandFrame` serializes every role in physical auxiliary-bank order.
`canonicalDescriptorFrameScope_exec` composes generation, full serialization and
three cleanup stages, restoring every register except the output frame and
preserving its arbitrary existing suffix. Its price is
`canonicalDescriptorSerializePrice L W + 24*L + 146*W + 173`.
The serialization price includes all generation/install work and the structural
copy bound `card(LiveDescriptorRole 11)*(36*W+7)+1`.
`DescriptorOperandLoad` executes loading into an arbitrary injective caller role
placement, proves every loaded word exact, and bounds loading by
`card(LiveDescriptorRole 11)*(4*B+6)+1` for maximum word width `B`.
`canonicalDescriptorOperands_scan` supplies binary-word scanner readiness.

The scope and loader dependency build passed. Superseded 55-field-only wrappers
are removed (restore committed generation/scope wrappers from `f2386c68`);
uncommitted partial serializers/loaders were replaced by this complete path.
Root imports are added; the full guarded build passed (15,458 jobs, combined peak
31.6 GiB). The axiom audit passed (353,004 declarations, peak 4443.2 MiB);
final guarded scope/loader checks used 2549.3/2562.3 MiB respectively.
This closes descriptor **operand** production, not the complete router
frame: repair/header/classifier/placement operand generation, activity/selected
profile composition, full router integration, small dimensions, executed short
records and uniform global amortization remain R3 gates. R3 and kappa are unchanged.

**Complete classifier operand frame (verified checkpoint):**
`BinaryScalarWidthBatch` shares the existing exact-width routine and traversal
scratch; its structural restoration/cost lemmas support reusable control banks.
`canonicalClassifierGenerate_exec` generates all six classifier operands and
four exact scalar widths from only binary dimension and residue. Raw fits,
source readiness and width fits are derived internally. The original 108-register
descriptor bank is preserved. `ClassifierOperandBank` identifies all sixteen
classifier roles, including the ten empty roles using one restored blank source.

`canonicalClassifierFrameScope_exec` composes compact-input setup, complete
classifier serialization, operand/width cleanup and the existing full descriptor
cleanup. Only the output frame changes; its arbitrary existing suffix is retained.
The price is `canonicalClassifierGeneratePrice L W p + 16*(6*(L+W)+7)+1`
plus `20*(L+W)+22` for classifier cleanup and `24*L+146*W+173` for descriptor
cleanup. The dependency build passed (8,827 jobs); guarded checks stayed below
2.7 GiB. Root imports are added; the full guarded build passed (15,470 jobs,
peak 4.5 GiB). The axiom audit passed (353,124 declarations, peak 4445.7 MiB);
the final guarded scope check used 2557.1 MiB.
Repair/header/placement operands, profile/frame composition,
full-router integration, small dimensions, executed short records and global
amortization remain open. Full R3 and kappa are unchanged.

**Complete inner header operand frame (verified checkpoint):**
The row driver invokes the inner router with `R=1`; its outer row counter remains
handled by the existing driver. `BinaryCanonicalWord` identifies the existing
canonical-copy routine with the exact shortest binary operand, including zero.
`canonicalHeaderScalarGenerate_exec` reuses the generated borrowed-width palette
word and one push to create both header operands in an additional `10*W+13` steps.
All source readiness and fits follow from the original dimension/residue inputs.

`canonicalHeaderFrameScope_exec` composes all setup, complete header-work-bank
serialization and final restoration. Every setup tape is restored and arbitrary
existing frame suffix is preserved; only the output changes. The total price is
`canonicalClassifierGeneratePrice L W p + 10*W+13`
plus `card(HeaderWorkRole)*(6*W+7)+1` for copy, `2*W+7` for header cleanup,
and `44*L+166*W+195` for preceding classifier/descriptor cleanup.
`CanonicalClassifierClean` factors that preceding restoration for reuse, and the
previous classifier scope now uses it. Both scopes passed their dependency build
(8,836 jobs, peak 4.9 GiB). Root imports are added; the full guarded build passed
(15,479 jobs, peak 4.5 GiB), and the axiom audit passed (353,178 declarations,
peak 4445.8 MiB). The final scope check used 2560.5 MiB.
This closes inner header **operand** production, not
remaining repair/placement metadata, profile/frame composition, full router
integration, small dimensions, short records or global amortization. R3 and kappa
remain unchanged.

**Repair scalar production (in progress):** `RepairZeroGenerate` executes two
shared zero-field constructions from binary target/borrowed widths and identifies
all five field-buffer operands, reusing one word for the three borrowed fields.
Its bound is `4*W*(wc+wy)+22*W+8*(wc+wy)+24`; scratch and both width sources restore.
`CanonicalRepairDimensions` proves that canonical fields total the original
dimension `n`, the one-row key length is `n+1`, and the required count word is
`binSyms (n+1) (2^n)`. `RepairRecordCountGenerate` constructs that exact word
from binary dimension with restored source/scratch and cost at most
`L*(4*n+11)+8*n+13`. Guarded checks passed (about 2.43/2.47/1.17 GiB respectively).
Canonical composition, remaining key/block/payload operands, repair-frame
serialization/cleanup and all other R3 acceptance gates remain open. These
additions are uncommitted pending the larger repair-frame integration.

`canonicalHeaderScalarGeneratedBank_palette` now proves the full shared palette
survives header/classifier setup; blank-source readiness covers all shared scratch.
`canonicalRepairZeroGenerate_exec` uses those facts to compose prior setup and
both repair zero words from original binary dimension/residue on a 124-register
scope. Every input fit is derived; the caller's reserved payload-width register
is retained without a blank assumption. Its dependency build passed (8,827 jobs,
peak 3.1 GiB). Record-count composition and key/block/payload production, repair
frame serialization/restoration and every remaining R3 gate stay open. This work
remains uncommitted with the larger repair chunk.

`canonicalRepairCountGenerate_exec` now composes all prior setup, both shared
zero fields and exact `2^n` record-count generation from original binary dimension/
residue. Scratch is reused and restored; the reserved payload-width tape remains
outside the blank assumptions. Its dependency build passed (8,829 jobs, peak
3.1 GiB). `BinaryCanonicalWord` now factors exact canonical-word identification
for both in-place normalization and copying. `BinaryCanonicalSuccessor` uses one
high padding bit, increment and normalization to produce the exact shortest
`n+1` word in `18*L+39` steps, including overflow of the original width, while
restoring its source and scratch. Its dependency build passed (2,089 jobs, peak
1.8 GiB). Canonical key-length composition and block/payload production remain
open, together with repair-frame serialization/cleanup and all other R3 gates.
This work remains uncommitted pending the larger repair-frame integration.

`CanonicalRepairCountReady` now identifies preserved dimension/payload sources,
the generated one-bit padding operand, shared scratch and spectators after repair
count setup. `canonicalRepairKeyGenerate_exec` composes that setup, overflow-safe
key-length successor generation and payload normalization from the original
dimension/residue/payload words. The extra price is `18*L+39 + 10*Lb+12`.
Its final key-length and record-count words are identified exactly with
`canonicalRepairPayload`; the payload word is exact as well. Guarded checks passed
at about 2.73 GiB. Block-width arithmetic, complete repair-bank serialization/
restoration and the remaining R3 gates stay open. This work remains uncommitted
pending the larger repair-frame integration.

`BinaryCanonicalSum` now executes overflow-safe shortest-word generation for
`x+y+1` from independently padded inputs, restoring sources and scratch in
`44*(L+M)+99` steps; no caller sum-fit premise is needed. Its guarded check
passed at about 1.17 GiB. `canonicalRepairBlockGenerate_exec` composes this
with all preceding metadata generation from original dimension/residue/payload
words, preserving the earlier outputs; its dependency build passed at 3.1 GiB.
`canonicalRepairBlockGeneratedBank_operands` identifies every repair setup word,
including all empty controls, with the exact canonical payload (guarded check
about 2.50 GiB). These results supersede the block-arithmetic and operand-generation
open items above. Repair serialization/restoration, placement metadata,
profile/frame integration, full router execution, small dimensions, short-record
fallback and uniform global amortization remain open. This repair chunk is
uncommitted pending frame integration; R3 and kappa are unchanged.

`canonicalRepairSerialize_exec` now generates all numeric repair operands and
serializes the entire setup-key bank, preserving arbitrary output suffix and all
sources. `canonicalRepairScalarRestore_exec` erases just the six new operands
and restores the preceding header bank while retaining the output.
`canonicalRepairFrameScope_exec` composes serialization with numeric, header,
classifier, descriptor and geometry cleanup: only the serialized output changes,
including restoration of original dimension, residue, payload and arbitrary
spectators. Its cost uses explicit dimension-only generation, copying and cleanup
bounds; numeric cleanup costs exactly twice the six word lengths plus 13.
The full guarded root build passed (15,496 jobs, peak 5.1 GiB), and the axiom
audit passed for 353,351 declarations (peak 4448.4 MiB). This verified chunk
supersedes the uncommitted/pending-integration notes in this repair subsection.
This closes repair operand-frame generation/serialization/restoration,
superseding those open items above. Placement metadata, profile/frame integration,
actual full router execution, small dimensions, executed short-record fallback
and uniform global amortization remain R3 gates; kappa is unchanged.

**Placement operand generation (in progress):** `canonicalPlacementOperands_exec`
now composes canonical geometry with the existing reservoir operand generator,
starting from the original binary dimension and blank workspace. It generates
all nine exact placement coordinates for every reservoir class, including the
zero-width front exchange, in at most `88*L²+546*L+507` steps.
`canonicalPlacementWidth_exec` adds the exact live target encoding width
`canonicalScalarWidth n`, preserving all coordinates and the dimension.
`canonicalPlacementResize_exec` uses the existing generic batch copier to
produce all nine coordinates at that exact canonical width, with restored
scratch and an explicit summed cost. Guarded checks passed at about 2.53 GiB.
The raw operand/width dependency builds passed; these additions remain
uncommitted pending placement-bank serialization and complete cleanup. Payload,
one-row control and normalized dimension projection, complete placement-frame
assembly, profile/frame integration and every remaining R3 gate remain open.

`canonicalPlacementScalar_exec` now completes the generated placement input
words with normalized dimension, normalized payload width and the one-row
control, preserving both original padded inputs and every previous coordinate.
`canonicalPlacementScalarBank_operands` identifies the complete role bank with
the actual `binaryScheduleInputWords`, including all empty controls and a separate
empty record-stream placeholder. `canonicalPlacementScalarBank_physical` lifts
this to every physical schedule register, including unassigned slots.
`placementOperandCopy_exec` serializes that bank in physical register order,
using shared empty sources and preserved copy scratch, with an explicit bound.
The dependency build passed (8,839 jobs, peak 2.9 GiB); the final projection/copy
module passed its guarded check at 2563.5 MiB. This supersedes the missing
payload/row/dimension-projection items above. Composition of generation with
serialization, complete placement cleanup and all broader R3 integration,
fallback and amortization gates remain open. This placement chunk is uncommitted.

`canonicalPlacementSerialize_exec` now joins original-input generation with
physical-order bank copying, preserving an arbitrary output suffix.
`canonicalPlacementScalarBank_restore` proves that clearing the thirty generated
words restores the entire original bank, including dimension, payload, arbitrary
carry-stack contents and spectators. `canonicalPlacementCleanCost_le` bounds
cleanup by `60*L+60*Lb+121`, independently of bank contents.
`canonicalPlacementFrameScope_exec` composes generation, complete placement-bank
serialization and full cleanup: only the serialized output changes. The dependency
build passed (8,842 jobs, peak 2.9 GiB). This supersedes the placement-generation,
serialization and cleanup open items above. The full guarded root build passed
(15,506 jobs, peak 4.5 GiB); the axiom audit passed for 353,475 declarations
(peak 4450.8 MiB), and the final module checked at 2565.6 MiB. This verified
placement chunk supersedes the uncommitted notes above. Profile/frame connection, assembly of the complete router frame,
actual router integration, small dimensions, executed short-record fallback and
uniform global amortization remain open. R3 and kappa are unchanged.

**Remaining auxiliary-bank connection (in progress):** Full frame assembly also
needs the seven live-profile auxiliary words and six width-conversion words.
`routerAuxiliaryGenerate_exec` now generates their shared three nonempty operands
from binary count, live index-width and target-width words: resized profile count,
shortest target width and constant one-row control. It restores every source and
scratch tape. `routerAuxiliaryBank_profile` and `_width` identify all thirteen
roles, including their empty controls. `routerAuxiliaryClean_exec` restores the
three generated words after a disjoint caller output, with exact cleanup cost
`2*W+2*canonicalScalarWidth wy+9`. The dependency build passed (8,559 jobs, peak
2.9 GiB). `canonicalAuxiliarySources` identifies all three source words in the
existing canonical setup, so no extra caller numeric operands are needed.
Canonical execution composition, separate bank serialization in full-frame order
and final integration remain open. These additions are uncommitted; all broader
R3 gates and kappa are unchanged.

`canonicalAuxiliaryGenerate_exec` now composes original dimension/residue setup
with the auxiliary generator, deriving the exact count, index-width, target-width
and every numeric fit from canonical geometry. `CanonicalScalarInputGenerate`
factors the common setup prefix out of descriptor generation; the descriptor
generator now reuses it. Both dependency builds passed, and the composed auxiliary
generator passed its guarded check at 2592.5 MiB. `routerAuxiliaryCopy_exec` now
provides separate seven-word and six-word serializers, so full-frame assembly can
place the header bank between them. It preserves sources, copy scratch and arbitrary
output suffix and passed at 2535.6 MiB. Canonical serialization/cleanup composition,
full profile/frame connection, router integration and the other R3 gates remain
open. This auxiliary/frame chunk remains uncommitted pending that integration.

`canonicalAuxiliaryFrameScope_exec` now produces either remaining auxiliary
frame directly from original dimension/residue, preserves arbitrary output suffix
and restores every setup tape. The two variants remain separate so the full
frame can put the header between the seven live-profile and six width words.
`canonicalAuxiliaryClean_exec` restores all fifteen generated geometry/width/
auxiliary words, with exact cost `24*L+2*indexBits+2*canonicalScalarWidth wy+33`.
The final module passed its guarded check at 2572.1 MiB. The full guarded root
build passed (15,514 jobs, peak 10.5 GiB), and the axiom audit passed for 353,531
declarations (peak 4451.6 MiB). This verified chunk supersedes the pending and
uncommitted auxiliary notes above. This closes auxiliary frame production and
cleanup, superseding the corresponding open notes above. Full frame assembly,
profile connection, actual router execution, small dimensions, executed
short-record fallback and uniform global amortization remain R3 gates.

**Physical repair frame connection (in progress):**
`canonicalRepairBlockGeneratedBank_physical` identifies the generated numeric
bank with every physical register of the initial canonical repair bank, including
all empty scratch words. `repairPhysicalOperandCopy_exec` serializes every
nonstream physical register in the loader's order, with restored scratch and an
explicit cost bound. `CanonicalRepairClean` factors the full setup restoration
proof out of the existing setup-key frame scope so both serialization orders can
reuse it. The refactored scope passed its dependency build (8,849 jobs, peak
2.9 GiB). The full guarded root build passed (15,516 jobs, peak 4.5 GiB), and
the axiom audit passed for 353,542 declarations (peak 4452.3 MiB).
Physical-order generation/copy/cleanup composition and the generated
coordinate-profile overlay remain next, followed by full frame assembly and the
other R3 gates. R3 and kappa are unchanged.

**R3 sizing audit (2026-10-23):** The original R3 estimate of **3–5k** lines and
the later **15–24k additional or substantially revised Lean lines** estimate are
retired. At this audit snapshot the routing directory had approximately **74.3k lines in 834 modules**,
about **65k lines beyond the documented R2 checkpoint**, while R3 remains open.
The current matching scheduler imports **586 routing modules / 48.4k lines**;
another **248 modules / 25.9k lines** lie outside that import closure. This is an
import inventory, not evidence that those outside modules can all be removed:
they include terminal routing, reservoir semantics and alternative interfaces.
Future implementation must reuse the generic loader/loop and frame interfaces,
consolidate duplicated traversal proofs, and audit superseded wrappers against
the actual router path. Shared scanner final-bank reasoning is now centralized
in `delimitedScheduleBank_prepend`; coordinate generation and residue filtering
instantiate it instead of maintaining separate input/archive/spectator lemmas.
No new line-count ETA is supported until the remaining full-router construction
and retirement opportunities are assessed. Existing layout,
CRT-control, rotation and sorting primitives are reused. R1's logical identity is
not a tape implementation: source gathering, packed loads, guards, repair and their
costs must be proved before the router can improve a machine bound. Do not introduce
a free arbitrary-source read or a zero-initialized borrowed-control assumption.

## Resampling work packages (M7 and M11)

These packages prioritize shared arithmetic and the new fused schedule. The older
[NearOne design](IntegerMultBounds/MathlibTM2/NearOne/DESIGN.md) remains a mathematics
index; its broader status and estimates are historical. The `Mult/ShortConv` and
`Mult/ChirpRing` bridges have been restored, and S1 now supplies an executed shared
batch primitive. The existing chirped-forward and phase-cell inverse/error theorems
remain available for the S2–S3 callers.

| Package | Status | Deliverable and acceptance gate | Additional Lean, estimate |
| --- | --- | --- | --- |
| S1 shared short convolution | ✅ | `ShortConv.Fixed.closed_exec` executes a fixed 117-tape batch program from raw blocks and unary dimensions. Packing, one shared ring-product call, exact coefficient extraction/decoding, rounding error, costs and scratch restoration are proved. Shared by S2 and S3. | Implemented |
| S2 fast forward map | ✅ | `closedGroup_exec`: fixed 640-tape raw-input caller, generated coefficient tables, overlapping windows, decoded error ≤4 and exact restoration except output. Uniform costs and eventual O(M(p)) per output for complete live-axis batches at executable sizes are proved. | Implemented |
| S3 fast inverse map | 🟡 math / 🟡 kernels | Constructed-data cell arithmetic executes on 117 tapes with CellRun.Valid. Integer-column initialization and repeated iteration execute from a retained factor page. Coefficient/factor generation, encoding, setup bounds, gathering, boundary/coupling/recovery and uniform line costs remain. Shared S3–S5 interface is pinned. | 6–10k |
| S4 grouped/fused execution | ⬜ | Ordered core/halo neighborhoods, overlap/cropping, reusable setup, error composition and full-tensor support. Combine S2–S3 with R4 so exposure is not repaid per axis. Preserve reserved chunks and restore layouts before subsequent phases. | 8–16k |
| S5 boundary work | ⬜ | Fast boundary matrix operations required by the new parameter regime, including numerical stability, coefficient widths and actual tape costs. Shared prepared-boundary interface pinned; implement its stability, precision, storage and paid setup/solve/release contracts. The old band solve alone does not establish it. | 4–10k |
| S6 outer integration | ⬜ | New sizing and precision, both resampling directions, bulk CRT/exposure and every changed cost matched into the final machine. Depends on R4, S4–S5 and M4; closes M11 with M9–M10. | 3–6k |

**Shared S3–S5 interface pinned (2026-10-24):** The
[shared contract](IntegerMultBounds/MathlibTM2/NearOne/DESIGN.md#shared-s3s5-interface-pinned-2026-10-24)
fixes ambient-coordinate core/halo semantics, stage error handoffs, setup reuse
keys, prepared-boundary ownership, precision duties, exact restoration and the
complete grouped cost/storage ledger. `Mult.PhaseCellInterface` formalizes
`Window`, `ErrorOn` and `SolveSpec`: arithmetic/locality errors add, crop/publish
incurs no window-count factor, and the full solver endpoint supplies the existing
`concrete_resampB₀_specX` hypothesis. `PhaseCellReferenceSpec.pcSolve_spec` proves
the existing rounded solver satisfies that same endpoint. It does not require an
S1 implementation to equal the scalar-rounding reference exactly.

`SolveSpec.with_locality` now explicitly bridges a halo solve to a global core
contract using a separately proved locality comparison for the same ambient
matrix. It adds arithmetic and locality errors once and composes with
`SolveSpec.of_windows`. The guarded interface/reference/axiom-audit build passes
3851 jobs at 2.4 GiB combined peak; locality estimates themselves remain open.

S3 owns generated interior kernels and coupling/recovery; S5 owns generated
computed-Schur setup and repeated boundary solves; S4/R4 owns exposure,
locality, reserved-coordinate-safe publication and grouping by proven equal keys.
Local halos retain global phase/period cuts and add artificial endpoint cuts;
full-line boundary or precision bounds cannot silently be relabeled as local.
The next implementation gate is one generated cell interval through S1 with
`CellRun.Valid`, rescaled error and actual cost. The interface is pinned, while
S3/S4/S5 execution, locality/stability and cost gates remain open; kappa is unchanged.
The guarded interface/reference/audit checks pass at 1730.6/1737.3/1723.0 MiB;
the guarded audit build completes 3851 jobs at 2.4 GiB combined peak. Only the
three existing approved axioms are allowed; proof limits are unchanged.

**S3 interior kernel started (2026-10-25):** `Mult.ToeplitzShortConv` proves
both triangular products are coefficient ranges of one linear convolution:
lower reads i; upper reverses the input row and reads L-1-i. `block_reverse`
reverses coefficient words without reversing their bits. The lower and upper
output-error theorems apply directly to S1's returned pair symbols in front of
an arbitrary suffix, with the required factor 2^l and error 2*2^l/2^q explicit.
`PhaseCellToeplitz.lower_batch_exec` in `Mult.PhaseCellLowerBatch` combines
one actual fixed 117-tape S1 execution, its exact frame, paid S1 cost and every
lower-stage decoded error. It starts from normalized raw operands and supplied
unary dimensions; it is not yet a closed cell solve. The convolution/index check
peaks at 1807.7 MiB and the lower-batch check at 1796.8 MiB.

Next: compose the executed compaction with subsequent products and normalization,
generate interior weights/generators and dimensions, compose all four products
and rescaling, then prove `CellRun.Valid` and its paid scalar cost. Boundary setup,
line composition and the final S3 uniform cost remain open. S3 is active; no
S3 completion or kappa change is claimed by this first stage.
The guarded interface and Toeplitz audit build passes (4065 jobs, 2.4 GiB
combined peak). Existing `ShortConv.coeff_diskGrid` supplies next-stage range
preservation and will be reused rather than reproved for each triangular product.

**Executed upper-stage preparation and restoration (2026-10-25):**
`PhaseCellToeplitz.reverseRowsInPlace_exec` in `Mult.PhaseCellReverseRows` reuses the existing row reversal
and replaces an exact private source stream in place, restoring all scratch,
dimensions and other stacks. Two symbol moves preserve the low-bit-first words.
`PhaseCellToeplitz.reverseRowsFromDimensions_exec` in `Mult.PhaseCellReverseSetup` computes L*w from the
retained row/word counts and releases that generated counter. Its bound is
`C = M*(32*L*w+19*L+17)+6*L*w+9*L+20`.
`PhaseCellToeplitz.reverseInput_exec` in `Mult.PhaseCellUpperInput` discharges placement on ten empty private
host registers inside S1's existing 117-tape bank; they are blank again before
convolution. `PhaseCellToeplitz.upper_batch_exec` in `Mult.PhaseCellUpperBatch`
executes reversal, one S1 run and reversal again, restores the original raw
operands/dimensions and returns only the prefixed S1 result. The bound is
`Fixed.cost q l w M + 2*C`, with the upper-stage error proved from the actual
returned symbols. Reversed operands and the L*w count are no longer supplied.
The product output still has padded ring rows; compaction/crop into the next
stage's contiguous operands is not yet implemented.

The guarded upper-stage audit build passes (3999 jobs, 2.5 GiB combined peak).
The counter-setup, fixed-input and upper-batch checks peak at 1827.3, 1806.7 and
1803.0 MiB. S3 remains open through generated coefficients/normalization,
four-product cell composition, boundary/line composition and the final paid
uniform cost. No kappa change.

**Executed coefficient compaction (2026-10-25):** The existing extraction
program now has generic slice proofs for offset a and length m in
`ChirpExtract`, `ChirpBatchExtract` and `ChirpBatch`. The loop and program
bodies are unchanged. Original chirp theorems specialize a=3m and keep their
previous statements and costs. The general batch bound is
`M*(6*a*w+20*m*w+19*m+6*r*w+23)+8`; source and count restoration and arbitrary
source/destination suffixes are preserved.
`ShortConvSliceDecode` proves compact stream length/indexing, exact word decoding
at stride m, and disk-grid preservation. `ToeplitzShortConv.upper_coeff_error`
factors the numerical upper-stage estimate once for padded and compacted output.
`PhaseCellToeplitz.upperRows` in `Mult.PhaseCellUpperCrop` selects offset 0 and length L, in the upper stage's
required order; `upperRows_disk` reuses S1's existing range theorem to admit those
numerators to the next product. `upper_crop_exec` connects this data and its error
to actual extraction execution and the exact destination prefix.

`PhaseCellToeplitz.upperCropFromDimensions_exec` in `Mult.PhaseCellUpperCropSetup` generates 2^l*w from
the retained exponent/word headers, executes compaction and clears the generated
counter. It assumes no supplied ring-row symbol count. Its bound is
`M*(20*L*w+19*L+6*2^l*w+23)+4*w+6*2^l*w+9*l+22`, and only the destination
prefix changes. The generated-count crop check peaks at 1842.0 MiB; the generic
slice/loop/batch checks peak at 1845.7/1911.1/1935.2 MiB.

Next: compose upper/crop/lower stages with an executed staging/frame contract,
then generate weights/generators and prove the four-product `CellRun.Valid`
endpoint and paid scalar cost. The structural S1 packer, coefficient packer,
shared-product caller and unary setup caller now preserve arbitrary raw operand
suffixes with unchanged costs; the original exact-stream statements specialize
the same proofs at empty suffixes. The fixed-bank `exec_with_tails` and S3 `lower_batch_with_tails_exec` now
expose this contract with unchanged costs and exact suffix restoration. Boundary
and full-line composition, selected precision and final uniform S3 costs remain
open. This is kernel progress, not S3 completion or a kappa change.
Final verification: the expanded S3 audit and both S2 regression audits pass
in the guarded build (13936 jobs, combined peak 10.6 GiB, 2.5 minutes).
All eight changed/new kernel and audit files pass guarded single-file checks;
the largest measured peak is 1935.0 MiB. Default proof limits and the three
approved axioms are unchanged. PLAN and whitespace checks pass.

Suffix-preservation verification (2026-10-25): the expanded S3 audit and both
S2 regression audits pass in a guarded build (13936 jobs, combined peak
10.6 GiB, 2.7 minutes). Guarded single-file checks pass for the structural
packer (1889.5 MiB), product caller (1851.5 MiB) and unary caller
(1835.4 MiB). No program definitions, old theorem contracts or costs changed.

Fixed-bank staging checkpoint (2026-10-25): `inputBankWithTails` and
`startWithTails` retain arbitrary suffixes beneath both counted raw operands.
`Fixed.exec_with_tails` proves the same finite program and cost, and the old
`Fixed.exec` is its empty-suffix specialization. The lower-stage wrapper shares
this proof. `PhaseCellUpperOperand` identifies each compacted upper row and
proves its length and normalized disk bound for the next S1 call. Guarded
checks peak at 1857.3 MiB (fixed bank), 1797.8 MiB (lower wrapper) and
1792.5 MiB (upper operands). The expanded S3 and both S2 regression audits
pass in a guarded build (13937 jobs, combined peak 10.6 GiB, 2.2 minutes).
The actual staging, generator switching and temporary-stream release between
products still require executed composition; S3 remains incomplete.

Executed triangular-pair checkpoint (2026-10-25): `PhaseCellStageFrame`
identifies compaction's exact bank as the next lower call's input.
`PhaseCellStageInput.upperToLowerInput_exec` executes generated-count compaction
onto the right-operand tape, preserving its original rows below the new prefix.
`PhaseCellTriangularPair.triangularPair_exec` composes the upper product, staging
and lower product on 117 tapes, with the sum of their actual costs and decoded
lower error against the computed normalized upper rows. Its guarded check peaks
at 1806.3 MiB. The expanded axiom audit passes (4009 guarded build jobs,
combined peak 2.4 GiB). Temporary compact/padded upper rows remain explicit in
the postcondition: crop/publication of the lower result and paid prefix release
are still required before the second branch and four-product cell composition.
Generated weights/generators, precision, boundary/coupling/recovery, full line
composition and final S3 costs remain open; kappa is unchanged.

Paid intermediate release checkpoint (2026-10-25): `PhaseCellPrefixRelease`
proves prefix removal with an exact arbitrary suffix and original-symbol
counts. `releaseRows_exec` generates and releases both product counters from
retained batch/row/width dimensions; its bound is
`12*symbols + 9*M + 6*L*w + 9*L + 18`.
`PhaseCellInputRelease.releaseUpperInput_exec` removes only the compacted
upper-row prefix, restores the original right operand and leaves the output
untouched. `PhaseCellTriangularPairRestore.triangularPairRestored_exec` now
executes both triangular products, generated staging and this release, returning
the canonical bank with both original raw operands and decoded lower-product
error. The two padded product streams remain explicitly on the output tape.
Lower-result crop/publication and paid release of those output prefixes are
still required before repeated branches. The expanded axiom audit passes
(4012 guarded build jobs, combined peak 2.5 GiB); the row-release and fixed-input
release checks peak at 1827.1 and 1800.2 MiB. This does not complete S3: generated
cell arithmetic, both branches, boundary/coupling/recovery, precision and uniform
line costs remain open.

Lower-output components checkpoint (2026-10-25): `PhaseCellLowerCrop`
reuses the shared generated-count selector on lower-product streams. Its
`lowerRows_error` reads compact row position `L-1-i` and proves the lower error
with stride L; no free row reversal is assumed. The execution theorem preserves
source/destination suffixes and restores generated counts and work ports.
`PhaseCellRingRelease.releaseRingBatch_exec` generates both ring-symbol and
batch-total counts from exponent/width/batch headers, erases one padded batch,
releases both counts and preserves the exact borrowed suffix. Its bound is
`12*symbols + 9*M + 4*w + 6*2^l*w + 9*l + 26`. Guarded checks peak at
1807.6 MiB (lower crop) and 1821.5 MiB (ring release). The expanded S3
axiom audit passes in 4014 guarded build jobs (combined peak 4.0 GiB).
These components still
need composition with the triangular pair: crop into private workspace, remove
both padded result batches, then move the compact stream back to the persistent
output tail while clearing workspace. Both branches and the full cell/line
precision, setup and cost obligations remain open.

Compact triangular-pair endpoint (2026-10-25):
`PhaseCellResultPublish.publishPairResult_exec` releases both padded batches,
then transfers compact symbols in order through fresh workspace.
`PhaseCellPairFinish.finishTriangularPair_exec` composes lower extraction and
publication on the fixed bank. `compactTriangularPair_exec` now executes the
whole upper/staging/lower/release/extraction/publication chain from ordinary raw
operands on 117 tapes. Exactly one compact result prefixes the original output;
original operands, dimensions, native stacks and every work port are restored.
`compactPairCost` charges every constituent operation. Decoded lower error is
proved against the actual normalized upper numerators at reversed compact row
position `L-1-i`; there is no free rescaling or orientation change. The publication
and complete-pair checks peak at 1838.0 and 1829.6 MiB. The expanded S3
axiom audit passes (4016 guarded build jobs, combined peak 2.5 GiB).
Next: connect the two stages' explicit scales and errors to `CellRun.Valid`,
batch both generator branches, execute their merge/scalar arithmetic and generate
weights/generators. Boundary/coupling/recovery, full-line precision and uniform
S3 cost gates remain open. This endpoint does not mark S3 complete.

Triangular-stage scale checkpoint (2026-10-25): `PhaseCellPairScale`
connects compact upper operands and the actual published lower words to explicit
scaled stage errors. Bilinearity gives upper factor `a*b` and lower factor
`a*(a*b*2^l)`. Real projection loses no precision when raw generator words are
real; computed FFT intermediate rows may retain arbitrary imaginary rounding
noise. The real-stage error lemmas match the upper/lower arithmetic obligations
of `CellRun.Valid` on computed inputs. At generator scale 2 and input scale V≥0,
the proved tolerances are `4*V*2^l/2^q` and `8*V*(2^l)^2/2^q`. These are explicit
interpretations of stored numerators, not free tape rescaling or scalar arithmetic.
The guarded module check peaks at 1819.6 MiB. The expanded axiom audit
passes (4017 guarded build jobs, combined peak 2.5 GiB). Both generator branches, executed
merge/weight/reciprocal arithmetic and generated setup still need composition;
boundary/coupling/recovery, full-line precision and uniform costs remain open.

Both generator branches checkpoint (2026-10-25): `PhaseCellTwoBranches`
proves that concatenated generator/input banks produce the two compact branch
streams in order. `twoBranches_exec` runs all four triangular products through
the shared compact-pair program at batch size `M+M`, with one fixed-cost charge
per S1 call and exact raw-bank restoration. `PhaseCellDuplicateStream` and
`PhaseCellBranchInput.twoBranchesFromSingleInput_exec` execute the repeated
right-hand-side producer from one raw V stream, charging `6*M*L*w+6`; copy
workspace returns empty. The resulting repeated input remains installed in the
prepared bank, so its eventual release is still a caller obligation. Combined
generator construction and the doubled batch header remain explicit setup
inputs. Guarded checks peak at 1809.1 MiB (branch execution), 1799.2 MiB
(duplication) and 1809.8 MiB (single-input composition). Next: execute branch
merge and scalar arithmetic, generate coefficients/weights/headers, release
prepared input, and establish the full `CellRun.Valid` and line/cost endpoints.
The expanded S3 axiom audit passes (4020 guarded build jobs, combined peak
2.5 GiB). S3 remains active; boundary/coupling/recovery and uniform precision
are open.

Merge-word checkpoint (2026-10-25): the existing line-solver subtraction
automaton now lives in the small shared `Fast/SubWord` module. Its generic
`subWord_exec` proves exact full-stack framing and time `5*w+6` without a
multiplier-cleanliness hypothesis. `ResampBCore.rsb_subWord_runs` specializes
that proof, preserving its old contract and program; the duplicate automaton
execution proof was removed. `PhaseCellMergeWord.mergeWord_exec` proves that
one guard bit makes the actual reversed result word decode to the exact signed
difference. `value_sub` proves exact fixed-point subtraction. Guarded checks
peak at 1794.7 MiB (shared word) and 1885.2 MiB (merge word). This is the
arithmetic primitive for branch merge, not yet the stream loop or scalar
product. Those executions, generated cell setup and the full cell/line/cost
contracts remain open.

Merge-stream checkpoint (2026-10-25): `PhaseCellMergeStream.mergeStream_exec`
uses the existing Gaussian word-stream executor with the shared subtraction map.
No second per-word loop or subtraction implementation was introduced. Two
equal-length coefficient streams are consumed; the reversed exact-difference
stream prefixes the accumulator, and all other stacks (including width/tmp)
are restored. The bound is `n*(5*w+6)+2`, including empty streams, with w≥1.
The word guard-bit theorem supplies exact signed decoding; range hypotheses
remain separate from modular execution. Its guarded check peaks at 1895.4 MiB.
The expanded S3 audit passes (4288 jobs, combined peak 2.6 GiB), and the
refactored resampling core passes its guarded check at 1984.1 MiB.
The shared-word refactor passes regression builds for the old resampling line,
band factorization, S2 forward/supplier and S3 audits (13960 jobs, combined peak
4.4 GiB). Next: split the two published branch blocks into merge inputs with
generated counts, execute merge/publication and scalar multiplication, then
compose generated cell setup and the full numerical/line/cost endpoint.

Routed branch-merge checkpoint (2026-10-25): `PhaseCellTakePrefix`
consumes a counted prefix in original symbol order, preserving the suffix and
restoring workspace. `PhaseCellMergePublish.mergePair_exec` routes adjacent
branch blocks to the existing subtraction stream executor, then publishes the
difference in original word order above the exact output suffix. All temporary
stacks are cleared. `PhaseCellMergeSetup.mergeFromWords_exec` generates and
clears the total-symbol counter from word-count/width headers and charges the
whole chain by `n*(25*w+15)+22`. The word-count header remains explicit;
generating the per-branch count from cell descriptors is still setup work.
Guarded checks peak at 1805.5 MiB (prefix routing), 1922.7 MiB (routed merge)
and 1903.8 MiB (generated-count wrapper). The expanded S3 axiom audit
passes (4291 guarded build jobs, combined peak 2.6 GiB). Next: instantiate these stream contracts
on the two published branch lists, execute the reciprocal/scalar product, and
compose generated cell setup, `CellRun.Valid`, full-line correctness and costs.
S3 remains active; the entire inverse is not yet executed.

Executed four-product merge endpoint (2026-10-25): `PhaseCellHalfCount`
recovers M from the retained 2M header, preserving its actual symbols in
`6*M+4` steps. `PhaseCellBranchWords` generates ML and releases the half header.
`PhaseCellFixedMerge.fixedBranchMerge_exec` now generates every merge header
from 2M, L and w on the 117-tape bank, merges both adjacent result blocks, and
clears every header and work port; its bound is `ML*(25*w+21)+17*M+34`.
`PhaseCellMergedBranches.mergedBranches_exec` composes the one-input producer,
all four triangular products and the fixed-bank merge. Exactly one compact
branch-difference stream prefixes the original output, with the repeated-input
bank explicitly retained. `PhaseCellMergeRange.branchDifference_word` proves
that w≥q+3 recovers the exact signed difference from the actual output words;
there is no modular aliasing or extra rounding at merge. The two branch
numerators inherit the normalized disk bound from S1. Guarded checks peak at
1809.5/1813.5/1914.4/1894.2/1897.5 MiB for half-count, branch-count, fixed
merge, composed execution and range/decode modules. Next: execute reciprocal/
scalar arithmetic, generate coefficients, weights and headers, release the
prepared input and establish the complete `CellRun.Valid`, boundary/recovery,
line and uniform cost contracts. The expanded S3 axiom audit passes
(4296 guarded build jobs, combined peak 2.6 GiB). S3 is still active.

Shared scalar-kernel checkpoint (2026-10-25):
`PhaseCellScalarStream.realScalarStream_exec` reuses the real fixed-point table
multiplier with a one-word table for all merged coefficients. It restores the
operand/scalar streams and all other stacks, prefixes the actual product words
to the output, and charges `n*(rmulCost(w)+6*w+8)+6`. Its multiplier counters
and stored real scalar remain explicit inputs; setup and fixed-bank routing
have not yet been composed. `PhaseCellScalarRange` proves that actual compact
branch numerators have norm ≤1 and their merged difference norm ≤2. For a
stored scalar of norm ≤2, w≥q+4 proves product-word fit and signed decoding
with truncation error ≤`2/2^q` on the actual branch stream, without an output-fit
oracle. Guarded checks peak at 1889.6 MiB (kernel/bounds) and 1898.8 MiB
(branch range/error). Next: generate scalar readiness and the reciprocal word,
route and release the merged input around this call, execute output scaling/
weights and establish the full `CellRun.Valid`, boundary/recovery, line and
uniform cost contracts. The expanded S3 axiom audit passes (4298 guarded
build jobs, combined peak 2.6 GiB). S3 remains active.

Scalar-bank preparation checkpoint (2026-10-25):
`PhaseCellScalarPlacement` allocates the thirty scalar roles and 64 multiplier
tapes on the existing 117-tape bank. It proves injectivity, disjointness,
freshness after merged-branch execution and preservation of all retained
operands/dimensions/output ports. The exact three-counter readiness bank is
specified and proved sufficient. `PhaseCellScalarUnary.unarySetup_exec`
executes the binary q/w producer from unary ports 100/94, preserving both
source headers and all spectators; its cost is
`(q+w)*(4*w+10)+12*w+20`. No binary dimension words are supplied. The selected
w≥q+4, q≥1 guarantees q,w and the doubling program's temporary values fit
in binary width w. The unchanged thirty-role encoding was separated into
`ChirpOutputRoleCode` so scalar proofs do not import S2's entire output backend.
Next: compose binary-bank loading, the existing topN counter generator and
setup cleanup, then install the generated reciprocal word and route/release
scalar data around the actual multiply. Full cell/line correctness and uniform
costs remain open; S3 is active. Guarded checks for the final allocation and
unary producer peak at 1890.1 and 1899.8 MiB. The expanded S3 and both S2
regression audits pass (13967 jobs, combined peak 7.7 GiB, 1.2 minutes).

Generated scalar readiness checkpoint (2026-10-25):
`PhaseCellScalarBank.loadBank_exec` composes unary dimension conversion and
complete five-variable binary-bank loading. `PhaseCellScalarCounters` runs
the existing multiplier-dimension program and installs w, q and topN(w).
`PhaseCellScalarPrepare.prepare_exec` clears all 26 temporary setup ports,
with an explicit cleanup charge bounded by `52*w+53`; only the three actual
readiness counters remain changed. `prepareCanonical_exec` applies this to
the real 117-tape S3 bank and derives `Ready` plus clean multiplier tapes from
execution, without a prepared-state oracle. It preserves merged output, raw
operands, retained dimensions and native stacks. The unchanged table-role
encoding was separated into `ChirpBankRoleCode` to keep setup imports narrow.
Guarded checks peak at 1909.2 MiB (bank), 1897.3 MiB (counter generator) and
1934.5 MiB (complete setup). Next: route the merged words and stored scalar
into the generated-ready multiplier, publish and release its result/inputs,
generate the reciprocal/coefficient/weight data and establish the complete
cell/line numerical and uniform cost contracts. The expanded S3 and both S2
regression audits pass (13971 guarded build jobs, combined peak 7.7 GiB,
1.2 minutes). S3 remains active.

Executed scalar-application checkpoint (2026-10-25):
`PhaseCellTakeSetup` generates and releases a transfer count.
`PhaseCellScalarRoute.route_exec` generates ML from the retained doubled
header, routes the merged prefix into scalar operand port 84 and copies the
stored real factor from port 96 to 85. Every routing counter/scratch port is
cleared before multiplication; the factor source and original output suffix
are preserved. Readiness and multiplier cleanliness are proved to survive.
`PhaseCellScalarFinish` releases restored operand copies and publishes the
ordered product, clearing arithmetic data ports. `PhaseCellScalarRun` composes
the entire prepared pass. `PhaseCellScalarApply` adds generated readiness, and
`PhaseCellScalarCanonical.applyCanonical_exec` derives freshness/cleanliness
from the actual canonical bank, supplying the complete executed scalar pass
with decoded error ≤`2/2^q` and explicit setup/routing/product/release costs.
Readiness counters remain installed for reuse. Guarded checks peak at
1826.0/1921.6/1902.8/1916.3/1896.2/1892.4 MiB for generated transfer, routing,
finish, prepared run, setup/application and canonical entry.
The expanded S3 axiom audit passes (4323 guarded build jobs, combined peak
2.5 GiB). The stored factor is ordinary input data, not yet a generated reciprocal.
Next: retain/generate the reciprocal through the four-product stage (the raw
X suffix is a candidate storage location with proved S1 suffix support),
compose the entire cell arithmetic, generate weights/generators, release
prepared data/counters, and finish the cell/line error and uniform cost proofs.
S3 remains active.

Generator-suffix retention checkpoint (2026-10-25): the existing S3
programs now have proved generator-side suffix contracts through reversal,
upper multiplication, staging, lower multiplication, input release, compaction,
both branches, repeated-input production and final branch merge.
`mergedBranches_with_x_tail_exec` starts from one raw input stream and a suffix
beneath the combined generator bank, executes all four products and merge, and
restores that suffix exactly. A stored reciprocal word can therefore survive
under raw source port 110 while S1 uses its entire working bank. Runtime programs,
costs and numerical error bounds are unchanged; every original exact-stream
theorem is retained as the empty-suffix specialization of the same proof.
The counted access and scalar composition are now proved by the following checkpoint. Generating the
actual reciprocal, weights and generator data, prepared-data/counter release
and the complete cell/line numerical and cost contracts remain open. The expanded
axiom audit passes (4323 guarded build jobs, combined peak 2.6 GiB). All twelve
changed pipeline modules pass guarded single-file checks; the largest peak is
1914.7 MiB. S3 is active.


Retained-scalar composition checkpoint (2026-10-25):
`PhaseCellInteriorProducts.lean` proves `interiorProducts_exec` composes all four triangular products, exact branch subtraction,
counted reciprocal access, scalar counter setup, multiplication and staging-word
cleanup on the same 117 tapes. `copyAfterPrefix_exec` restores the full generator
prefix after copying its retained scalar, and `fetchCanonical_exec` derives all
access counts from the ordinary batch dimensions. The decoded result has error
at most `2/2^q` against the computed branch difference times the stored scalar.
`scaled_scalar_real_error` turns this into the real merge-stage bound after
rescaling, allowing imaginary FFT noise in intermediate rows. The reciprocal
word is still supplied numerical data; its generation is not proved. Repeated
inputs and multiplier counters remain explicit retained setup. Generated
coefficients/weights/reciprocal, complete `CellRun.Valid`, boundary/coupling/recovery
and full-line cost/error gates remain open. The expanded axiom audit passes
4327 guarded build jobs at 2.6 GiB combined peak; the composed theorem passes
its guarded single-file check at 1908.8 MiB. S3 remains active.


Real-stage handoff checkpoint (2026-10-25): `PhaseCellStageValues` identifies
cell coordinate `i` with stored reversed-row position `n*L+(L-1-i)` and proves
exact signed decoding of every compact branch numerator. Its
`upperNumerator_real_error` and `pairNumerator_real_error` give the real upper
and lower stage bounds on computed inputs: `4*B*2^l/2^q` and
`8*B*(2^l)^2/2^q`. Both generator branches use the same proofs, with real raw
generators and unrestricted imaginary FFT noise in intermediate rows.
`branchScalar_real_error` proves the actual output word satisfies the real merge
bound `8*B*(2^l)^2/2^q`. `cell_stage_precision` proves this latter budget is at
most `2^(-j)` when `B ≤ 2^b` and `b+2*l+j+3 ≤ q`; coefficient precision and address
width remain separate. No inverse-generator or reciprocal generation is assumed
proved: the reference generator still uses noncomputable `natInv`, and the
existing executable rational coefficient samples do not close that setup gate.
Full `CellRun.Valid`, weights, final rescaling, boundary/coupling/recovery and
line costs remain open. The new module checks at 1910.8 MiB, and the expanded
axiom audit passes 4328 guarded build jobs at 2.6 GiB combined peak. S3 is active.


Rational generator construction checkpoint (2026-10-25):
`NLogN.ToeplitzGeneratorIteration` defines a finite list recurrence with zero
initial vector, off-diagonal evaluation and an optional rounding map. Its
one-step and accumulated bounds are structural: error is at most
`rho^n*U+delta/(1-rho)`. Field embeddings commute with the unrounded recurrence,
so rational data give inverse-column approximations without evaluating `natInv`
or using a real rounding oracle. `NLogN.PhaseCellGeneratorData` instantiates this
constructor with the corrected executable rational coefficients of the actual
rounded cell matrix. It proves first-column and shifted-reverse accuracy,
computed corner at least `5/7` after one or more iterations, positive computed
reciprocal at most two, and reciprocal error at most twice the column error.
Choosing `j+1` iterations gives both column and reciprocal error at most `2^(-j)`.
This closes a numerical construction gap only: fixed-width encoding, tape
execution, setup costs and storage bounds are not yet proved. Weight setup,
full `CellRun.Valid`, final rescaling, boundary/coupling/recovery and full-line
contracts remain open. The data module checks at 1764.0 MiB; the expanded axiom
audit passes 4344 guarded build jobs at 2.5 GiB combined peak. S3 is active.


Encoded-generator checkpoint (2026-10-25): `PhaseCellGeneratorWords` constructs
real Gaussian numerators by computable rational floor arithmetic and proves the
grid error and exact zero imaginary component. Scale-two generator encoding
preserves the S1 numerator disk: the rational iterates have absolute value at
most `3/2`, so half-sized inputs and at least two grid bits absorb rounding.
`PhaseCellEncodedGenerators` constructs both generator banks and the reciprocal
word from the actual rational coefficient recurrence. It proves their lengths,
disk bounds, scalar norm at most two and accuracy against the actual rounded
matrix inverse. With `q ≥ j+2` and `j+2` iterations, each interpreted generator
and reciprocal is within `2^(-j)` of its target. Coefficient precision, arithmetic
precision, iteration count and storage width remain distinct. These constructors
close the numerical word/range obligations; tape generation, intermediate width
and bit-growth bounds, setup cost/storage, weights, full `CellRun.Valid`, final
rescaling and boundary/line contracts remain open. The expanded axiom audit
passes 4346 guarded build jobs at 2.5 GiB combined peak. S3 is active.


Constructed-data execution and cell-run checkpoint (2026-10-25):
`PhaseCellPreparedInterior.lean` proves `preparedInterior_exec` instantiates the 117-tape execution with the
constructed encoded generators and reciprocal, discharging their range and
reality conditions and returning their inverse-target accuracy. The setup bank
is still an input; this is not a setup-generation execution theorem.
`PhaseCellInteriorRun` interprets the computed upper/lower arrays and the actual
scalar output tape as `CellRun` fields, retaining reversed-row coordinates,
ring factors and input magnitude scale. `interiorRun_valid` derives the
triangular, merge and input-magnitude clauses structurally.
`preparedRun_valid` additionally derives generator/scalar accuracy from the
constructors and uses `q ≥ b+2*l+j+3` for `B ≤ 2^b`. It establishes
`CellRun.Valid` at tolerance `2^(-j)` conditional on exactly the three remaining
weight-stage errors: reciprocal weights, scaled input production and final
weight multiplication. Those hypotheses are pending work, not executed stages.
Setup tape generation/cost/storage, these weight stages, final word conversion,
boundary/coupling/recovery and the line endpoint remain open. The conditional
cell-run module checks at 1918.4 MiB; the expanded axiom audit passes 4367
guarded build jobs at 2.6 GiB combined peak. S3 remains active.


Complete numerical cell-run checkpoint (2026-10-25): `PhaseCellWeightData`
constructs reciprocal-weight, normalized-input and final-output Gaussian words
by rational floor arithmetic on the actual selected similarity samples and
computed inputs. It proves each rounding error and the reciprocal-weight range.
For RHS magnitude at most `2^cExp` and weight lower bound `2^(-e)`, normalization
by `2^(cExp+e+1)` places the rational encoder argument within `1/2`; at least two
grid bits therefore give the S1 input disk. `PhaseCellNumericalRun` uses
`inputExponent p cExp = cExp+(8*p+1)+1` and constructs all `CellRun` fields from
rational data and the actual interior scalar-output tape. `numericalRun_valid`
proves the complete `CellRun.Valid` contract with no assumed stage-error facts,
at tolerance `2^(-j)` when `q ≥ inputExponent p cExp+2*l+j+3`. It preserves
ambient coordinates and the selected coefficient precision `2^15*p`.
This is a complete numerical-data/validity theorem, not a composed tape solver:
setup and weight-stage execution, intermediate word/bit-growth fits, final
conversion/publication, setup and line costs, boundary/coupling/recovery remain
open. In particular the computed numerical `y` fields have not yet been produced
on the output tape. The numerical-run module checks at 1906.3 MiB; the expanded
axiom audit passes 4369 guarded build jobs at 2.6 GiB combined peak. S3 is active.


Executed weight-input checkpoint (2026-10-25): `PhaseCellWeightStream`
uses the existing `rmulOne`/`cmulStream` engine for aligned varying real weights.
It keeps arithmetic grid precision `q`, normalization `b`, multiplier counter
`q+b`, magnitude exponents and word width separate. Its output is the actual
`tdivN (q+b) (x*a)`, with error at most `2/2^q` against the normalized product,
proved signed-word fits and exact input/table/private-stack restoration.
`PhaseCellWeightedInput` constructs reciprocal table words from the rational
weights. Their lower bound `2^(-e)` and RHS norm bound `2^cExp` discharge operand
fits; normalization `b=cExp+e+1` makes every actual output satisfy the S1 disk.
The interpreted real input-stage error is at most `2^b*2/2^q`, hence at most
`2^(-j)` when `q ≥ b+j+1`. No output-fit oracle is required. The stream's cost is
`N*(rmulCost w+6*w+2)+8`. `ScalarFinish.finish_stream_exec` generalizes the existing
cleanup proof to an entire factor stream, with unchanged runtime code; the old
single-scalar theorem is its singleton specialization.
This addresses machine truncation toward zero directly. The earlier rational
floor-based numerical run is not asserted equal to the machine data. Fixed-bank
routing, generation of the `q+b` readiness counters, setup generation, final
weight multiplication/publication and boundary/line composition/costs remain
open. Guarded checks peak at 1897.5 MiB (generic stream), 1902.9 MiB (input stage)
and 1903.0 MiB (shared cleanup). S3 remains active.


Closed 117-tape input-weight checkpoint (2026-10-25):
`PhaseCellWeightRoute` generates one `M*L*w` symbol counter for both source
transfer and table copying, then releases it and the row count. Its cost is
`22*M*L*w+15*M*L+17*M+34`; the complete table suffix is preserved.
`PhaseCellWeightRun` composes routing, the existing varying-weight multiplier
and shared stream cleanup. `PhaseCellWeightPrepare` temporarily extends the
actual unary precision header by the normalization descriptor on port 116,
executes readiness generation at `q+b`, then restores the original precision
and descriptor symbols. Only the three counters remain; their paid release is
proved too. `PhaseCellWeightClose.lean` proves `ScalarPlacement.closedWeights_exec`
executes setup, routing, multiplication, publication and counter release,
changing only the persistent output prefix. `closedWeightedInput_exec` supplies
the constructed reciprocal words, derives operand fits and the S1 output disk,
and gives real-stage error at most `2^(-j)` for `q ≥ b+j+1`, with
`b=cExp+e+1`. No readiness, routing-count or output-fit oracle remains.
Ordinary descriptor/data headers and reciprocal words are still input data:
executing their setup constructors and integrating the normalized stream into
the interior bank remain open, as do final weighted publication, bit-growth and
storage bounds, boundary/coupling/recovery and the full line endpoint and costs.
The expanded axiom audit passes 4377 guarded build jobs at 2.6 GiB combined
peak. S3 remains active.


Closed final-weight stage checkpoint (2026-10-25): `PhaseCellOutputBounds`
proves that the actual scalar result has norm at most four. Restoring its
cell scale is the exact numerator shift `d=b+2*l+2`, with
`2^d=4*2^b*(2^l)^2`. Both shifted operands and final products fit at
`w ≥ q+d+4`. The final error charges multiplier truncation and weight encoding
at the restored magnitude: `(2+2^(d+2))/2^q`. Consequently the complete final
weight-stage tolerance `2^(-j)` needs `q ≥ d+j+3`, or `b+2*l+j+5`, two bits
beyond the triangular-stage budget.
`PhaseCellOutputScale` generates counts, isolates the owned output prefix,
executes the existing shift machine and restores its staging, leaving the
borrowed suffix unchanged. `PhaseCellOutputClose.lean` proves `ScalarPlacement.closedOutputWeights_exec`, which saves the shift header, reuses the closed
aligned-weight pass at extra shift zero, and restores the exact header symbols.
Only the weighted output prefix changes; no readiness or output-fit oracle is
supplied. Its explicit cost is prefix rescaling plus `closedWeightsCost q 0`
and `4*d+4` for header saving/restoration. `PhaseCellOutputData` proves decoded
word accuracy against the actual rational similarity weights.
Data/descriptor generation, integrating stage banks and their computed arrays
into the complete cell execution/validity theorem, final line ordering/conversion,
boundary/coupling/recovery and line/setup/storage costs remain open. Both weight
stages now execute as standalone 117-tape components. The expanded axiom audit
passes 4398 guarded build jobs at 2.6 GiB combined peak. S3 remains active.


Actual-arithmetic cell-validity checkpoint (2026-10-25): `PhaseCellRowTable`
proves that compact index `n*L+(L-1-i)` selects row `n` and cell coordinate `i`.
The final similarity table uses this actual reversed order, with ambient phase
coordinates unchanged. `PhaseCellExecutedData` constructs the actual normalized
input numerators, scalar interior stream and final shifted/weighted output
words from raw Gaussian RHS data. Input disk, input-stage error and scalar
magnitude bounds are derived from the constructors and selected weight bounds.
`executedRun_valid` in `PhaseCellExecutedRun.lean` proves the complete real `CellRun.Valid` contract for these actual stage words and decoded
output symbols, with no stage-error assumptions and no equality with the
rational-floor reference. The common bounds are
`q ≥ inputExponent p cExp+2*l+j+5` and
`w ≥ q+inputExponent p cExp+2*l+6`, at tolerance `2^(-j)`.
The shared `inputExponent` definition moved to `PhaseCellWeightData`; the old
numerical-reference API retains the same definition and behavior.
This composes the numerical contracts of the individually executed stages;
it does not yet provide their complete bank-to-bank tape execution. That
composition, data/descriptor generation, final ordering and complex/line
endpoint, boundary/coupling/recovery and full setup/storage/line costs remain
open. Guarded checks peak at 1910.7 MiB (actual run), 1902.1 MiB (stage data)
and 1891.8 MiB (row table). The expanded axiom audit and
reference regression pass 4401 guarded build jobs at 7.5 GiB combined peak.
S3 remains active.


Input/interior execution composition checkpoint (2026-10-25): `PhaseCellInputRows`
proves structurally that the aligned product on a flattened batch is exactly
the flattening of its rowwise products. `PhaseCellInputInstall` derives the
transfer count, installs the normalized stream on raw input tape 111, and pays
for releasing the owned table copy and normalization descriptor. Its endpoint
is exactly `singleBranchInputWithXTail`, including the unchanged borrowed X
suffix and persistent output tail. `PhaseCellInputStage` starts from raw RHS
words, constructs the actual normalized words through execution, and installs
them. `PhaseCellInputInterior` then executes the four triangular products,
merge and retained scalar multiplication; no normalized-input data is assumed
in its initial bank.
`PhaseCellExecutionSizing` proves a conservative controller-compatible choice:
`cExp=rhsExp+2*l+j+5`, `b=inputExponent p cExp`, `q=2*b`, `w=4*b+8`.
It preserves the given RHS bound and satisfies the actual-run validity and
final word-width bounds. `PhaseCellNormalizationHeader` uses the existing
half-count machine on the precision header to generate the normalization
count, preserving all actual header symbols. `inputInteriorFromPrecision_exec`
therefore needs an empty normalization slot initially, and includes its
`6*b+4` generation cost. Every other input/interior setup, routing and owned
staging release cost is included. The interior endpoint still explicitly
retains its repeated raw input and three scalar counters.
Coefficient/table data generation, output-control and table loading after the
interior stage, final stage composition and ordering, complex/line correctness,
boundary/coupling/recovery and uniform setup/storage/line costs remain open.
The even-precision choice has not yet been matched into a uniform line budget.
The expanded axiom audit passes 4407 guarded build jobs at 2.5 GiB combined
peak. S3 remains active.

Historical resampling/outer-integration estimate (S2–S6, before S2 completion): **24–48k additional or substantially
revised Lean lines**, excluding R1–R4, M9–M10 and generated data. This is a lower-confidence
scope estimate, especially for fused execution and boundary work, not a delivery-time
estimate. The rows partition the intended work; shared helpers should be proved once.
S1 is complete independently of root imports and Routing. `ShortConv.Fixed.closed_exec`
packs raw batches, generates headers/counters, invokes one shared ring product and
clears generated workspace. Only the output changes; inputs, dimensions, scratch and
spectators are restored, including empty batches. `output_coeff` proves exact signed
coefficient recovery and `output_err` bounds rescaled error by `2r/2^p`. The fixed cost
is `ShortConv.Fixed.cost`; setup outside its per-record term is paid once per batch.

S2 is complete as a standalone forward primitive. The component contracts below
record its construction; the final completion audit follows the progress notes:

- **Correlation:** `chirpTableCorrelation_exec` generates G/K tables, gathers windows
  from the raw line, produces weighted/reversed operands, installs S1 dimensions,
  executes one shared product/extraction and erases all temporary streams/counters.
  Only the correlation destination changes. Its cost is `chirpTableCorrelationCost`;
  retained binary banks and multiplier templates are still supplied.
- **Output caller from binary banks:** `chirpOutputFromBanks_exec` generates both E
  and normalization tapes, installs all nine counters, executes both shifts/products,
  rounding and crop, then erases all generated factors, counters and intermediate
  streams. Its program is dimension-independent; `chirpOutputFromBanksCost` charges
  every phase. Only the consumed correlation source and final output change.
  Binary dimension/factor banks and multiplier readiness are still supplied.
- **Reusable output interface:** `ChirpOutputLayout` packages the static wiring and
  shared intermediate; `chirpOutputRun_exec` restores counters and factor tables,
  allowing setup to be reused across lines. `OutputPlacement.layout` gives a checked
  146-tape allocation for the arithmetic registers, independent of all dimensions;
  the complete caller's table banks and correlation registers still need allocation.
- **Returned-tape mathematics:** `chirpForwardTape_value` identifies every actual
  retained word with the computed analytic map, including the final partial block.
  `chirpForwardSelected_error` proves scaled error at most 4 for the exact integer
  output list using explicit choices: `m = α(⌊√p⌋+1)`, `Γ = 32p`,
  `l = ⌈log₂(7m)⌉`, `q = p+2Γ+l+13`. For `α ≥ 1` and `α² ≤ p`, all window,
  exponential and accumulated-error gates follow; no numeric gate oracle remains
  in this mathematical theorem. It does not yet execute the complete caller.
- **Selected sizing:** `chirpForwardWidths_le` bounds the working precision and
  input/output widths linearly in p. `chirpForwardTableWord_good` supplies a common
  evaluator bank width `13q+8 size(B)+16` at both q and q-Γ. The actual
  `tblChirpForwardWindow_do` program computes the selected m from p and α by a
  proved integer root-search loop, with checked intermediate fits.

`chirpForwardOutput_length` proves exactly t outputs; generated correlation rows
supply the output-stage unit-disk bounds. The generic `chirpOutputTape_word` bridges
the executed row-periodic arithmetic to scalar semantics. These are checked data,
error and component-execution theorems, not yet one complete original-input machine.

**Caller initialization progress:** `chirpBankLoad_exec` now initializes every table
variable and both length headers from raw caller words and counters; input words
may share sources, including a common empty zero source. `chirpBankLoad_holds`
establishes the full evaluator bank contract. `chirpBankClear_exec` charges release
of every variable and header, and `chirpBankClear_load` proves exact restoration
of the entire register function for a fresh bank. `chirpOutputMultiplierSetup_exec`
computes q, w and topN(w) counters for both output multipliers from one reusable
binary bank; `chirpOutputMultiplierSetup_base` establishes their readiness from
fresh arithmetic registers. The initialization/release standard-axiom audit and
guarded build pass. These generic contracts still need instantiation and composition
with the complete selected-parameter caller; they do not close S2.

**Selected scalar generation:** `tblChirpForwardParameters_do` now composes the
root-search window, ring-power doubling and fixed precision arithmetic in one
13-variable program. Only p and α are supplied: it computes m, l, Γ, q and both
signed word widths, preserving p, α and the accumulator. Its bound is
`4*(sqrt(p)+1)+7 + (4*l+9+36)` table atoms. The single condition
`125*p < 2^W`, together with p≥1, α≥1 and α²≤p, pays every intermediate fit.
The three added modules pass guarded file checks below 2 GiB. This removes the
remaining principal selected-scalar arithmetic assumption; installing these words
into all consumer banks and the complete caller's volume/address sizing remain open.

**Computed consumer installation:** `chirpBankClone_exec` executes bank loading
directly from retained computed table variables and their two length headers,
with all source roles and spectators preserved. `chirpForwardOutputBank_exec`
now composes the selected-parameter program with that installation: from p, α,
a zero source and t in the source bank, it establishes the complete 14-variable
output-dimension bank, including all eight zero workspace words. It bounds the
full selection/conversion execution and preserves input, output, left stacks and
every register outside the two banks. `tblChirpForwardParameters_do` additionally
proves all final parameter words fit the common binary width, enabling copying
without a fit oracle. The new clone/output-bank file checks pass at 1762.4 and
1834.4 MiB; the strengthened parameter check passes at 1881.6 MiB. Original
source-bank initialization, the other consumer banks and complete machine
composition remain open.

**All consumer-bank assignments:** `tblChirpForwardCallerParameters_do` extends
selection with the binary block count `(t-1)/m+1`, reusing two retired ring-search
workspace slots. Its source bank retains p,α,s,t and zero and proves every final
word fits. `chirpBankFamily_exec` installs a structural list of disjoint consumer
banks once, preserving the source and every spectator. `chirpForwardConsumers`
specifies the gathering, S1-dimension, output-dimension, coefficient and multiplier
banks, including coefficient slot 43's generated block count. The composed
`chirpForwardConsumerSetup_exec` executes selection and family installation with
one total bound and complete frame. It also executes `chirpBankEmissionSetup_exec`
to replace the source emission header by computed w before installing the banks;
the coefficient word-width counter is no longer a selected-value input. This
conversion has a linear cost `2*e+2 + 6*w+11*W+6`, including clearing the old
header. The five new modules pass individual guarded checks (peaks 1833.7,
1770.9, 1824.1, 1312.4 and 1821.3 MiB). These contracts still assume a disjoint
bank layout and supplied initial source bank/length counters. Concrete placement
and initial source loading remain necessary before this supplies the complete
original-input caller.

**Concrete banks and raw source loading:** `ForwardBankPlacement` allocates the
16-variable source and all five consumer banks in exactly 193 tapes, proving
each map injective, every consumer disjoint from the source and all consumers
pairwise disjoint. This discharges the bank-family layout conditions, but does
not allocate the additional correlation and arithmetic registers.
`chirpForwardSourceLoad_exec` initializes the complete source bank from four raw
b-bit binary words p,α,s,t and one shared empty source. The sixteen padded
variables, W-length header, zero-length initial emission header, accumulator
and twelve scratch roles are all established; only source-bank registers change.
Its exact cost is `100*W+8*b+137`, with b≤W. A W-length caller counter is still
supplied. The placement and loader guarded file checks pass at 1822.0 and
1776.8 MiB. These pieces still require full setup/caller composition and a common
allocation including raw inputs and arithmetic/correlation workspace.

**Raw setup composition and common fits:** `chirpForwardRawSetup_exec` now
executes raw source loading, selected scalar computation, computed emission-width
conversion and consumer installation as one program. Its postcondition retains
the full computed source semantics, every installed bank and the complete
spectator/native/left-stack frame, with all phases in its cost bound. No initialized
bank is supplied. `chirpForwardCaller_fits` chooses `B=max(s,t+125p)` and the
existing `W=13q+8 size(B)+16`; it proves the raw scalar words fit `size(B)` bits,
`size(B)≤W`, `125p<2^W`, emitted width≤W, table argument bounds, all gathering
address/volume gates, output crop volume and S1/multiplier dimension fits. The
proof uses one generic quadratic envelope, not per-case certificates. Both
new file checks pass (1828.4 and 1870.1 MiB). A W-length caller counter is still
supplied; complete arithmetic/correlation placement and execution, shared line
setup and the final actual cost comparison remain open.

**Actual connected line execution:** `chirpForwardLine_exec` now composes the
raw-line correlation program with `chirpOutputRun` directly, using the generated
correlation rows' proved lengths and norm bounds. It returns exactly
`cstream A (p+l+Γ+5) (chirpForwardOutput ... u)`. Only the final output tape
changes: the consumed correlation input returns to its original empty state,
and all raw input, coefficient factors, counters and arithmetic/S1 workspaces
restore. The bound is the sum of the actual raw-correlation and output costs.
`ChirpOutputState.supplyInput` and `ChirpOutputLayout.consumeInput` prove the
state connection and final restoration structurally over arbitrary rows/streams.
The output-layout and connected-line file checks pass at 1910.7 and 1930.4 MiB.
This is retained-setup line execution: its bank/readiness/layout preconditions
still need the prepared caller and full finite placement, and grouped line
iteration/shared setup and the final total-cost comparison remain open.

**Connected-line placement progress:** `LinePlacement` now embeds the checked
146-tape output arithmetic, 193-tape table allocation and 117-tape shared product
in one fixed 640-tape space. A separate 30-role processor shares the restored
64-tape multiplier bank; raw gathering and correlation extraction have disjoint
private ranges, with the extraction destination linked to the output input.
`ringLayout`, `batchLayout`, `output_cross`, processor/raw injections and the
raw-input link are proved. Structural support checks prove correlation dimensions
injective and disjoint from scratch/operands, with the private product bank
separate from dimensions and operands; range arguments separate table banks from
raw gathering. The module's file check peaks at 1977.8 MiB. These are core static
placement facts, not yet every producer/control separation or a fully instantiated
line execution: installing the computed data/readiness and composing the actual
caller, shared-line iteration and the final cost comparison remain open.

**Fixed selected-line execution:** `LinePlacement.program` is now one fixed
640-tape raw-line program. `program_exec` instantiates `chirpForwardLine_exec`
with the concrete allocation and discharges every register-layout/separation
hypothesis, including the remaining producer controls. Its caller supplies no
layout or execution oracle. `selected_program_exec` additionally selects m,l,Γ,q,w,B,W
from p,α,s,t and proves every numerical fit, window condition and generated-E
norm bound, using only s<t, α≥1 and α²≤p. Both the generic fixed and selected
contracts change only the final output tape and retain setup. The new control,
fixed-line and selected-line file checks pass at 1928.1, 1948.7 and 1951.6 MiB.
Prepared G/K/E/normalization tapes, multiplier readiness, consumer banks and
counters are still data preconditions: the raw setup must establish and scope
these around the fixed line, with grouped iteration, complete cleanup and the
final actual cost comparison still open.

**Fixed-line readiness and table setup:** `LinePlacement.readiness_exec` now
executes all three multiplier setups from the same retained q,w bank, restoring
that bank and charging at most three setup costs. `readiness_ready` proves the
producer's full Ready interface and both output-base interfaces from fresh data
registers. `tables_exec` generates G,K,E and normalization once using the same
restored coefficient evaluator bank, changing only the four destination tapes.
Their exact spectator frames support setup composition. A sizing gap exposed by
the padded table scheduler was fixed: the common base is now `max(s,t+125p)`,
so `chirpForwardCaller_tableBounds` proves M≤B, M*m≤B and 4m+1≤B even when
the last block extends past t. All earlier caller fits still pass. Readiness,
tables and revised sizing file checks peak at 1927.3, 1920.7 and 1869.6 MiB.
These programs still need composition with the generated bank contents and
output-counter installation around the fixed line; grouped execution, cleanup
and the final actual cost comparison remain open.

**Composed arithmetic preparation:** `LinePlacement.arithmeticSetup_exec` now
executes readiness and four-table generation together, retaining both binary
banks and charging every phase. `arithmeticSetup_prepared` proves that from fresh
producer/output registers and clean multiplier workspace, its exact final state
has producer Ready, the exact G/K streams and the full output factor/readiness
interface. `tables_prepared` proves the key composition: G/K writes preserve
both output interfaces, while E/normalization writes preserve producer readiness.
No prepared arithmetic-interface oracle is introduced. Generic table-bank versus
processor/output separation replaces duplicated multiplier-only range proofs.
The readiness, composed execution and final prepared-state checks peak at
1926.9, 1914.3 and 1919.3 MiB. Generated raw-bank setup and nine output counters
still need composition with this state around the fixed line; grouped execution,
full cleanup and the final actual cost comparison remain open.

**One complete retained line-preparation stage:** `LinePlacement.prepare_exec`
now composes multiplier readiness, G/K/E/normalization generation and all nine
output counters in one executed program. Its exact final state is the counter
installation over the table/readiness state, and its bound charges every phase.
`prepare_state` derives producer readiness, exact G/K streams, the full output
state, all nine counter lengths and empty output scratch from fresh data/control
registers. `counters_prepared` proves counter writes preserve the existing
arithmetic interfaces. Generic bank frames prove the earlier phases retain the
dimension bank and output controls until installation. Counter and full-preparation
file checks peak at 1935.5 and 1920.5 MiB. The generated raw scalar/consumer-bank
setup still needs to feed the preparation's bank hypotheses, followed by full
fixed-line composition, grouped reuse, cleanup and the final cost comparison.

**Computed-bank to preparation bridge:** `LinePlacement.bankSetup_exec` now
instantiates raw scalar loading, parameter selection and all consumer-bank
installation in the fixed 640-tape layout, including concrete scalar-input and
width-counter positions. `consumer_state` derives the five exact bank schemas
from its computed source, with coefficient-owned zeros and inherited fits proved.
`prepare_from_source` then executes the full readiness/table/counter preparation
using those bank schemas, deriving all of its numeric/table-schedule conditions
from selected sizing and the source semantics. The proof uses direct natural
inequalities and existing source-word fits, with default proof limits retained.
The bank-state, fixed raw setup and source-to-preparation checks peak at 1952.7,
1919.7 and 1940.7 MiB. `outside_banks` supplies the arithmetic/product/raw-workspace
spectator frame. The fixed raw setup and preparation executions still need chaining
with those fresh-state/frame contracts, then the fixed line, grouped reuse,
final cleanup and total cost comparison.

**Raw-input initialization is now chained:** `LinePlacement.initialization`
is one fixed program executing raw bank setup followed by full arithmetic/table/
counter preparation. `initialize_exec` starts from p,α,s,t words of selected
width and the stated W-length counter, constructs every bank and executes
preparation, with no initialized-bank or prepared arithmetic oracle. It retains
the computed bank-stage witness and an explicit full initialization cost.
`initialized_prepared` carries fresh initial arithmetic registers through the
bank-setup frame and derives all producer/table/output/counter interfaces in
the exact final state. Its guarded file check peaks at 1933.1 MiB. Remaining
raw/product workspace and data frames must connect initialization to fixed-line
execution; grouped reuse, final cleanup and the total-cost comparison remain open.

**Initialized raw-line machine with returned-tape error:**
`LinePlacement.initializedLine_exec` now executes initialization followed by the
selected fixed line in one 640-tape program. Inputs are raw scalar words, the
raw line, the stated selected W-length counter and fresh workspace; no prepared
bank, table, multiplier, numerical gate or layout hypothesis is supplied. The
actual returned tape is decoded by `readOutput`, and the same execution theorem
proves scaled resampling error at most 4 for that decoded result. Its bound
includes initialization, correlation and output arithmetic. Setup remains
allocated for reuse: this is not the final cleaned/grouped S2 contract.
`preparedStack_off` proves the exact 22-tape preparation footprint; structural
support checks transport all raw, producer, product and dimension workspace
conditions, including product left/private-stack cleanliness. Initialization
also retains the source accumulator's empty-state proof for cleanup. The frame
and initialized-line checks peak at 1978.8 and 1942.4 MiB. Grouped execution,
setup cleanup/restoration and the final actual cost comparison remain open;
the W-length counter is still a stated caller input.

**Executed setup release:** `clearPrepared_exec` erases exactly the 22-tape
preparation footprint at cost twice its symbol volume plus 45; its line-result
restoration theorem preserves the output and returns those tapes to their original
fresh values. `chirpBankFamilyClear_exec` structurally releases disjoint generated
banks. The fixed six-bank instantiation clears all source/consumer variables and
headers in exactly `218W+12w+243` steps and proves every bank role empty.
`release_exec` composes preparation and bank release, and `release_lineResult_exec`
feeds it directly from the initialized-line bank witness. `releasedStack_readOutput`
proves the actual decoded output, hence its error bound, is preserved. Freshness
of preparation support follows from the initial fresh arithmetic state and raw
bank frame. The four release file checks peak at 1939.7, 1801.9, 1927.6 and
1924.2 MiB. The releases still need composition into the complete restored caller,
with grouped reuse and the final actual cost comparison remaining open.

**Closed raw-input single-line caller:** `LinePlacement.closedLine_exec` now
composes initialization, selected line execution and full release. Its final state
is exactly the original state with only the returned output tape replaced; all
raw/scalar inputs, width counter, binary banks, factors, readiness/output counters,
private/product workspace, native stacks, left stacks and arbitrary spectators
restore. The actual decoded output retains scaled error at most 4. Every phase
is charged, including symbol-volume preparation release and exact six-bank release.
The stronger original bank-setup spectator frame is now retained through execution;
`released_lineResult_eq` uses a structural bank-ownership case split rather than
an enumeration of the finite register space. Restoration and closed-caller file
checks peak at 1922.3 and 1926.6 MiB. The current bound still exposes the retained
bank-stage witness inside release-volume cost; reducing it to selected numerical
parameters belongs to the final cost comparison. Grouped execution sharing one
setup/release across lines is still open; the W-length counter remains a stated
caller input.

**Grouped-line transfer support:** `stageLine_exec` consumes the next raw line
from the batch cursor, archives its original symbols and supplies the line-input
tape. `collectLine_exec` clears that staged copy and collects the result, returning
both temporary line ports to empty. `group_roundTrip` proves the combined exact
register effect changes only the three group data ports, preserving every setup
register. `finishGroup_exec` reverses the two archives once to restore the original
input prefix and publish output lines in order. `lineSymbolsSetup_exec` computes
the shared s*w symbol counter from source words 14/11, reuses the zero slot and
restores the entire source bank; its cost is paid once per group. The three new
file checks peak at 1923.4, 1920.5 and 1927.0 MiB. These are executed transfer/counter
components and an exact round-trip state lemma, not yet the repeated prepared-line
loop. Connecting retained-line readiness through staging and proving that loop,
then scoping one initialization/release and closing total costs, remain open.

**Executed reusable grouped step:** `LineData` packages the retained tape facts,
excluding the replaceable raw input. Its frame theorem and `LineData.stage`
prove readiness survives staging; `SelectedLineData.exec` invokes the actual
selected forward program from that interface. `groupStep_exec` now composes
staging, forward execution and collection, with an exact final state changing
only the batch cursor and two archives. Its bound adds
`16 * inputSymbols + 2 * outputSymbols + 18` to the actual line execution bound.
`groupStepR_low` and `LineData.groupStep` prove every line/setup tape and the full
retained interface are ready for reuse. The data and step guarded checks peak at
1941.1 and 1930.3 MiB. The repeated counted loop, one group-wide initialization/
release, grouped error/restoration and final numerical cost comparison remain open.

**Executed counted prepared group:** `groupLoop_exec` now structurally executes
an arbitrary list of bounded input lines with the actual fixed line program,
retaining setup between lines. Its exact state accumulates both reversed archives
and saves every consumed count symbol; the cost adds three control steps per
line and the final loop test. The register recurrence is proved separately over
arbitrary streams, avoiding simplification through the numerical/data context.
`preparedGroup_exec` tests the supplied count, executes that loop, restores every
count symbol, restores the original raw batch and publishes outputs in line order.
Its final state is exactly the original prepared state with only `groupOutput`
prepended by the output batch. Its bound is the sum of executed line bounds plus
`5 * lineCount + 2 * inputSymbols + 2 * outputSymbols + 8`; both archives and the
saved-count tape start and finish empty. The loop and prepared-group guarded
checks peak at 1967.2 and 1934.9 MiB. One initialization/release around this group,
the decoded grouped error contract and final numerical cost comparison remain open.

**Closed raw-input group with one shared setup/release:** `initialized_lineData`
now derives the retained interface from initialization's bank witness; the existing
single-line caller reuses it instead of duplicating setup reasoning.
`initializedGroup_exec` executes raw initialization, generates the shared s*w
symbol counter and runs the prepared group. It retains the exact source/consumer
bank witness and original spectator frame for final release. `groupRelease_exec`
erases the shared symbol counter and releases all preparation and binary banks.
The generic `releasedStack_eq_of_frame` proves restoration whenever only owned
setup differs, including arbitrary spectators. `closedGroup_exec` composes all
phases in one dimension-independent program: only `groupOutput` changes, receiving
the complete output batch in order before its original suffix. All raw/scalar
inputs, count symbols, archives, banks, left/private/native stacks and spectators
restore. Initialization/data, refactored single-line, initialized-group, release
and closed-group checks peak at 1924.6, 1930.9, 1947.0, 1929.6 and 1927.4 MiB.
Every phase is charged, but the cost still contains the bank-stage witness in
release symbol volume and data-dependent output lengths. The decoded grouped
error contract and final numerical cost comparison remain open; the W-length
counter remains a stated caller input.

**Published grouped error and scalar-only cost:** `take_drop_flatten_map`
recovers arbitrary equal-width rows from a flattened batch before any suffix.
`readGroupLine_published` identifies each actual published row with the selected
forward decoder, and `publishedGroup_error` proves scaled error at most 4 for
every line at its actual output offset. `GroupOutputError` packages that formula
without expensive typeclass elaboration inside the full caller statement.
`groupInputBatch_length`, `groupOutputBatch_length`, `groupLineCost_sum` and
`groupRunCost_eq` reduce all data-dependent line and batch costs to scalar
parameters. `LineData.clearPreparedCost` computes the exact release volume from
the retained tape interface; high group ports do not contribute. It is
`2 * (3 * (w+q+topN w) + (M*(7m+1)+m+1)*w + 4*w + t*(p+l+Γ+5)) + 45`.
`closedGroup_exec` now gives one complete execution, exact original-state
restoration except output, the decoded error for every published line, and
`n ≤ selectedGroupCost s t α p us.length`. There is no intermediate bank-state
witness or data-dependent length in this cost bound. Cost equalities are
transported structurally through the setup/release sum, avoiding rewriting
through the full evaluator cost definitions. Decode, length/cost, release-volume
and strengthened closed-group checks peak at 1927.2, 1919.6, 1949.8 and 1931.3 MiB.
The final comparison with the intended fast-resampling cost bound remains open;
no multiplication bound or kappa change is claimed.

**Linear conversion budgets and exact group amortization:** The host already
proved `toUnary_exec_linear` for the actual unchanged Horner program. All chirp
counter-list conversions, advance-packet emission and block-count setup now use
that theorem, charging `6*x+11*W+6` instead of the former width-times-value
budget. The sharper costs propagate through cyclic/multiplier/output/operand/S1
counter setup, raw gathering, the complete group caller and `selectedGroupCost`.
The shared symbol-counter setup now costs at most `2*tblC W w + 6*s*w + 11*W + 7`.
Control generation charges `M*(6*tblC W e+11*W+14)+8*D+6*tblC W e+6`, where
`D=chirpCenter s t m M*w`; the complete gather setup charges
`M*(6*tblC W e+11*W+14*((3*m+1)*w)+41)+22*D+6*tblC W e+16`.
These remove spurious W factors from generated symbol volume, with no program,
layout or correctness change. `selectedGroupCost_affine` separates the exact
shared zero-line cost from `N*selectedGroupUnitCost`. The counter-list and affine
cost checks peak at 1322.4 and 1932.0 MiB. The rebuilt caller/audit passes.
The remaining per-line budget still regenerates the fixed advance schedule,
including `6*M*tblC W w`; the sweep itself already restores that schedule.
Retaining this group-invariant schedule is the next cost-comparison work item.
The current explicit budget is not yet claimed to meet the intended fast bound.

**Retained-schedule execution and generated shared controls:** `chirpGatherMode`
now selects the existing generated-schedule sweep or the actual retained-schedule
sweep. `chirpRawGatherWith_exec` shares one cyclic-copy and cleanup proof for both
modes; `chirpGatherFromDimensionsMode_exec` either generates its count/schedule
or borrows and restores them. `ChirpRawReady` states those concrete tape facts.
Correlation, forward-line arithmetic and fixed/selected allocation are now proved
over either mode, with `programWith` as the common fixed program. The original
`program` remains its generated-schedule instantiation. `LineData`, its frame,
staging and collection lemmas, and the counted/prepared group execution now carry
the mode, so the actual group loop can retain both controls between lines.
`chirpGatherFromDimensionsModeCost_split` proves the exact avoided per-line charge:
`M*(6*tblC W e+11*W+24)+10*D+17*tblC W e+11*W+16`, where
`D=chirpCenter s t m M*w`. The shared sweep has no control-generation term.
`controlsSetup_exec` generates the count from computed source slot 7 and the
advance schedule from the gather bank, changing only those two raw-control tapes
and restoring both banks. It charges all conversion and schedule generation once.
The sweep, raw-gather, mode bridge, correlation, retained-interface and generated-
control checks peak at 1806.8, 1838.5, 1808.9, 1846.9, 1941.9 and 1940.5 MiB.
The generic shared group and existing closed caller build and pass their axiom audit.
The closed raw-input caller still selects the original mode: composing generated
controls into the shared `LineData` interface, selecting the retained loop and
clearing those controls once on final release remain next. This work has not yet
removed schedule regeneration from that complete caller's published cost.

**Closed caller now retains the generated schedule:** `LineData.transport`
separates the arithmetic/producer footprint from the raw-control interface, and
`LineData.shareControls` proves generated controls establish shared readiness
without regenerating arithmetic setup. `initializedGroup_exec` now executes
initialization, the shared symbol counter and `controlsSetup` exactly once, then
runs `preparedGroup` in retained mode. The count and advance schedule are inputs
computed by that program, with no new caller-supplied schedule or numeric gate.
`controlsRelease_exec` erases the retained controls in
`2*(M+(D+M))+5` steps, where `D=chirpCenter s t m M*w`;
`controlsReleaseR_collect` restores their original empty tapes while preserving
published output. `groupRelease_exec` composes this with symbol/arithmetic/bank
release. `symbolGroupResult` isolates the state after control release, so existing
setup-restoration reasoning is reused. `closedGroup_exec` now executes this entire
retained-control path, preserves its decoded error guarantee and exact original-
state restoration except output, and bounds execution by the revised scalar-only
`selectedGroupCost`. `selectedGroupCost_affine` uses the retained-mode unit cost;
schedule generation and final erasure occur only in its shared zero-line term.
Transport, shared-interface, control release, initialized-group, full release and
closed-group checks peak at 1943.7, 1943.6, 1948.5, 1958.9, 1937.1 and 1934.4 MiB.
The final fast-cost comparison remains open; retaining the schedule is now part
of the complete caller, rather than only a conditional component contract.

**Checked coefficient-volume cost comparison:** `ChirpFastCost` now proves
`2^l ≤ 14m` for the selected ceiling logarithm, the padded block-volume bounds,
and linear tape-work estimates for gathering, operand formation, output shifts/
products/rounding/cropping and short convolution. The latter reuses S1's existing
`chirpBatchProductCost_le`, rather than duplicating its packed-product argument.
`chirpForwardUnitCost_le` bounds one complete retained line, including batch-port
transfers, by
`chirpLineFixedBound W q l w m + M*rpRecBound (q+1) l w +
6*(s+t+m+1)*rmulCost w + 2000*(s+t+m+1)*(w+1)`.
Its fixed term is independent of source/output lengths except the address width;
all product/header setup and erasure are included. `selectedGroupUnitCost_le`
discharges all numerical gates from the selected dimensions.
`selectedGroupCost_le_fast` composes that bound with exact shared amortization,
and `closedGroup_exec` now returns both the original exact scalar budget and
`selectedGroupFastCost`, alongside actual execution, restoration and decoded error.
The complete coefficient-volume proof and caller checks peak at 1988.1 and
1934.9 MiB. This eliminates a window-size factor from all pointwise/tape work,
but is not yet the intended `O(M(p))` statement: the remaining bridge must match
`rmulCost` and `rpRecBound` to the multiplier envelope and account for fixed
startup. Existing `Cost.MatchConv.mt_cv_ring_le`, `Cost.Growth.gr_ringBound_le`
and `Cost.MatchBase.mt_rmul_le` provide the relevant supplier bounds.

**Uniform supplier and fixed-startup comparison:** `Cost.ChirpLogGrowth` bounds
packed logarithmic factors at precision p before applying the multiplier envelope,
so the O(p²) packed-size bound does not double the exponent loss.
`Cost.ChirpSupplier.chirp_selected_rpRec_le` bounds the complete recurring ring
charge, including formatting, by C*m*p^(129/128); `chirp_selected_work_le`
bounds all repeated line work by C*(s+t+m+1)*p^(129/128), plus fixed startup.
`chirp_selected_group_work_le` lifts this to the closed caller's fast budget,
retaining shared setup exactly once. `chirp_selected_fixed_le` bounds startup by
`32000*(W+1)^2 + (7056*mtCvKf 125+264000)*p^2`. This includes product headers,
loading and cleanup, and uses the existing generic ring-setup comparison.
The guarded supplier check peaks at 2851.6 MiB with default proof limits.
These comparisons do not yet close the required address-width/startup and shared
setup amortization into the intended resampling envelope.

**Address-width and complete line-startup absorption:** `Cost.ChirpAddressCost`
proves squared binary length is at most 262144 times its positive value, then
bounds the selected `(W+1)^2` by `5000000000*(p^2+t)` under `s<t`.
`chirp_selected_fast_le` therefore bounds the entire line budget by
`C*(p^2+t)*p^(129/128)`, with one uniform constant, including address arithmetic,
ring setup/headers and erasure. `chirp_selected_long_line_le` specializes this to
`C*t*p^(129/128)` for `p^2≤t`. `chirp_selected_group_le` applies directly to the
actual scalar `selectedGroupCost`, charging its zero-line shared setup once;
`chirp_selected_long_group_le` gives the corresponding long-line specialization.
The guarded address/line/group check peaks at 2838.5 MiB. The supplier axiom audit
now covers these six additional theorems, and its guarded build passes.
These theorems leave shared setup as an exact scalar charge; they do not prove
its required uniform bound/amortization or discharge the long-line regime in the
outer caller.

**Uniform shared setup and dimension-based amortization:** `Cost.ChirpSetupCost`
now proves the complete zero-line `selectedGroupCost` is at most
`6000000*(t+m+1)*(W+1)^3`, including scalar/bank setup, G/K/E and normalization
table generation, counters, shared advance controls and every release phase.
Its arbitrary-bank loading lemma is instantiated on the five actual consumer
banks; output counters are charged by their exact unary volume. Table setup is
bounded using total padded coefficient volume, not a per-window worst-case.
`chirp_selected_total_le` combines this explicit setup bound with
`C*N*(p^2+t)*p^(129/128)` for every admissible group size.
`chirp_selected_amortized_le` proves the full actual scalar budget is at most
`C*N*t*p^(129/128)` when `p^2≤t` and `(W+1)^3≤N`; these are dimension/count
conditions, with no supplied machine-cost inequality. The guarded setup check
peaks at 2875.8 MiB with unchanged proof limits.
This supplies a concrete candidate interface for S4's reuse regime. Completion
still needs to audit those size/count conditions against the intended S2 caller;
the conditional amortized theorem alone does not establish them for every caller.

**Cost comparison attached to actual execution:** `Cost.ChirpForwardBudget`
selects one universal constant from the proved total and amortized comparisons.
`chirpGroupAllowance` contains only scalar dimensions, explicit cubic setup and
the multiplier envelope; it contains no ring/multiplier cost primitive.
`closedGroup_exec` now returns this bound for the actual execution witness n,
and also returns `n≤C*N*t*p^(129/128)` under `p^2≤t` and `(W+1)^3≤N`, together
with the same decoded error and exact restoration guarantee. The original
scalar/fast budgets remain available. The guarded caller check peaks at
2821.3 MiB. The expanded machine and supplier axiom audits pass in a guarded
build (13924 jobs, combined peak 5.6 GiB).
The S2 caller itself permits arbitrary group length; S4/S6 have not yet supplied
an outer size/count theorem establishing these amortization gates. The cited
`notes/fast-gaussian-resampling.tex` is absent locally and two source fetches
failed, so no stronger claim about its intended size regime is made here.

**S2 completion audit:** The final cost gate is discharged by
`Cost.ChirpCallerSizing.chirp_runtime_size_gates` and `chirp_runtime_group_cost`.
For the actual executable `Mult.Sizes`, eventually every axis has `p^2≤t`, and
every complete complementary batch has `(W+1)^3≤N`. This covers every mixture
of source and target dimensions: one other live axis already supplies the lower
bound. It reuses `Sizes.eventually_pow_p_le_r 4`, the proved modulus bounds and
positive axis products, not an assumed machine-cost comparison or a new parameter
choice. The generic deterministic sizing lemma is available for future retunes.

| Acceptance gate | Authoritative evidence |
| --- | --- |
| Fixed executed forward map from raw scalar and line inputs | `LinePlacement.closedGroup`, `closedGroup_exec`; 640 tapes independent of all dimensions |
| Executable G/K/E/normalization tables, overlap and crop | Initialization and retained line execution in the closed caller's proof dependencies |
| Actual decoded forward-resampling error | `GroupOutputError` in `closedGroup_exec`: scaled error at most 4 for every published line |
| Exact borrowed-workspace/input restoration and ordered output | Final state in `closedGroup_exec` is the original state with only the output batch prepended |
| All setup, supplier, transfer and release costs paid | `chirpGroupAllowance` bounds the actual execution witness for all admissible sizes, including empty batches |
| Intended fast cost at executable full-axis batch sizes | `chirp_runtime_size_gates` discharges the closed caller's conditions; `chirp_runtime_group_cost` gives C*N*t*p^(129/128), with a uniform constant |
| Proof integrity and local resource limits | Both machine and supplier axiom audits pass; guarded build completes 13925 jobs, peak 3.4 GiB combined; sizing file peaks at 2832.9 MiB |

The stated caller ABI retains its supplied W-length width counter and line-count
counter, raw binary dimensions and norm-bounded input batch. It assumes no
coefficient tables, correlation outputs or arithmetic execution/cost oracle.
S2 is independently importable, as S1 is; root integration is not its acceptance
gate. Full tensor support/locality, fused core/halo scheduling, reserved chunks,
new parameter selection and matching the global multiplication machine remain
S4/S6 obligations. This completion does not change kappa.

Detailed contracts are indexed in the
[chirp design notes](IntegerMultBounds/MathlibTM2/NearOne/DESIGN.md).
S3–S6 remain open; kappa is unchanged until the full affected machine costs close.

## Long-term source and proof obligations

The new direction follows [PR 4359](https://github.com/CrocSwap/integer-mult-bounds/pull/4359),
pinned for this assessment to `da637c87c89482bc4c86be36bd0071b3d400dbed`:

- [Finite precompilation](https://github.com/zxv/integer-mult-bounds/blob/da637c87c89482bc4c86be36bd0071b3d400dbed/research/kappa-rebuild/architecture/FINITE-PRECOMPILATION.md): autonomous productive jobs, paid complementary axes, exact integer batch matching and an acyclic execution schedule.
- [Finite-template closure](https://github.com/zxv/integer-mult-bounds/blob/da637c87c89482bc4c86be36bd0071b3d400dbed/research/kappa-rebuild/transfer-audit/FINITE-TEMPLATE-CLOSURE.md): fresh linear semantic precision and actual simultaneous storage, including uncredited owned centers.
- [Outer transfer audit](https://github.com/zxv/integer-mult-bounds/blob/da637c87c89482bc4c86be36bd0071b3d400dbed/research/kappa-rebuild/transfer-audit/OUTER-TRANSFER-AUDIT.md): delayed BIT cover, changed atom width and reserves, global support-local scheduling and the nine outer charges.

These are conditional written arguments and replay evidence, not Lean proofs. Prove the
compiler structurally for arbitrary finite data and instantiate the local certificates last;
do not materialize the astronomical winning uniform word. Rank counts alone do not prove
native adapters, arbitrary-input semantics or ownership. Cover routing must preserve one
common external weight and pay fallback classes; reserves must include simultaneous stock.

The old outer ledger cannot be retuned to the new target: Gaussian resampling restricts
its dimension exponent to below one half, and its exposure saving collapses near one.
M11 needs the grouped/fused and support-local outer construction at dimension exponent
`0.99999`, including boundary matrix execution/error bounds and deferred reserved axes.
The upstream minimum outer saving is `0.00230197698`, leaving only `0.00000197698`
above the target; every charge must be justified by the implemented machine.

The older selected construction remains a conditional benchmark. Its
[selected record](https://github.com/CrocSwap/integer-mult-bounds/blob/0fdd7d82de03e43c9e5a1000dfbcd380d1b687d2/certificates/selected-result.json)
and [pinned source evidence](docs/sharper-bound-source.json) are retained for provenance,
not as a requirement to implement its entire route.

## Archived route and reusable work

The [archived native-machine roadmap](plan/archive/native-roadmap.md)
preserves the old manuscript-section tables and the separate `83/10^12`
compact-control target. Its yellow rows describe unfinished historical native
interfaces; they are not gaps in the completed Mathlib proof and are not the
active work queue. The archive is preserved for reference, not automatically
refreshed against the current library.

Reusable mathematics and surviving implementations remain indexed in
[COMPONENTS.md](COMPONENTS.md). The [retention audit](docs/proof-retention.md)
and retirement records document which code supports the completed theorem,
what remains unused and how to recover retired code. Archiving a roadmap
does not itself remove any Lean modules.

Run `python3 scripts/plan-status.py --check` to check the active proof summary;
`--list` lists its theorem milestones. Detail files under `plan/archive/`
are excluded from regeneration and the active milestone list.

S3 output-control checkpoint (2026-10-25): `complementHeader_exec` generates
the complementary width header by copying the retained width and releasing the
shift-sized prefix. Both source headers preserve their actual symbols, private
workspace is restored, and the exact cost is `4*w + 6*d + 10`. The guarded
single-file check passes at 1804.8 MiB. Full output-control composition, boundary
work and uniform line costs remain open; S3 is incomplete.

S3 generated output controls (2026-10-25): `outputHeaders_exec` composes
half-counting the retained even precision, two copies of the retained row
exponent and two guard bits with complementary-width generation. It produces
shift `d=b+2*l+2` and remainder `w-d`, preserves all borrowed header symbols
and restores private workspace, at exact cost `6*b+8*l+4*w+6*d+23`. The
guarded module check passes at 1817.7 MiB. This removes prepared shift-control
inputs from the next composition gate; complete cell execution, generated
coefficient pages, boundary/coupling/recovery and uniform line costs remain open.

S3 output-stage composition (2026-10-25): `outputFromHeaders_exec` generates
both shift controls from retained even precision, row exponent and word width,
runs the actual output rescaling/weight pass and releases both generated
controls. Its endpoint changes only the owned output prefix, with the existing
computed-word error bound and exact restoration of all other stacks. Its cost
bound is `closedOutputWeightsCost + 6*b+8*l+6*w+6*d+28`, where
`d=b+2*l+2`. No preloaded shift/remainder or multiplier-readiness oracle remains.
The guarded single-file check passes at 1928.2 MiB. The similarity table is still
prepared input; joining the input/interior endpoint, coefficient generation,
boundary/coupling/recovery and uniform line costs remain open.

S3 interior handoff cleanup (2026-10-25): `closedInputInterior_exec` now
composes generated normalization, actual source weighting, installation, four
triangular products, branch merge and scalar multiplication with paid release
of all three readiness counters. Its endpoint is the fixed raw-input bank with
only the output prefix replaced; no installed counters remain. The earlier
decoded scalar error guarantee is unchanged. Additional cleanup is exactly
`releaseWeightCountersCost q w`. The guarded check passes at 1907.6 MiB.
The duplicated normalized input remains explicit retained work on tape 111;
loading the final weight table, releasing that work, coefficient generation,
boundary/coupling/recovery and uniform line costs remain open.

S3 retained output-table loader (2026-10-25): `fetchOutputTable_exec`
generates the `M*L*w` table width and `(2*M*L+1)*w` skip from retained
`2*M`, `L` and `w` headers, copies the table from tape 110 to 96, restores
the complete source page and arbitrary suffix, and releases all generated
counts/private workspace. The table follows two generator banks and one
scalar. No prepared skip/count oracle is required. Its paid bound is
`40*M*L*w+15*M*L+17*M+12*w+49`. Guarded page-skip and loader checks pass
at 1799.7 and 1826.7 MiB. Connecting this loader to the canonical cell bank,
releasing retained normalized inputs, coefficient generation, boundary work
and uniform line costs remain open; S3 is incomplete.

S3 complete cell-arithmetic chain (2026-10-25): `cellArithmetic_exec` now
executes raw-source weighting, normalization/installation, all four S1
triangular products, branch merge, reciprocal multiplication, counter release,
retained output-table loading, final rescaling/weighting and cleanup in one
117-tape chain. The original generator/scalar/output-weight page and arbitrary
suffix survive exactly. Both normalized-input copies on 111 and the copied
output table on 96 are released; generated normalization/readiness/addressing/
shift controls are all paid for. The exact output is the actual
`weightedOutputNumerators` applied to the actual interior words, not an assumed
equality with scalar-rounding reference data. `preparedOutput_exec` retains
the existing decoded output error guarantee. Guarded prepared-output/cell
checks pass at 1921.0/1931.4 MiB. The source and input reciprocal table are
still staged inputs. Numerical-constructor specialization and matching to
`executedRun_valid`, setup generation, row-order publication, boundary/coupling/
recovery and uniform line cost/storage gates remain open. S3 is not complete.

S3 constructed-data execution/validity bridge (2026-10-25):
`constructedCell_exec` specializes the complete cell arithmetic chain to the
actual numerical generator/reciprocal constructors and ambient input/output
weights. All generator disks, scalar norm/reality, input/output weight ranges
and row lengths are derived. The exact terminal stream is
`executedOutputWords`, and every row satisfies the existing `executedRun_valid`
contract; no scalar-reference equality or stage-error oracle is assumed.
The shared page and arbitrary suffix are preserved, and temporary copies and
controls are released by the composed program. The guarded check passes at
1918.0 MiB. Numerical setup and source staging still enter as bank data; their
actual generation/movement, forward-order publication, boundary/coupling/
recovery and uniform line cost/storage matching remain open. S3 is incomplete.

S3 suffix-safe row publication (2026-10-25): `publishRows_exec` reuses the
structural coefficient-row reversal, generates the total old-prefix count from
batch/record dimensions, erases exactly that prefix, and publishes the new rows
above the untouched suffix. It restores every other stack and preserves word
bit order. For `M` rows of `L` words its bound is
`42*M*L*w+19*M*L+26*M+24`. The guarded check passes at 1841.4 MiB.
The reusable contract accepts retained `M`, `L`, `w` and `L*w` headers; the
closed cell caller must still derive `M` and `L*w` from its ordinary headers
and identify the output rows. Setup/source staging, boundary/coupling/recovery
and uniform line costs remain open; S3 is incomplete.

S3 publication header generation (2026-10-25):
`publishFromDimensions_exec` derives the row-batch count `M` from the retained
`2*M` header and derives `L*w` from retained row/width headers, invokes the
suffix-safe publication machine and clears both generated headers. Only the
owned output prefix changes. It needs no preloaded publication counters and
has bound `42*M*L*w+19*M*L+34*M+6*L*w+9*L+37`. The guarded check passes at
1831.4 MiB. Identifying the actual terminal word list as equal-length rows and
composing this wrapper with constructed cell execution remain open, together
with setup/source staging, boundary/coupling/recovery and uniform line costs.

S3 actual-word publication composition (2026-10-25): structural
`outputRows_spec` decomposes any `M*L`-word list, including zero-length rows,
without supplied row data. `publishWords_exec` instantiates the generated-header
publication machine. `publishedCell_exec` now composes constructed cell
arithmetic and publication on 117 tapes, emitting exactly
`publishedWords M L (executedOutputWords ...)`. All retained setup and the
output suffix survive, temporary copies/controls are released, and the cost
bound adds `publishFromDimensionsCost`. Original arithmetic `CellRun.Valid`
is retained. Guarded row-data and composed-publication checks pass at
1901.6/1919.0 MiB. The coordinate-read identity connecting published words to
the existing reversed-index numerical endpoint remains to be proved, alongside
setup/source staging, boundary/coupling/recovery and uniform line costs.

S3 published-coordinate numerical handoff (2026-10-25):
`publishedWords_read` proves that the forward position `n*L+i` decodes exactly
the old compact position `n*L+(L-1-i)`, preserving arbitrary tape suffixes and
requiring no word-fit or rounding assumption. `executedRun_y_published` now
identifies every valid cell output with its actual forward-order published
word. This closes the numerical coordinate-read obligation left by
`publishedCell_exec`; publication incurs no extra error. The structural proof
uses equal-length row reads and the existing flat-map lemma, with default
proof limits. The guarded check passes at 1911.3 MiB. Setup/source staging,
complex/full-line/boundary coupling and recovery, and uniform line cost/storage
matching remain open; S3 is incomplete.

S3 amplified-precision correction (2026-10-25): the earlier `q=2*b`
controller choice satisfies local stage gates but cannot also pay the final
rounded-cell error amplification by `2^b`. It is superseded for final sizing.
`executionPrecision` is now `4*b`, `executionWidth` is `8*b+8`, and
`executionStagePrecision` is `2*b`, where `b=executionExponent` still depends
on the requested final accuracy and original source bound.
`execution_error_bits` and `execution_stage_bound` prove compatibility;
`cell_error_budget` and `execution_cell_error` pay the full
`η+64*L*η*2^b+2*(η+2^cExp*η)` down to `2^-j`. The sized validity theorem
now uses the stronger stage precision. `quarterCount_exec` recovers b from
the 4*b header with exact source restoration, releases its intermediate header
and costs `22*b+10`. Guarded controller/sizing checks pass at 1801.2/1921.5 MiB.
The existing half-count arithmetic/publication execution theorems remain valid
for their stated inputs; migrating those wrappers to quarter-counting is the
next integration obligation. Setup/source staging, boundary/coupling/recovery,
complex/line assembly and uniform costs remain open. S3 is incomplete.

S3 quarter-count execution migration (2026-10-25): normalization and output
shift generation now recover b from q=4*b, using the restored temporary header
on 115. The complete input/interior/output/publication chain and its exact
restoration/cost proofs have migrated. Normalization costs `22*b+10`; combined
output controls cost `22*b+8*l+4*w+6*d+29`, and their execution/cleanup overhead
is `22*b+8*l+6*w+6*d+34`. These replace the earlier half-count costs.
`publishedCell_sized_exec` instantiates this chain from the requested final
accuracy and original RHS bound, with q=4*b, width=8*b+8 and stage exponent
2*b. All stage/word-width obligations are derived; the actual RHS bound is
weakened only to the declared source allowance. Its guarded check passes at
1915.3 MiB. The migrated expanded axiom audit passes (4422 jobs, combined peak
4.2 GiB). The proved rounded-cell budget is now compatible with executed
controls. Matching published reads to the exact interior solution under the
required ambient cell geometry, setup/source staging, boundary/coupling/
recovery and uniform line cost/storage matching remain open. S3 is incomplete.

S3 exact real interior comparison (2026-10-25):
`publishedCell_accuracy` now proves requested `2^-j` accuracy of the actual
forward-order published word against a solution of the original ambient
principal system. It combines sized actual `CellRun.Valid`, the published read
identity, `rounded_cell` and the full amplified-error budget. Stage bounds,
source magnitude and `L*η≤1` are derived. Principal-system, nonwrapping fit,
interior membership, common phase cell and maximality remain explicit geometry
conditions, with original ambient s preserved. No scalar-reference equality,
free stage-error or halo-size substitution is assumed. The guarded check passes
at 1909.3 MiB. Generating interval/ownership metadata and setup/source staging,
complex/line assembly, boundary/coupling/recovery and uniform cost/storage
matching remain open; S3 is incomplete.

S3 paid source/table staging (2026-10-25): `fetchPage_exec` generalizes
retained-page copying to any fixed bank offset with generated counts and exact
source/suffix restoration. The final table loader now specializes this shared
engine; its bound is `40*M*L*w+15*M*L+17*M+12*w+50`, one step above the
older unrolled loader. The superseded uncommitted two-copy page helper was
folded into structural `copyRepeated`/`pageAddress`. `stagePayload_exec`
copies the per-call RHS after three banks plus scalar, moves it to 93, then
copies the reciprocal table after four banks plus scalar to 96. All borrowed
payload symbols and private workspace restore. `stagePayloadBank_exec` proves
the resulting bank exactly matches `inputSourceBank` with nonempty source and
factors, starting from empty work buffers. Per-call RHS data are explicitly
borrowed payload, not shared setup-key data. Staging costs
`fetchPageCost 3+4*M*L*w+4+fetchPageCost 4`. Guarded address/fetch/staging/bank
checks pass at 1812.6/1828.8/1806.1/1913.2 MiB. Composing this staging call
with the sized cell caller, initial gathering/packing, generated setup/geometry,
boundary/line assembly and uniform cost/storage matching remain open.

S3 staged repeated-cell endpoint (2026-10-25): `stagedCell_sized_exec`
composes paid RHS/reciprocal staging with the sized constructed arithmetic and
forward-order publication. It starts with empty work buffers and returns
exactly the initial bank with only the output prefix replaced. The setup page,
borrowed per-call payload, headers, native stacks and output suffix are restored;
all copies and generated controls are released. `emptyInputBank_output_frame`
removes the computed normalized rows from the terminal-bank description.
The cost adds `stagePayloadCost` to the complete arithmetic/publication ledger,
and the actual `CellRun.Valid` endpoint is retained. The guarded staged/frame
checks pass at 1919.1/1913.1 MiB. Setup generation and initial payload gathering/
packing, generated interval metadata, complex/boundary/coupling/recovery and
uniform line cost/storage matching remain open. S3 is incomplete.

S3 computable ambient geometry predicates (2026-10-25):
`PhaseCellDiscreteGeometry.phaseIndex_eq` proves the signed integer quotient
`(2*(t-s)*j+s)/(2*s)` equals the existing nearest-rounding phase, including
ties and signed indices. `isInterior_spec` makes the original ambient interior
predicate decidable without real comparisons. `interiorIndices` enumerates
one phase in physical order without duplicate/out-of-axis indices;
`interiorSet` computes the full ambient interior mask and
`mem_interiorSet` proves exact agreement with the analytic definition. These
are computable metadata, not a tape scan or localized halo geometry. The
guarded check passes at 1736.6 MiB. Interval endpoint/length generation and its
geometry proof, executed descriptor/setup generation, payload gathering,
boundary/line assembly and uniform costs remain open. S3 is incomplete.

S3 computed full-cell interval geometry (2026-10-25):
`PhaseCellGeneratedInterval` computes minimum-coordinate starts and max-minus-
min lengths from the integer interior enumeration; empty phases have zero
length. `generatedInterval_spec` proves positivity, ambient nonwrapping fit,
common phase and exact coverage of all interior vertices of that phase.
`generatedInterval_solver_geometry` packages membership/maximality for the
computed ambient interior set. `generatedCell_accuracy` now derives the
requested published `2^-j` accuracy from one interior anchor, without supplied
interval, mask, fit, same-cell or maximality oracles. Guarded interval/accuracy
checks pass at 1759.0/1898.8 MiB. These are full ambient-cell constructors;
artificial halo cuts and paid descriptor/tape generation are not inferred.
Setup execution, phase grouping/payload gathering, complex/boundary/coupling/
recovery and uniform line cost/storage matching remain open. S3 is incomplete.

S3 computed full-interior ownership schedule (2026-10-25):
`activePhases` computes distinct nonempty phase keys from the integer interior
scan. `mem_activePhases`, `activePhase_interval` and
`generatedIntervals_cover_iff` prove that their generated intervals cover
exactly the computed ambient interior. `generatedIntervals_unique` proves
unique ownership between distinct keys; the list has no duplicate keys and
contains at most s entries. The guarded check passes at 1738.3 MiB. This
removes a supplied full-cell cover from the numerical metadata endpoint, while
retaining original ambient coordinates/cuts. Total interval-volume accounting,
length grouping, executed scans/setup/payload gathering, halo-cut treatment,
complex/boundary/coupling/recovery and uniform line costs remain open.

S3 generated interior-volume accounting (2026-10-25):
`intervalLength_eq_card` proves each computed span has exactly its coordinate
set cardinality, including empty phases. The phase fibers of the physical
interior give `sum_intervalLength`; casting physical coordinates into `ZMod s`
preserves cardinality. `activePhases_volume` proves the actual duplicate-free
key list has total interval length exactly `(interiorSet s t w).card`, and
`activePhases_volume_le` bounds it by s. Thus generated cell work has an exact
volume ledger rather than an interval-count-times-largest-cell surrogate. The
guarded check passes at 1751.1 MiB. Length grouping, executed scan/setup and
payload gathering, halo cuts, complex/boundary/coupling/recovery and uniform
line cost/storage matching remain open. S3 is incomplete.

S3 computed equal-length batching (2026-10-25):
`PhaseCellLengthGroups` computes distinct positive length keys and duplicate-
free phase lists for each length. Every emitted key has a nonempty batch.
`lengthGroups_list_volume` proves that the actual key-list sum of
`batchCount*rowLength` equals the ambient interior-mask cardinality; the total
is at most s. `groupOrigin` supplies natural-index origins for the existing
batch ABI, and `lengthGroup_solver_geometry` derives every row's full ambient
cell fit/membership/common-phase/maximality premises. The guarded check passes
at 1739.2 MiB. Length is only the batching field: all other setup-key parameters
still need equality for reuse, especially boundary metadata. Grouped machine
composition, executed descriptor/setup generation and gathering, halo-cut
treatment, complex/boundary/coupling/recovery and uniform line costs remain open.

S3 generated-group execution/accuracy bridge (2026-10-25):
`lengthGroup_sized_exec` now instantiates the complete staged 117-tape cell
program with batch count and origins from the computed equal-length schedule.
It derives positive row length from an emitted key; source rows, weights and
setup numerators use the actual generated origins, with the original empty-
work/restoration/output-prefix endpoint and complete staging/arithmetic/
publication cost. `lengthGroup_accuracy` proves requested `2^-target` error
for every published row against the ambient principal interior solution,
deriving all fit/membership/common-cell/maximality premises from the schedule.
The guarded check passes at 1911.5 MiB. The initial bank still contains
constructed numerical setup and packed per-call payload; executing their
generation/gathering and the outer group loop, halo cuts, complex/boundary/
coupling/recovery and uniform line cost/storage matching remain open.

S3 integer setup representation (2026-10-25): shared generator evaluation/
step/iteration definitions and embedding lemmas now work over rings, allowing
the integer setup to reuse the same structural engine.
`dyadicGeneratorIter_spec` proves that its n-th integer vector divided by
`2^(P*n)` equals the existing exact rational recurrence.
`PhaseCellIntegerGenerators` supplies actual corrected exponential coefficient
numerators and proves exact agreement with `PhaseCellGeneratorData.column`.
`integerColumnWords_eq` and `integerReversedColumnWords_eq` express both
executed generator banks using integer quotients only, with the identical
downward-rounding convention. Guarded recurrence/data/word checks pass at
1740.4/1736.2/1808.2 MiB. This removes rational reductions/floor operations
from the explicit column representation, but is not yet a tape setup theorem.
Reciprocal encoding, setup widths, executed generation and complete setup
cost/storage, outer scheduling/gathering, halo cuts and complex/boundary/line
composition remain open. S3 is incomplete.

S3 integer reciprocal and stored-setup widths (2026-10-25):
`columnNumerators_corner_pos` proves the integer reciprocal divisor is positive.
`integerReciprocalWord_eq` proves that dividing `2^(q+P*n)` by this corner
produces exactly the stored reciprocal used by the complete cell execution.
Thus both generator branches and the scalar now have explicit integer-only
representations matching the actual numerical constructors.
`columnNumerators_abs_le` bounds each stored entry by `2^(P*n+1)`, independent
of row count; `columnNumerator_fits` gives signed setup width `P*n+3`, and
`reciprocalNumerator_fits` gives numerator width `q+P*n+2`. Guarded data/word
checks pass at 1749.9/1819.9 MiB. These are stored-vector/division-input bounds,
not bounds for every matrix-product accumulator. Executed setup, intermediate
width/cost/space bounds, outer scheduling/gathering, halo cuts and complex/
boundary/coupling/recovery/line integration remain open. S3 is incomplete.

S3 integer setup accumulator widths (2026-10-25): coefficient numerators
are bounded by `2^P`. `rowTerms_abs_le` bounds every setup product, and
`rowPartial_abs_le`/`rowAccumulator_abs_le` bound any sublist accumulation,
including subtraction from the scaled unit RHS. With `L≤2^l`, row products,
partial sums and RHS accumulators fit widths `P*(n+1)+3`,
`P*(n+1)+l+3` and `P*(n+1)+l+4`. `integerSetupWidth=P*(n+1)+q+l+5`
provides one monotone allowance also covering stored vectors and reciprocal
inputs. `columnNumerators_one` proves the first iterate is a scaled unit seed,
so matrix steps may start at n≥1. Guarded arithmetic/fit checks pass at
1751.9/1815.9 MiB. This is a width contract, not an executed setup loop or
peak-space/cost theorem. Setup execution, outer scheduling/gathering, halo
cuts and complex/boundary/coupling/recovery/line integration remain open.

S3 executed integer setup seed (2026-10-25): `generateSeed_exec` emits
the scaled unit first iterate from ordinary row-length, word-width and
coefficient-precision headers. It generates/releases the symbol count, emits
zero symbols, replaces exactly bit P, restores the skipped prefix and all
workspace, and preserves the arbitrary existing output suffix and actual header
symbols. The dimension-independent program has bound
`10*L*W+9*L+6*P+17`. `seedWords_eq_column` identifies the emitted words with
the actual integer generator's first iterate. Guarded format/execution checks
pass at 1807.7/1838.1 MiB. This executes initialization only: coefficient-page
generation, matrix-row/iteration loops, reciprocal/column encoding and setup
release/peak-space/cost composition remain open, along with outer scheduling/
gathering, halo cuts and complex/boundary/line integration. S3 is incomplete.

S3 executed integer generator-row arithmetic (2026-10-25): the existing
scalar readiness program now admits precision zero when W≥5, preserving its
positive-precision API and all program bodies/costs. The shared real multiplier
stream exposes signed-word hypotheses directly; at truncation precision zero
it computes exact integer products. `integerProducts_exec` generates and pays
for the counters, restores both operands and scratch, and retains the counters.
`subtractRow_exec` structurally consumes an arbitrary product list through the
shared subtraction automaton, restoring its saved/count/temporary tapes.
`integerRow_exec` composes both on the 117-tape bank with bound
`prepareCost 0 W + L*(rmulCost W+13*W+12)+10`. `generatorRow_exec` identifies
the output with the next actual integer inverse-column entry, deriving operand
and result fits from the existing coefficient/column bounds. This is row
arithmetic with staged inputs, not a closed setup loop. Coefficient-page/RHS
staging, row/iteration control, reciprocal/column encoding and setup release/
peak-space/cost composition remain open, as do outer scheduling/gathering,
halo cuts and complex/boundary/coupling/recovery/full-line integration.
The expanded guarded S3 axiom-audit build passes 4446 jobs at 9.1 GiB combined
peak. Only the three approved axioms are allowed; proof limits are unchanged.
S3 remains incomplete.
The reusable `integerRowPrepared_exec` restores installed readiness and both
operands while changing only the accumulator word. Its bound is
`L*(rmulCost W+13*W+12)+10`; the generated-readiness wrapper derives its
contract from this kernel, so a future iteration loop may pay setup once.
`rowColumnWords_eq` identifies the reused row operand with the stored integer
column in its existing order. All twelve affected single-file checks pass;
the largest measured peak is 1933.8 MiB, below the per-module CI allowance.

S3 executed integer row staging and iteration (2026-10-25):
`stageIntegerRow_exec` generates/releases the L*W symbol count and copies the
borrowed column, factor row and RHS, preserving arbitrary suffixes. Its bound
is `26*L*W+9*L+10*W+36`. `finishIntegerRow_exec` releases owned operand copies
and publishes the accumulator in its original symbol order. The composed
`integerRowCall_exec` changes only the output prefix, with bound
`L*(rmulCost W+43*W+21)+14*W+55`. `consumeIntegerRow_exec` additionally consumes
owned factor/RHS prefixes at paid cost, retaining their exact suffixes.
`IntegerRowContext.update` proves shared readiness, column storage and workspace
survive loop control, source consumption and publication. `integerRows_exec`
uses the existing unary scanner to execute an arbitrary finite row list and
restores the actual count symbols. Its bound is `N*(integerRowCost L W+5)+4`,
where `integerRowCost L W=L*(rmulCost W+55*W+30)+20*W+73`.
`integerGeneratorStep_exec` specializes this loop to descending generator rows;
prefix publication then emits the next complete integer column in normal order,
with every output fit derived from the structural width bound.
`prepareIntegerStep_exec` also executes readiness generation once, adding
`prepareCost 0 W`, and retains that bank for reuse. The factor page is proved
independent of the iteration count; the RHS page is the scaled-unit seed in
reverse word order. These pages are still explicit inputs: their generation,
repeated-iteration control/column replacement, reciprocal/column encoding and
setup release/peak-space/uniform costs remain open, as do outer scheduling/
gathering, halo cuts and complex/boundary/coupling/recovery/full-line integration.
S3 is incomplete; kappa is unchanged.
Verification: the expanded S3 axiom-audit build passes 4454 jobs at 2.6 GiB
combined peak. All nine new/affected single-file checks pass below 2 GiB each
(the row-call check peaks at 1923.4 MiB). The scan of 146 changed Lean files
finds no new proof-integrity violations. PLAN and whitespace checks pass.
Setup width/exponent-header generation remains part of the open setup work.

S3 generated iteration RHS (2026-10-25): `generateReverseSeed_exec` emits the
single power word through the existing seed generator, then prepends the
executed (L-1)*W zero prefix; all counts/workspace restore. Its bound is
`10*L*W+15*L+6*d+37`. `generateRhsPage_exec` adds an executed empty-row branch,
covering arbitrary L with bound `10*L*W+15*L+6*d+39` and an arbitrary exact
output suffix. `generateIterationRhs_exec` generates exponent P*(n+1) from
ordinary P/n headers, emits the descending RHS page and releases that exponent.
Only the RHS prefix changes; the bound is
`10*L*W+15*L+12*P*n+21*P+49`.
`generateRhsIntegerStep_exec` composes this generation, executed readiness and
all integer generator rows on 117 tapes. Its bound is
`prepareCost 0 W + L*(integerRowCost L W+10*W+20)+21*W+53`.
The generated RHS is consumed before return, restoring the original RHS suffix;
no RHS page or RHS-exponent header is supplied. The owned factor page is still
an explicit input. Coefficient/factor-page generation, repeated-iteration
control/column replacement, setup-width generation, reciprocal/column encoding
and setup release/combined peak/uniform cost proofs remain open, along with outer
scheduling/gathering, halo cuts and complex/boundary/coupling/recovery/full-line
integration. S3 is incomplete; kappa is unchanged.
Verification: the expanded S3 axiom audit passes in the guarded build
(4457 jobs, 2.6 GiB combined peak). All five new/affected single-file checks
pass below 2 GiB each. The scan of 149 changed Lean files finds no new
proof-integrity violations; all changed/untracked text files pass whitespace
checks. The composed per-step cost uses P*(n+1)<W to absorb exponent generation
into 21*W, making the bound independent of the current iteration number.

S3 executed integer-column construction (2026-10-25): `replaceColumn_exec`
generates one L*W count, erases the owned old column prefix, installs the next
column and releases its temporary output, preserving both arbitrary suffixes.
Its bound is `18*L*W+9*L+18`. `copyFactorPage_exec` derives L² and L²*W from
retained row/width headers, copies a borrowed factor page and releases both
counts at bound `16*L²*W+15*L²+9*L+22`.
`preparedIntegerStep_exec` reuses installed readiness. `integerIteration_exec`
composes factor copying, generated RHS/exponent, all rows, column replacement
and an actual increment of the iteration header. It changes only the current
column and iteration count, returning the context needed by the next call.
Its uniform bound is
`I(L,W)=16*L²*W+15*L²+L*(integerRowCost L W+28*W+38)+21*W+94`.
`integerIterations_exec` runs M such iterations through the existing unary
scanner at bound `M*(I(L,W)+5)+4`, restoring the original count symbols,
retained factor page, readiness and every borrowed suffix/work tape.
`prepareIntegerIterations_exec` generates readiness once for the entire loop.
`generateIntegerColumn_exec` also initializes the actual unit seed and its
iteration header for a nonempty cell, requiring no input column, RHS page or readiness. It emits
the finite integer generator column at iteration M+1, retaining the factor page,
with bound `prepareCost 0 W+M*(I(L,W)+5)+10*L*W+9*L+6*P+22`.
`IntegerGeneratorContext.column_error` connects actual signed-decoded output,
divided by 2^(P*(M+1)), to the existing inverse-column error ≤2^-M;
`corner_pos` proves the actual decoded reciprocal divisor is positive.
The retained square factor page is still an explicit input and storage
obligation. Coefficient/factor generation, selecting/generating final sizing
headers, quotient/reciprocal encoding, setup release/combined peak/uniform cost
matching, outer gathering/scheduling, halo cuts and complex/boundary/coupling/
recovery/full-line composition remain open. S3 is incomplete; kappa is unchanged.
Verification: the expanded guarded S3 axiom-audit build passes 4467 jobs at
4.2 GiB combined peak. All fourteen new/affected single-file checks pass below
2 GiB each (largest measured peak 1931.7 MiB). The source scan of 159 changed
Lean files finds no new proof-integrity violations. All 161 changed/untracked
paths pass the text whitespace check; PLAN and git whitespace checks pass.


The executed column encoder now generates and releases its slice counters from
retained P/n/q/W headers, preserves the raw integer column and borrowed suffixes,
and emits the existing dyadic runtime column words. Signed decoding and the
existing inverse-column error bound hold for the emitted words. The encoder
cost is L*(20*W+6*(2*q+8)+23)+31*W+57. This is a separate verified entry point;
composition with raw column generation, reciprocal and reversed-branch encoding,
factor-page generation and the combined S3 cost/storage envelope remain open.

Final checkpoint: the guarded S3 audit build passes all 4473 jobs, including
the emitted-column decoding/error theorems, at 5.8 GiB combined process RSS.
The source integrity scan passes for all 165 changed Lean files.


The integer-column generator and runtime encoder are now composed in
`ScalarPlacement.generateEncodedColumn_exec`: one executed 117-tape program
starts from the retained factor page and ordinary headers, initializes and
iterates the integer column, generates/releases encoding counters, and emits
runtime column words on tape 111. It retains the signed raw column, factor page
and arbitrary borrowed suffixes. The combined bound is
`prepareCost 0 W + M*(integerIterationCost L W+5) + L*(30*W+6*(2*q+8)+32) +31*W+6*P+79`.
At M=j+1 the emitted words have inverse-column error at most 2^-j when j+2≤q.
Factor-page generation, reciprocal/reversed-branch encoding, final sizing
headers and combined setup storage/uniform costs remain open; S3 is incomplete.

Verification: the guarded S3 audit passes all 4474 jobs at 2.6 GiB combined
peak; the new module passes its single-file check at 1934.0 MiB. Axiom, source
integrity, plan-summary and whitespace checks pass.
