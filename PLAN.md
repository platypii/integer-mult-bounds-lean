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
| [Proved Mathlib end-to-end multiplier](plan/C-mathlib-end-to-end.md) | — | ✅ 1/1 | ✅ 1/1 | 1873 |

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
| S3 fast inverse map | 🟡 | `retainedComplexBoundary_spec` executes from one encoded complex input and the retained ordinary-parameter readiness bank: preserve/split the input, generate the residual and boundary table, construct/factor/solve/unscale the boundary system, generate ambient publication, recover both components, pair the complex output and restore every stack except its owned output prefix. Physical halo reads have error at most `2^-target`; no supplied boundary solutions, columns, factors or publication controls remain. Shared arithmetic precision and exact borrowed-suffix restoration are proved. `retainedInverse_spec` specializes the executed solver to the full complex matrix equation with uniform coordinate error. Packed-table retirement now has an explicit polynomial bound in ordinary geometry. The complete retained inverse execution now has a dimension-only time bound, including factor-bank release. Closed caller/setup, uniform fast time and simultaneous live-storage bounds remain open, including matching prepared boundary costs into the S3 budget. Shared S3–S5 interface remains pinned; kappa is unchanged. | Re-estimate after resource audit |
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


The second generator no longer needs a supplied reversed word bank:
`generateReversedColumn_exec` constructs `reversedColumnWords` on tape 113
from the encoded first column on tape 111. It saves/restores the head word,
reuses the structural coefficient-word reversal, and prepends zero. Both
borrowed suffixes and all other tapes are restored. Length/word counters are
generated from retained L/q headers and released; the exact cost is
`(L-1)*(16*(2*q+8)+21)+4*L+12*(2*q+8)+4*q+31` for L>0.
Signed decoding and error ≤2^-j are proved at iteration j+2, q≥j+2.
The guarded S3 audit passes 4478 jobs at 2.6 GiB combined peak.
Reciprocal encoding, factor-page generation, final sizing and combined
setup/cost/storage remain open, as do the outer full-line S3 obligations.
All four new modules pass individual guarded checks; the maximum measured
peak is 1892.6 MiB. Source integrity, summary and whitespace checks pass.


The inverse-generator setup is now composed end to end from the retained factor
page: `ScalarPlacement.generateGenerators_exec` initializes and iterates the
integer column, emits the first runtime generator on tape 111, constructs the
shifted reverse on tape 113, and computes the reciprocal on tape 96. It generates
`2^(q+P*n)` from ordinary headers, copies the positive signed corner into the
existing binary restoring divider, converts and crops the quotient to runtime
width, and releases numerator, binary workspace and counters. The raw column,
factor page and borrowed suffixes remain explicit and preserved.
`generatorBank_accuracy` proves stage error ≤2^-j for all three actually decoded
banks at n=j+2 and q≥j+2. Division alone costs at most `W*(12*W+93)+75`;
the complete reciprocal constructor costs at most
`W*(12*W+128)+6*(2*q+8)+4*q+134`. `generatorSetupCost` adds these executed
phases to column iteration and reversal without claiming a uniform S3 bound.
The guarded axiom audit passes all 4486 jobs at 2.6 GiB combined peak.
The retained dense square factor page is still supplied, and final sizing/header
generation, packed payload assembly/release and combined peak/uniform cost
matching remain open. Gathering/scheduling, halo cuts and complex/boundary/
coupling/recovery/full-line composition also remain open. S3 is incomplete;
this checkpoint does not change the proved multiplication saving.
All nine new/affected modules pass individual guarded checks; the maximum
peak is 1929.3 MiB. Source integrity, generated-summary and whitespace checks pass.


The generator setup now publishes its retained runtime page rather than three
separate temporary banks. `sizedGeneratorSetup_exec` generates
`W=integerSetupWidth P q (M+1) 0=P*(M+2)+q+5` from ordinary P/M/q headers,
derives all iteration/encoding/division width inequalities when q≤2*(M+1),
constructs both generators and the reciprocal, releases the raw integer column,
and packs `[column; shifted reverse; reciprocal]` above the original tape-110
payload. The page has exactly `(2*L+1)*(2*q+8)` symbols; physical offsets i,
L+i and 2L retain the proved signed-decoding errors ≤2^-j.
`packGeneratorsCost` pays raw-column release and assembly:
`12*L*W+18*L*(2*q+8)+18*L+8*(2*q+8)+4*q+44`.
`releaseGeneratorPage_exec` generates/releases its own page count, with bound
`26*L*(2*q+8)+14*(2*q+8)+9*L+4*q+30`.
`sizedGeneratorRelease_exec` releases the page, readiness counters, generated
iteration and width headers, restoring the complete original bank, factor page,
unary header symbols and arbitrary borrowed suffixes. Its bound is
`releaseGeneratorPageCost L q+2*(W+topN W+(M+1))+9+2*W+2`.
The guarded S3 axiom audit passes all 4493 jobs at 2.6 GiB combined peak.
This is single-cell generator-page assembly and teardown, not a complete input
ABI transition or an execution-wide peak-space theorem. The dense factor page is
still supplied. Coefficient/factor and weight-table generation, remaining runtime
headers, repeated/batched page assembly, full input/output ABI composition,
combined peak/uniform costs, gathering/scheduling, halo cuts and complex/boundary/
coupling/recovery/full-line composition remain open. S3 remains incomplete;
the proved multiplication saving is unchanged.
All seven new modules pass individual guarded checks; the maximum measured
peak is 1937.8 MiB. Source integrity, generated-summary and whitespace checks pass.


The factor page is now constructed internally by the numerical setup entry:
`ScalarPlacement.numericalGeneratorSetup_exec` composes `factorFactory_exec`
with the checked inverse-generator and packed-page constructors. Numerical
binary table headers P/s/t/u/band/L and ordinary unary iteration/precision/row
headers are input encodings; no pi table, exponential samples, distance vector,
matrix rows, factor page, inverse column or reciprocal is provided.
The proof first shows that unreduced Gaussian arguments `u*t*k²/s` give exactly
the existing corrected exponential samples. The table machine generates pi once,
branches around diagonal/out-of-band entries, evaluates the corrected routine
once per retained distance, and explicitly clamps the subtraction-by-two at zero.
A structural word proof constructs each Toeplitz row from a reversed prefix and
a forward prefix of that distance vector; a paid scanner emits descending rows,
restores the original unary count symbols and releases all per-row work.
The coefficient table's 63-register workspace and temporary distance vector are
released before the factor page feeds the existing generator program.
`factorFactoryCost` charges the table instructions (`tblC V W` per atom),
row/page assembly and cleanup. The distance stream uses at most
`L*(310*P+114)+160*P+450` atoms, with explicit non-overflow condition
`u*t*(L+1)^2*2^(13*P+8)<2^V`, W≤V. There is no execution oracle or setup cost
assumption. `numericalGeneratorRelease_exec` releases runtime/factor pages and
generated iteration/readiness state, restoring every original bank field outside
the consumed, owned binary table-header workspace. Factor-page release costs at
most `12*L²*W+15*L²+9*L+18`.
The guarded S3 axiom audit passes all 9724 dependency jobs at 2.6 GiB combined peak.
This does not establish S3 completion: numerical table headers and their two
word-width counters still need the outer loader/generation bridge; weight-table
generation, remaining runtime headers, repeated/batched pages, full input/output
ABI composition, execution-wide peak/uniform cost matching, gathering/scheduling,
halo cuts and complex/boundary/coupling/recovery/full-line composition remain open.
The dense page's L²*W storage remains an explicit cost/space obligation. The proved
multiplication saving is unchanged.
All thirteen new modules pass individual guarded checks; maximum measured
peak is 2118.0 MiB, below the per-module CI budget. Source integrity, generated
summary and whitespace checks pass.


The numerical table loader is now part of the executed setup:
`ScalarPlacement.headerGeneratorSetup_exec` starts with ordinary unary P/M/q/L
headers, owned unary s/t/u/band headers on 97--100, and clean native/table work.
It generates the setup width W, computes a logarithmic arithmetic workspace
`V=W+13*P+size(t)+size(u)+2*size(L)+size(band)+16`, initializes all 48 binary
table variables and both table counters, and loads the six actual header values.
`unarySize_exec` reuses the gamma writer's structural halving loop, retaining
original input symbols and appending `Nat.size n` ticks within `19*n+8` steps.
The generated V proves every header fits and
`u*t*(L+1)^2*2^(13*P+8)<2^V`; no initialized binary state, boundedness hypothesis,
width counter, sample, factor page, inverse column or reciprocal is supplied.
The same entry then runs the coefficient/factor factory and packed inverse setup.
`headerGeneratorRelease_exec` releases runtime/factor pages, table words,
readiness/iteration counters and the generated setup-width slot. All borrowed
stacks, original header symbols and arbitrary payload suffixes return; the
explicitly owned geometry inputs are consumed.
`headerGeneratorSetupCost` includes both width generators, table initialization,
all six retained-source binary loads, geometry cleanup and numerical setup.
The loader charges `(P+s+t+u+band+L)*(4*V+10)+36*V+61` steps, so unary geometry
reading is explicitly paid and still needs the outer amortized cost match.
The guarded S3 axiom audit passes 9731 dependency jobs at 2.6 GiB combined peak.
This closes the supplied table-state/width-counter gap. Weight-table generation,
remaining runtime-cell ABI/parameter composition, repeated/batched page assembly,
execution-wide peak and uniform cost matching, gathering/scheduling, halo cuts
and complex/boundary/coupling/recovery/full-line composition remain open.
S3 is incomplete and the proved multiplication saving is unchanged.
All six new modules pass individual guarded checks; maximum measured peak is
1952.8 MiB. Source integrity, generated-summary and whitespace checks pass.

Weight-table generation now has an exact natural arithmetic specification.
`PhaseCellRationalArgs.similarity_ratio` expresses the existing upward-tie
potential using `r=(2*t*j+s) mod (2*s)`: numerator `u*r*(2*s-r)` and positive
denominator `4*s*(t-s)`. Its numerator is at most `u*s^2`, independently of j.
`similarity_sample` proves that unreduced arguments produce the same corrected
exponential sample, retaining the subtraction-by-two correction.
`weightData_output_word` and `weightData_reciprocal_word` identify the actual
runtime words with natural divisions of that numerator, at the original ambient
coordinate `(lo+k).val`. They introduce no ideal-exponential substitution or
rounding oracle. These are arithmetic specifications; executing the argument
builder, weight stream, and ABI placement with paid setup/storage bounds remains
open. S3 is incomplete. These helpers await the larger weight integration before
commit.

The per-coordinate weight kernel now executes on the table machine.
`weightArgument_do` computes both unreduced arguments in eight atoms, retaining
geometry headers and the accumulator. `correctedExpCode_do` evaluates the raw
negative exponential and clamps its correction without emission, retaining the
sample numerator. The coefficient emitter now reuses this same correction proof.
`weightEmit_do` uses five atoms to produce both exact grid words from one sample;
`weightBody_do` composes these stages in at most `310*P+119` atoms and proves
preservation of pi, precision, sign and geometry/scale headers. Two guard bits
bound the scaled sample; no separate sample-fit assumption is required.
This is a per-coordinate execution theorem with explicit arithmetic-width
conditions. Whole-table iteration, generation of scale/geometry headers, the
117-tape host, runtime weight-page placement and paid cleanup remain open, along
with the other S3 obligations listed above. The weight integration remains
uncommitted pending a larger coherent checkpoint.
The composed kernel and coefficient refactor pass the guarded S3 axiom audit
(all 9737 jobs, 4.3 GiB combined peak). All six affected arithmetic/kernel
modules pass individual guarded checks; maximum peak is 1833.2 MiB. Source
integrity, generated-summary and whitespace checks pass. This verifies the
per-coordinate kernel, not completion of whole-table setup or S3.

The full weight stream now executes on the fixed 117-tape bank.
`weightStreamCode_do` loops over the original ambient coordinates `(lo+i) mod s`,
emits each exact output/reciprocal pair, and preserves the shared headers within
`L*(310*P+124)+3` table atoms. The loop works for empty lists and wrapped cells.
`coefficientTableHost_exec` factors the shared 63-register host/cleanup argument;
the existing distance-coefficient host now specializes this structural theorem.
`weightHost_exec` specializes it to the generated weight stream, prefixes the
interleaved page to tape 110, consumes the owned table workspace and preserves
all other bank fields and arbitrary borrowed suffixes. Its charged bound is
`(L*(310*P+124)+3)*tblC(V,w)+4*L*w+126*V+129`.
The entry currently requires prepared pi/geometry/scale table values and explicit
arithmetic-width conditions. Generating those values from the unary headers,
deriving their widths, separating the interleaved page into the final runtime
weight banks, and composing with generator setup and the cell ABI remain open.
S3 is incomplete. The preceding argument/kernel/stream/host work forms one
logical checkpoint; the earlier notes about waiting to commit refer to the
individual helper stages before this integration.
The integrated weight-stream checkpoint passes all 9740 guarded S3 audit jobs
at 5.9 GiB combined peak. All newly added and refactored modules pass individual
guarded checks; maximum measured peak is 2009.0 MiB, below the CI module budget.
The audit includes both old coefficient entry points and the new generic host,
weight-loop and weight-host execution theorems. Source integrity, generated
summary and whitespace checks pass. No claim of complete S3 setup is made.

The weight factory now starts from ordinary retained unary headers.
`weightGeometry_do` constructs the sign, doubled modulus, similarity denominator
and combined scale exponent in eight atoms. `weightScales_do` constructs the
three binary powers with one reusable loop counter; `weightInitCode_do` also
generates pi once and preserves the original numeric headers and accumulator.
`numericalWeightStream_do` composes initialization with the ambient-coordinate
loop, with `numericalWeightAtoms(P,q,L)=158*P+8*q+L*(310*P+124)+427`.
`weightWorkspaceWidth_facts` derives all arithmetic-width conditions uniformly
from P≥13, 0<s<t, u≥1, lo<s and L≤s, for the explicit width
`V=coefficientWorkspaceWidth(P,w+q+2,t,u,0,t)`.
No per-coordinate fit assumption, prepared pi, denominator or scale is supplied.
`loadWeightHeaders_exec` loads unary P/s/t/u/q/L/lo from tapes
114/97/98/99/112/102/111 into the initialized binary state and preserves each
original source symbol. Its cost is `(P+s+t+u+q+L+lo)*(4*V+10)+42*V+71`.
`weightHeaderState_fits` proves every loaded value fits the generated width.
`generateWeightWidth_exec` builds V on tape 115, with all scratch and source
headers retained, within `4*w+4*q+4*P+19*(3*t+u)+45` steps.
`weightSetup_exec` combines width generation, binary-bank initialization, all
seven header loads, pi/geometry/scale generation, numerical weight execution,
table cleanup and release of the generated width source. It leaves only the
interleaved pair stream prefixed to tape 110; the original unary headers,
borrowed suffix and every other bank field survive. The runtime word-width
header w on 94 is retained input metadata. The total charged setup bound is
`weightWidthCost+weightFactoryCost+2*V+2`, including all loading and cleanup.
The guarded S3 axiom audit passes all 9750 dependency jobs at 2.6 GiB combined
peak. This closes the supplied pi/scale/table-state/argument-fit gap for weight
setup, but the interleaved output still needs final runtime layout and composition
with the inverse-generator setup. Repeated/batched pages, the complete cell ABI,
execution-wide peak and uniform cost matching, gathering/scheduling, halo cuts,
and complex/boundary/coupling/recovery/full-line composition remain open.
The unary geometry/header reading costs are explicit and need outer amortization.
S3 is incomplete and the proved multiplication saving is unchanged.
All ten new setup modules pass individual guarded checks; maximum measured peak
is 1919.3 MiB, below the per-module CI budget. Source integrity, generated-summary
and whitespace checks pass. This is one integrated unary weight-setup checkpoint.

The single-cell numerical setup now includes ordered weights and inverse
generators in one executed 117-tape program, with complete paid teardown.
`splitPair_exec` and `splitPairs_exec` separate the generated interleaved stream
structurally, preserving each word's bit order, the original count symbols and
both temporary bank suffixes. `packPairBanks_exec` reverses only the reciprocal
input row, releases its temporary copy, and consumes the output row in descending
coordinate order. `pairLayout_exec` combines these passes within
`L*(46*w+45)+28` steps, restoring every scratch stack and temporary count.
`ambientWeightSample_eq_weightData` preserves the original ambient ZMod coordinate
including wraparound and ties. `weightPage_eq_execution_tables` identifies the
actual packed page, at P=2^15*p, with the existing single-cell executed output
weight table and reciprocal input row; no alternate weight model is substituted.
`packedWeightSetup_exec` composes the unary setup and ordering passes.
`runtimeWeightSetup_exec` additionally generates w=2*q+8, restores its width
source and consumes the owned lower-endpoint header on 111, leaving all borrowed
headers and suffixes unchanged.
`ScalarPlacement.weightedGeneratorSetup_exec` composes this with the unary inverse
setup. All geometry and precision inputs are ordinary unary headers; no word
widths, table state, pi, factors, weight samples or inverse columns are supplied.
The retained page is exactly `[first generator; shifted reverse; reciprocal;
descending output weights; ascending reciprocal input weights; borrowed suffix]`.
`weightedGeneratorBank_page` proves that layout. The per-call RHS is not in this
setup page; gathering/insertion and the full runtime cell ABI remain to be proved.
`releaseWeightPage_exec` generates its counts from L/q, erases exactly the
2*L*(2*q+8) weight symbols, and releases its work within
`24*L*(2*q+8)+26*L+2*(2*q+8)+4*q+25` steps.
`weightedGeneratorRelease_exec` releases both setup families and all generated
widths/counters/pages. Only the owned geometry and lower endpoint are consumed;
all original borrowed state is restored exactly.
The setup bound is the sum of the executed weight and inverse setup bounds; the
release bound adds the executed generator/factor and weight release bounds.
This is a single-cell numerical setup integration. Repeated/batched pages,
per-call RHS placement and remaining runtime parameters, the complete cell ABI,
execution-wide peak and uniform cost matching, gathering/scheduling, halo cuts,
and complex/boundary/coupling/recovery/full-line composition remain open.
The dense L^2*W factor page and unary geometry-reading costs still require the
outer cost/storage match. S3 remains incomplete and the multiplication saving
is unchanged.
The combined numerical-setup checkpoint passes all 9761 guarded S3 axiom-audit
jobs at 2.6 GiB combined peak. All eleven new modules pass individual guarded
checks; maximum measured peak is 1939.6 MiB, below the per-module CI budget.
Source integrity, generated-summary and whitespace checks pass. The runtime
ABI and outer uniform cost/storage obligations above remain unproved.

A single cell now executes from raw gathered RHS words and unary controls through
numerical setup, the runtime ABI transition, arithmetic and valid publication.
`swapAfterPrefix_exec` swaps equal-sized borrowed blocks while retaining their
prefix, suffix, symbol order and every work stack. `swapCellPayload_exec` derives
both offsets from L/w and swaps the RHS with the reciprocal input weights within
`L*(46*w+9)+12*w+35` steps. The same swap restores the construction order.
`releaseConstruction_exec` releases the dense factor page and all construction
readiness/iteration/width counters while preserving the complete runtime page.
Its bound is `releaseFactorPageCost(L,W)+2*(2*W+topN(W)+n)+11`; the original
factor-page suffix survives, so it can hold the ordinary l header.
`installCellHeaders_exec` consumes the old iteration counter and owned P/q/l
sources, generates the runtime width and single-cell batch count, and installs
the exact arithmetic q/l headers within `2*M+2*P+10*q+6*l+22` steps.
`prepareCellRuntime_exec` composes construction storage release, header installation
and RHS placement. `cellRuntimeBank_eq_inputSourceBank` proves that the result is
the existing canonical single-cell input bank, including every empty work buffer,
native stack and input/output spectator field. `prepareCanonicalCellRuntime_exec`
executes that transition; no canonical-bank equality or execution is supplied.
`constructionCell_sized_exec` then runs the existing staged arithmetic and
publication and proves `CellRun.Valid` at the sized execution precision.
`unaryCellBank` contains only ordinary unary controls, raw RHS words, the borrowed
payload and original output tail. `unaryCellBank_base_eq` and
`unaryCellBank_setup_exec` identify the numerical setup's generated bank with the
construction bank consumed by runtime execution. `generatedCell_sized_exec`
composes that executed setup and runtime path into one fixed 117-tape program.
It generates its own widths, pi, factors, inverse columns, reciprocal and weight
words, arranges the RHS, executes the arithmetic and publishes a valid result.
The initial RHS is the gathered ambient-coordinate row; no normalized input,
weight table, inverse column, initialized binary table or setup execution oracle
is an input. Each cost is charged: `weightedGeneratorSetupCost` plus construction
release, runtime header installation, payload routing, staging, arithmetic and
publication. The factor page is released before arithmetic, preserving its suffix.
This closes the single-cell construction-to-runtime ABI/publication gap.
Post-publication runtime cleanup still needs to release the retained numerical
page and runtime headers and restore the original borrowed RHS layout. Batched
and shared-setup execution, efficient generation of control parameters,
execution-wide peak and uniform cost matching, gathering/scheduling, halo cuts,
and complex/boundary/coupling/recovery/full-line composition remain open.
The dense setup peak and unary geometry-reading costs remain explicit obligations.
S3 remains incomplete and the proved multiplication saving is unchanged.
The raw-input single-cell checkpoint passes all 9770 guarded S3 axiom-audit jobs
at 2.6 GiB combined peak. All nine new modules pass individual guarded checks;
maximum peak in the final pass is 1949.6 MiB, below the per-module CI budget.
The audit includes unary setup identification, the canonical ABI identity and
the complete sized raw-input execution/CellRun.Valid theorem. Source integrity,
generated-summary and whitespace checks pass. Runtime cleanup and the outer
S3 obligations above remain unproved.

The sized real single-cell path is now fully closed after publication.
`releaseRuntimePages_exec` first swaps the RHS back behind the reciprocal weights,
borrows a generated copy of the runtime precision for teardown, erases the
retained generator and weight pages using generated counts, and restores the
original RHS/payload sequence exactly. It retains the precision source and
preserves every other stack except the consumed runtime word-width source.
`releaseCellRuntime_exec` then clears all remaining owned runtime headers.
Its final `releasedCellBank` contains only the published output on 93 and the
original RHS followed by its borrowed suffix on 110; every native left stack and
every other right stack is empty, and input/output spectator fields are exact.
The page-release bound is `swapCellPayloadCost(L,2*q+8)+releaseGeneratorPageCost(L,q)
+releaseWeightPageCost(L,q)+6*q+2*(2*q+8)+8`; remaining header release adds
`2*(q+l+2*L+2)+11`. `cellRuntimeBank_R` supplies a small structural register-layout
lemma, avoiding repeated expansion of the entire numerical construction in
cleanup proofs. No proof limits were raised.
`closedCell_sized_exec` composes generated setup, the runtime ABI transition,
arithmetic, valid publication and full cleanup from raw RHS words and ordinary
unary controls. `sizedClosedCellCost` names the complete executed time ledger,
including setup/loading, factor storage release, routing, arithmetic, publication,
retained-page release and all header cleanup.
`closedCell_spec` strengthens the machine endpoint to requested accuracy for its
actual output tape, compared with a solution of the original ambient principal
system. It proves exact RHS/payload restoration, empty work/native stacks,
preserved spectator fields and the shared `PhaseCellInterface.ErrorOn` bound
on `publishedCellCore lo L`. `publishedCell_offset` and
`publishedCellRead_errorOn` identify the published word index with the original
nonwrapping ambient coordinate and introduce no core-size or window-count factor.
Geometry, interior/maximality, the original matrix and locality duties remain
explicit; no claim about a different halo system is substituted.
This closes single-cell post-publication cleanup and its real core-accuracy
endpoint. Batched/shared-setup execution, efficient control generation,
execution-wide peak and uniform cost matching, gathering/scheduling, artificial
halo cuts, and complex/boundary/coupling/recovery/full-line composition remain
open. In particular the dense construction peak and unary geometry-reading
costs still need the outer amortized bounds. S3 remains incomplete and the
proved multiplication saving is unchanged.
The closed-cell endpoint passes all 9777 guarded S3 axiom-audit jobs at 2.6 GiB
combined peak, including the shared core-error interface. All six new modules
pass individual guarded checks; maximum final peak is 1940.9 MiB, below the
per-module CI budget. Source integrity, generated-summary and whitespace checks
pass. The batched/full-line and uniform cost/storage obligations remain open.


Shared inverse construction is now executed once for an entire equal-length
batch. `repeatPrefix_exec` structurally repeats a counted word while restoring
its source, both count headers, archives and borrowed suffixes. The generator
bank replication and packing programs retain one scalar and put all first
columns before all reversed columns, exactly matching the existing grouped
runtime row bank. No numerical inverse is recomputed in the replica loop.
`loadBatchHeader_exec` consumes an owned unary batch packet beneath the factor
page on 109 and preserves its arbitrary control suffix. Delaying this read
keeps the construction scratch ports available. `batchInverseSetup_exec`
composes unary numerical construction, release of dense factors and construction
workspace, packet loading and grouped page preparation. The original payload
beneath the page and all borrowed bank suffixes are preserved.
`batchInverseSetupCost_affine` proves the exact cost identity: setup at batch
size zero plus `B * (38 * (L * (2*q+8)) + 43)`. Dense numerical construction is
outside the batch loop and its storage is released before copying.
This closes shared inverse setup, not the batch runtime. Batched weights,
payload gathering/layout, runtime headers, grouped execution and cleanup,
efficient control generation, execution-wide storage and uniform cost matching,
halo cuts and complex/boundary/coupling/recovery/full-line composition remain
open. S3 remains incomplete and the proved multiplication saving is unchanged.
The shared inverse checkpoint passes all 9787 guarded S3 axiom-audit jobs at
2.7 GiB combined peak. All eight new modules pass final individual guarded
checks; maximum peak is 1949.0 MiB, below the per-module CI budget. Source
integrity, generated-summary and whitespace checks pass.


Batched numerical weights now have an executed raw-header construction.
`weightBatchStep_exec` reads one owned ambient-origin packet, generates its
ordered output and reciprocal input rows, consumes the origin header and
prepends the two rows to separate accumulators. `weightBatchLoop_exec` uses a
structural unary scan over arbitrary origins, preserving the original batch
count symbols and all geometry. `packWeightBatch_exec` reverses whole rows in
both accumulators and releases their copied prefixes. Cell order becomes
forward without reversing coefficients or bits inside a row; output coordinates
remain reversed within each cell, as required by the existing arithmetic.
`batchWeightSetup_exec` composes count generation, the full numerical loop,
packing and count release. Its endpoint changes only the consumed packet prefix
on 109 and the new numerical page on 110; all borrowed accumulator and payload
suffixes, geometry headers, native stacks and spectator fields are preserved.
`reversedRowTable_eq_flatMap` and `batchWeightPage_eq_execution_tables` identify
the generated page exactly with `executedOutputTable` and the flattened
reciprocal `cellWeightRows`. No supplied numerical data or setup execution
oracle is assumed.
The row packer costs at most `B*(50*(L*w)+47)+30`.
`weightBatchStepCost_origin` charges the origin-dependent unary work explicitly;
`batchWeightSetupCost_le` gives the schedule-independent bound
`L*(6*w+9)+40+B*(weightBatchStepCost(P,s,t,u,q,L,s,w)+50*(L*w)+52)`.
This bound pays for numerical initialization and unary geometry loading at
every cell. It is an executed construction bound, not the required final
amortized fast-line estimate. Shared inverse/weight setup composition, payload
layout and gathering, runtime headers, grouped execution/cleanup, efficient
control generation, uniform total time/storage, halo cuts and
complex/boundary/coupling/recovery/full-line composition remain open.
S3 remains incomplete and the proved multiplication saving is unchanged.
The batched-weight checkpoint passes all 9792 guarded S3 axiom-audit jobs
at 2.6 GiB combined peak. All five new modules pass final individual guarded
checks, with maximum peak 1957.2 MiB, below the per-module CI budget. Source
integrity, generated-summary and whitespace checks pass. Shared inverse/weight
composition and the full grouped runtime and uniform-cost obligations remain
open.


The generated setup and arithmetic now compose for a whole real batch.
`generateRuntimeWidth_exec` generates the word width from the retained precision;
`saveBatchInverseHeader_exec` saves the batch count as an owned parser packet,
then consumes the temporary count and width. `batchWeightedSetup_exec` combines
this with the origin-dependent weight loop, one inverse construction, release
of dense factors/workspace and exact grouped column replication. Its simple
`batchWeightedBank` retains both numerical pages above the untouched raw RHS.
`swapBatchPayload_exec` generates the batch row/symbol offsets and swaps the
reciprocal-weight bank with the raw RHS behind the inverse/output-weight prefix.
All word orders, suffixes and work counters restore; its charged bound is
`B*(L*(46*w+15)+9)+12*w+41`. `installBatchHeaders_exec` retains the generated word
width, doubles the batch count for the two arithmetic branches and consumes the
old iteration/precision/control headers. It costs `2*N+2*P+6*q+6*l+6*B+23`.
`generatedBatchSetup_exec` composes numerical construction, routing and header
installation with the complete setup cost ledger.
`unaryBatchBank_setup_exec` starts with only ordinary unary controls, an owned
origin-packet stream and raw RHS words. `generatedBatchBank_eq_inputSourceBank`
identifies its executed endpoint with the existing grouped arithmetic ABI,
including empty work banks and exact spectator fields. Separate output/input
weight-row identities retain the original ambient phase coordinates while
inserting the RHS between the generated weight banks.
`generatedBatch_sized_exec` now executes one fixed 117-tape program from that
raw input through setup, payload staging, grouped arithmetic and publication.
Every published cell carries the existing `CellRun.Valid` certificate, with
costs charged for all setup, routing, staging, arithmetic and publication steps.
Inverse construction occurs once for the batch; weight initialization/loading
is still explicitly paid at every cell. The initial RHS is already gathered
in ambient-coordinate row order. Neither numerical data nor a setup execution
oracle is supplied.
This closes the generated-setup-to-grouped-publication gap. Batch teardown must
still restore the original borrowed RHS layout and release retained numerical
pages and headers. The requested ambient-core output interface for this batch
endpoint, efficient control generation, execution-wide peak storage and uniform
cost matching, gathering/scheduling, artificial halo cuts and
complex/boundary/coupling/recovery/full-line composition remain open. Dense
construction and unary geometry/origin-reading costs still need outer
amortization. S3 remains incomplete and the proved multiplication saving is
unchanged.
The raw-input batch checkpoint passes all 9801 guarded S3 axiom-audit jobs at
2.7 GiB combined peak. All nine new modules pass final individual guarded
checks, with maximum peak 1968.8 MiB, below the per-module CI budget. Source
integrity, generated-summary and whitespace checks pass. The batch teardown
and outer S3 obligations above remain open.


Post-publication batch cleanup and the requested ambient-core output endpoint
are now closed. `releaseBatchRuntime_exec` consumes the owned cell-length header,
uses the retained doubled batch count and the second length header to generate
the total batch length, then reuses `releaseRuntimePages_exec` on the flattened
page. It restores the original raw RHS/payload order, erases both numerical
pages and consumes every remaining runtime header. The final bank contains only
the published result on 93 and the exact original RHS followed by its borrowed
suffix on 110. All native left stacks and all other right stacks are empty;
input/output spectators are exact. No additional page parser is needed.
The release ledger is `2*L+2 + (4*(B*L)+17*B+10) +
releaseRuntimePagesCost(B*L,q) + 2*(q+l+B*L+L+2*B)+11`.
`closedBatch_sized_exec` composes generated setup, grouped arithmetic, publication
and this complete release, retaining every cell's `CellRun.Valid` certificate.
`sizedClosedBatchCost` charges the full path.
`closedBatch_spec` compares actual final-tape words with solutions of the
original ambient principal real system, under the explicit full-cell geometry
hypotheses. It supplies requested pointwise accuracy and the shared
`PhaseCellInterface.ErrorOn` bound for every published core.
`publishedBatchRead_errorOn` crops the preceding rows and transfers the existing
ambient-coordinate read lemma with no batch-size or window-count factor.
`closedLengthGroup_spec` specializes this executed, cleaned and accurate endpoint
to the computed `lengthGroup` and `groupOrigin`, deriving all fit, interior,
full-cell and maximality hypotheses from `lengthGroup_solver_geometry`.
`generatedBatchSetupCost_le` and `sizedClosedBatchCost_le_bound` remove dependence
on the particular origin sequence. The computed group endpoint uses
`sizedClosedBatchBound`, a complete dimension-only ledger. Its setup part is
one zero-replica inverse setup plus
`L*(6*w+9)+14*w+10*q+2*N+2*P+6*l+119 +
B*(weightBatchStepCost(P,s,t,u,q,L,s,w)+134*L*w+15*L+116)`, for `w=2*q+8`.
This still explicitly pays for numerical weight initialization and unary
geometry/origin loading at every cell; it does not prove the required amortized
fast-line estimate. Generating efficient controls and weight setup, execution-wide
peak storage and uniform cost matching, gathering/scheduling, artificial halo
cuts and complex/boundary/coupling/recovery/full-line composition remain open.
The raw RHS and computed schedule's unary packets are still inputs to the local
endpoint. S3 remains incomplete and the proved multiplication saving is unchanged.
The closed-batch/group checkpoint passes all 9808 guarded S3 axiom-audit jobs
at 2.6 GiB combined peak. All seven new modules pass final individual guarded
checks, with maximum peak 1952.9 MiB, below the per-module CI budget. Source
integrity, generated-summary and whitespace checks pass. The efficient setup,
full-line geometry/execution and uniform fast-cost/storage obligations remain
open.


Batch weight construction now shares its initialization, not only its inverse.
`sharedWeightInit_exec` generates the workspace width and binary table bank,
loads the ordinary geometry/precision headers once, and computes pi, similarity
geometry and powers of two once. `retainedWeightRows_exec` emits each cell's
weights while retaining these initialized headers and the empty accumulator.
`TblIns.run_bounded`, `TblBig.bounded` and `TblDo.bounded` preserve bounded table
values across successive host calls. `countedLoop_exec` supplies a structural
relational loop invariant, allowing table scratch values to vary between rows
without choosing a concrete register history.
`loadWeightOrigin_exec` consumes exactly one workspace-width binary origin word
and replaces only the table origin. It costs `8*V+8`, independent of the
origin's value; no absolute-coordinate unary header is constructed or read.
`retainedWeightPage_exec`, `retainedWeightStep_exec` and
`retainedWeightLoop_exec` generate and separate all origin-dependent rows while
retaining the same initialized table and preserving the original payload.
`sharedBatchWeightSetup_exec` composes this with one initialization, counted
loop, table release and the existing whole-row batch packer. Its final page is
exactly `batchWeightPage`; borrowed suffixes and all workspace are restored.
For `V=weightWorkspaceWidth(P,q,w,t,u)` its cost is
`sharedWeightInitCost + L*(6*w+9)+128*V+172 +
B*(retainedWeightStepCost(V,w,P,L)+50*L*w+54)`.
The closed batch path now uses this program. `batchInputBank` carries unary
dimensions, fixed-width binary origins and the raw gathered RHS. The closed
execution, cleanup, ambient-core error and computed length-group endpoint all
remain checked. Numerical pages are still generated by one fixed 117-tape
program. Setup and complete-execution cost functions no longer take the origin
sequence. `generatedBatchSetupCost_eq` expands setup as one fixed cost plus
`B*(retainedWeightStepCost(V,w,P,L)+134*L*w+15*L+118)`; the fixed part includes
one weight initialization and one zero-replica inverse setup. The computed-group
ledger uses this origin-independent bound without an origin-size hypothesis.
The superseded per-cell initialization/unary-origin batch constructors were
removed; restore from `a12d23a3` (row definitions now live in `PhaseCellWeightPage`).
This removes repeated pi/scale construction and repeated unary geometry/origin
loading from the batch loop. It does not yet establish the required amortized
fast-line estimate: numerical weight evaluation, dense inverse setup, outer
binary control generation, execution-wide peak storage, gathering/scheduling,
artificial halo cuts and complex/boundary/coupling/recovery/full-line composition
remain open. S3 remains incomplete and the proved multiplication saving is
unchanged.
The shared-initialization checkpoint passes all 9815 guarded S3 axiom-audit
jobs at 6.0 GiB combined peak, including the closed computed-group accuracy
endpoint. All 20 new or revised non-audit modules pass final individual guarded
checks; maximum peak is 1974.6 MiB, below the per-module CI budget. Source
integrity, generated-summary and whitespace checks pass. Binary control
construction, the uniform fast-cost/storage estimates and full-line composition
remain open.


The origin-control schedule now has executable natural arithmetic, without
coordinate-set searches or supplied endpoints. `phaseLower` is the clipped
ceiling quotient `(2*s*phase+2*(t-s)-1-s)/(2*(t-s))`.
`interior_phase_iff_range` and `coordinateSet_eq_Ico` prove that the original
ambient interior of a phase is exactly the half-open interval from
`phaseLower(phase)+band` to `min(s,phaseLower(phase+1))-band`.
`intervalStart_eq_naturalStart` and `intervalLength_eq_naturalLength` identify
these division formulas with the existing full-cell endpoints, including empty
phases and clipped end cells. The nearest-rounding tie convention is unchanged.
`naturalLengthGroup` filters the bounded phase range `0 .. t-s` by the computed
positive interval length. Its origins satisfy the original full-cell solver
geometry. `naturalGroups_cover` covers every original interior vertex, and
`naturalIntervals_volume` proves that summed natural cell lengths equal the
original interior cardinality, hence at most `s`; no artificial halo partition
or duplicate volume is introduced.
`naturalIntervalCode_do` computes one exact interval in 21 table atoms.
`tblNatSub_do` handles underflow by a comparison and truncated subtraction,
rather than allowing machine subtraction to wrap. `tblNatMin_do` supplies the
clipped endpoint. `naturalGroupCode_do` scans each possible phase once and emits
exactly the selected group's origins in physical phase order.
`naturalOriginPackets_eq_rows` identifies those emitted origins with the closed
batch solver's row ABI. `naturalOriginPairs_real_bits` converts the emitted
pair symbols to the exact fixed-width binary words consumed by the weight loop.
`originController_exec` now generates its doubled gap, one and phase-count
constants and executes the origin emitter from four binary numeric headers:
`s`, `t`, band width and target length. For the existing generated workspace
width `V`, `weightWorkspaceWidth_control` proves all interval arithmetic fits.
The charged controller time is
`(27*(t-s+1)+9)*tblC(V,V)+2*(naturalLengthGroup.length*V)+2`.
It prefixes the binary packets on 109, preserves the borrowed suffix, native
left stacks and input/output spectators, and retains a bounded table bank for
the outer controller to consume/release. No origin list or prepared interval
is an input to this controller stage.
`closedNaturalGroup_spec` supplies the existing fully cleaned execution and
requested ambient-core accuracy for this natural schedule, with the same
origin order and original principal interior system. Loading the four binary
headers from the outer ordinary parameter bank, installing the generated batch
count, releasing the controller bank and composing the controller directly with
the closed solver remain open. RHS gathering, the uniform fast-cost/storage
estimates, artificial halo cuts and complex/boundary/coupling/recovery/full-line
composition also remain open. S3 remains incomplete and the proved
multiplication saving is unchanged.
The natural-origin controller checkpoint passes all 9827 guarded S3 axiom-audit
jobs at 2.6 GiB combined peak. All twelve new modules pass final individual
guarded checks, with maximum peak 1942.5 MiB, below the per-module CI budget.
Source integrity, generated-summary and whitespace checks pass. The outer
controller/solver composition and uniform fast-cost/storage obligations remain
open.


### S3 ordinary-parameter controller and closed solver bridge

The origin controller now constructs its binary table from four retained unary
headers (`s`, `t`, band width and target length). `countWords_exec` structurally
counts the emitted fixed-width words without receiving their number, restores
the complete packet source and its scratch stacks, and charges exactly
`B*(6*V+6)+4` steps. `naturalGroupCountedHost_exec` counts before attaching the
borrowed suffix, so arbitrary suffix contents do not affect the count. It emits
exactly the natural origin packets and installs the generated unary count on 116.
The counted controller costs at most
`(27*(t-s+1)+9)*tblC(V,V)+B*(8*V+6)+6`.

`generateOriginControls_exec` constructs both temporary widths from ordinary
parameters, initializes and loads the origin table, executes the counted
controller, releases all 31 table ports and clears both width sources. Its exact
output differs from the original bank only on 109 (origin packet prefix) and
116 (generated count); native stacks, input/output spectators, raw RHS and
borrowed suffixes are preserved. `naturalGroupInputBank_exec` identifies this
output with the existing closed solver's complete input bank. The ordinary
input has no supplied origins, batch count, binary controller state or workspace
width headers.

`generatedNaturalGroup_spec` composes that controller directly with the closed
real solver. From ordinary unary parameters and already gathered RHS it executes
all control generation, numerical setup, batch solving, publication and cleanup,
with pointwise requested accuracy and `ErrorOn` on each original ambient core.
The ledger explicitly adds `generateOriginControlsCost` to the existing sized
closed-batch bound; no uniform fast-time or execution-wide storage estimate is
claimed. RHS gathering, efficient global grouping, artificial halo cuts,
complex/boundary/coupling/recovery/full-line composition and uniform cost/storage
bounds remain open. S3 remains incomplete and the proved saving is unchanged.

The ordinary-parameter bridge passes all 9834 guarded S3 audit jobs at 2.6 GiB
combined peak. All nine new or revised non-audit modules pass individual guarded
checks; their maximum measured peak is 1953.8 MiB. Source integrity, generated
summary and whitespace checks pass.


### S3 linear ambient-line RHS gathering kernel

`gatherOffset_exec` extends the existing restoring window sweep with an initial
forward seek. It restores the entire source, delimited control stream and all
scratch, prefixes only the destination, and charges exactly
`B*(14*rowSymbols+25)+12*(firstSeek+laterSeeks.sum)+23`.
Its structural proof has no supplied execution hypothesis or finite certificate.
`windowAdvances_fits`, `gatherRows_windowAdvances` and
`windowAdvances_volume` prove that forward differences of ordered absolute
origins fit the original source, copy exactly those windows and move through
at most one source length in total.

`naturalOrigins_ordered` and `naturalOrigins_fit` instantiate this sweep at the
natural equal-length group in physical phase order. `ambientStream_window`
proves each actual encoded ambient-line slice is the exact original-coordinate
`cellSourceRows` RHS row. `naturalGatherRows_eq_rhs` identifies the whole output
with the closed solver's Gaussian-integer RHS ABI, preserving coefficient word
and bit order. `naturalGather_exec` generates the row-symbol counter from
retained row and word dimensions, executes that sweep, clears the generated
counter, and restores every stack except the prefixed destination.

`naturalGroup_volume_le` proves `B*L ≤ s` for each selected length class from the
existing total interior-volume theorem. Together with the single-sweep movement
bound, `naturalGatherCost_le` bounds this gather, including generated-counter
setup and release, by `66*s*w+29` when `w ≥ 1`. It does not traverse the whole
source separately for each selected cell.

The delimited forward-advance control stream is still an explicit input to this
kernel. Its generation from ordinary parameters and the ambient-source gather /
closed-solver bank composition remain open. This checkpoint therefore does not
close outer RHS gathering or the uniform cost for all groups. Execution-wide
storage, artificial halo cuts, complex/boundary/coupling/recovery/full-line
composition and the final S3 uniform bound remain open. S3 is incomplete and the
proved multiplication saving is unchanged.

The linear natural-group gathering checkpoint passes all 9847 guarded S3 audit
jobs at 2.6 GiB combined peak. All seven new modules pass individual guarded
checks; maximum measured peak is 1947.4 MiB. Source-integrity, generated-summary
and whitespace checks pass, with default proof limits unchanged.


### S3 generated advance controls and raw ambient-line solver

`originAdvanceNext_exec` decodes the next binary origin packet, computes its
forward difference from the retained previous origin, multiplies by the word
width and emits its delimited unary advance. The structural
`originAdvanceLoop_exec` consumes exactly the generated batch count, archives
all consumed binary packets and emits every advance at runtime.
`originAdvanceControls_exec` appends the terminal zero advance, restores the
complete binary origin stream and unary count, releases conversion scratch and
prefixes only the control destination outside its bounded table. Its bound is
`B*(3*tblC(V,V)+29*V+30)+8*advances.sum+11`.
`originAdvances_natControls` proves these are exactly the earlier natural
sweep's controls. `naturalOriginAdvances_volume` bounds the total emitted ticks
by `s*w`, including the initial seek; conversion does not emit an absolute unary
origin for every cell.

`preparedNaturalAdvanceControls_exec` constructs its small table from ordinary
unary width sources, loads the word width, executes conversion and releases the
whole table. The existing generated workspace width proves all coordinate and
symbol advances fit. `generateOriginAndGatherControls_exec` shares one generated
pair of width sources between the origin and advance controllers, then clears
them. Its exact bank output differs only on 109 (origin packet prefix), 116
(generated count) and 91 (generated sweep controls). No prepared binary table,
origin list, batch count or unary advance stream is supplied.

`rawNaturalGather_exec` copies the ambient prefix to private scratch, performs
one restoring sweep, and releases the private copy, generated row-symbol count,
controls and temporary word width. The original ambient prefix and arbitrary
borrowed suffix survive below the gathered RHS on 110. Its charged cost is at
most `97*s*w+2*w+4*q+59`, where `w=2*q+8`.
`rawNaturalGroupInputBank_exec` composes the ordinary controller and raw gather
into the closed solver's exact input bank.

`rawNaturalGroup_spec` now executes the whole real nonempty equal-length group
from ordinary unary parameters and one ambient line: control generation, RHS
gathering, numerical setup, solving, publication and cleanup. It proves the
requested pointwise accuracy and `ErrorOn` on each original ambient core. The
final RHS payload retains the complete original line and borrowed suffix;
input/output spectators are unchanged and all other workspace is cleared.
The cost explicitly includes both generated controllers, raw gathering and the
existing sized closed-batch solver bound.

This closes the supplied-advance and pre-gathered-RHS gaps for one real natural
group. Global enumeration and execution of all length classes, the uniform fast
solver/time and execution-wide storage bounds, artificial halo cuts and
complex/boundary/coupling/recovery/full-line composition remain open. S3 remains
incomplete and the proved multiplication saving is unchanged.

The generated-control/raw-line checkpoint passes all 9859 guarded S3 audit jobs
at 2.7 GiB combined peak. All eleven new modules pass individual guarded checks;
maximum measured peak is 1963.5 MiB. Source-integrity, generated-summary and
whitespace checks pass with default proof limits unchanged.


### S3 bounded global length schedule and executed candidate discovery

`naturalLength_middle` proves every non-endpoint phase has one of the adjacent
lengths `s/(t-s)-2*band` and `(s/(t-s)+1)-2*band`. Together with the two clipped
endpoint lengths, `naturalLength_mem_candidates` gives a fixed four-candidate
list containing every actual cell length. `naturalLength_le_uniform` and
`naturalLengthCandidates_uniform` bound all candidates by
`(s/(t-s)+1)-2*band`; the FFT need not be sized to the whole ambient line.

`naturalLengthKeys` removes duplicate candidates and empty groups as a
computable mathematical schedule. It is a sublist of the four candidates, has
at most four entries, and contains exactly the nonempty length classes.
`naturalLengthKeys_list_volume` proves the exact ledger
`sum_keys B(L)*L = interiorSet.card ≤ s`. `naturalLengthKeys_pad` transfers one
common FFT-padding choice to every selected length.
`naturalLengthKeys_core_cover` and `naturalKeyCores_eq_interior` identify the
union of their actual published ambient cores with precisely the original
interior mask. `naturalLengthKeys_errorOn` transfers the same uniform coordinate
error to the whole interior without a key-count factor.

`naturalEndpointLengthsCode_do` computes both clipped endpoints with the same
verified interval code used by the real solver. `naturalMiddleLengthsCode_do`
computes the two interior candidates, including truncated empty lengths. The
combined candidate program uses 54 table atoms; generating its gap/one constants
adds six. `lengthCandidatesController_exec` emits exactly the four fixed-width
binary candidate words in candidate order, costing at most
`60*tblC(V,V)+8*V+2` after its initialized binary header bank.

`generateLengthCandidates_exec` supplies that entire bank from ordinary unary
parameters, generates both workspace widths, loads only `s`, `t` and band width,
runs discovery and releases all controller/width scratch. Its exact final bank
differs only on 87, where the four binary words prefix an arbitrary borrowed
suffix. No row length, batch count, phase constants, prepared interval or binary
numeric table is supplied.

The executed discovery stream deliberately contains all four candidates,
including possible zeros, duplicates and candidates whose group is empty. The
mathematical nonempty/deduplicated schedule is proved, but its runtime filtering,
iteration of the raw group solver and ambient publication are not yet composed.
Global execution, uniform fast solver/time and execution-wide storage bounds,
artificial halo cuts and complex/boundary/coupling/recovery/full-line composition
remain open. S3 remains incomplete and the proved saving is unchanged.

The bounded length-discovery checkpoint passes all 9868 guarded S3 audit jobs
at 4.1 GiB combined peak. All nine new modules pass individual guarded checks;
maximum measured peak is 1842.8 MiB. Source-integrity, generated-summary and
whitespace checks pass with default proof limits unchanged.


### S3 executed positive-key selection, count and per-key setup

`distinctLengthsCode_do` structurally proves a table program that emits positive
last occurrences from an arbitrary register list. Its bound is `n*(n+1)+1`
table atoms, so four candidates need at most 21. `loadBinaryHeaders_exec`
consumes numeric packet words into the table in order, preserving an arbitrary
packet suffix and every register outside the source/table bank.
`selectPositiveLengths_exec` initializes that table, loads four candidates,
removes zeros and duplicates, counts the selected words before attaching the
borrowed suffix, emits the selected binary queue and releases the entire table.
Its bound is `21*tblC(V,V)+230*V+263`, including conversion scratch restoration.

`generatePositiveLengthKeys_exec` shares generated width sources with candidate
discovery and constructs the positive distinct key queue on 87 and its unary
count on 86 from ordinary parameters. It restores every other register and
preserves an arbitrary suffix below the key queue. No candidate list, key count,
row length or binary table is supplied. The count is at most four, and the owned
binary queue has exactly `keyCount*V` symbols; iteration need not inspect the
borrowed suffix to decide when it ends.

`installLengthKey_exec` consumes one selected binary word and constructs both
ordinary row-length headers, 102 and 103, charging at most `10*L+19*V+18`.
It preserves the remaining key queue and all other metadata and releases every
parsing/conversion scratch register. `probeLengthKey_exec` then executes the
existing generated-origin controller and tests its actual unary batch count.
Its branch flag is exactly `0 < naturalLengthGroup.length`; the additional test
costs one step. `originControlsR_empty` proves that an empty class leaves the
original bank unchanged, enabling the outer loop to skip its numerical solve.

`naturalPositiveLengthKeys` is exactly the generated positive distinct schedule.
It may still contain a positive candidate whose group is empty; filtering by the
computed nonempty-group test gives the previously proved actual key schedule.
Empty candidates contribute zero row volume, so the positive schedule still has
exact total interior volume. It retains common FFT padding and the same
whole-interior `ErrorOn` through `naturalPositiveLengthKeys_errorOn`, without a
key-count factor. For positive band width all selected lengths fit the ambient
line, supplying the origin-controller probe's ordinary length precondition.

Generation, installation and probing are individually executed and verified;
the complete loop with the raw group solver, protected outer metadata and
ambient publication is not yet composed. Uniform fast solver/time and
execution-wide storage bounds, artificial halo cuts and complex/boundary/
coupling/recovery/full-line composition remain open. S3 remains incomplete and
the proved multiplication saving is unchanged.

The counted positive-key/per-key-setup checkpoint passes all 9875 guarded S3
audit jobs at 6.9 GiB combined peak. All eight new or revised non-audit modules
pass individual guarded checks; maximum measured peak is 1863.9 MiB. Source
integrity, generated-summary and whitespace checks pass with default proof
limits unchanged.


### S3 protected group caller and ambient-source retirement

`protectedRawGroup_spec` executes the real generated natural-group preparation
and closed numerical solver inside a 144-register caller. Ten header copies
install the private 117-register bank from retained master parameters, costing
`4*(P+N+q+l+s+t+u+band+2*L)+41`. The caller saves the actual generated row count
before numerical cleanup, preserves all other outer metadata and restores the
private workspace except for the output and retained RHS/source stacks.

The closed batch and its four group wrappers now expose an exact output-prefix
contract: the published prefix has `B*L*w` symbols and retains the caller's
original output suffix. The protected caller carries this contract together
with the existing coordinate accuracy and ambient-core `ErrorOn` guarantees.
`takeOuterLengthKey_exec` consumes one binary selected key directly in the
protected bank and restores all decoding scratch, charging `6*L+19*V+14`.
The original private-bank key installer now reuses this structural decoder.

`retireGroupRHS_exec` computes the gathered RHS length from the retained row
count, row length and word width, discards precisely that prefix, and restores
the original ambient source and all scratch. Its bound is
`12*B*L*w+6*L*w+9*L+9*B+19`; `retireNaturalGroupCost_le` bounds this by
`36*s*w+19` for a nonempty natural group. Both are executed tape programs;
there is no supplied solver callback or uncharged source reset.

Ambient output scattering, empty-class branching and the complete class loop
remain to be composed. Uniform fast solver/time and execution-wide storage
bounds, artificial halo cuts and complex/boundary/coupling/recovery/full-line
composition remain open. S3 is incomplete and the proved saving is unchanged.

The protected-caller/source-retirement checkpoint passes all 9884 guarded S3
axiom-audit jobs at 4.0 GiB combined peak. All 14 new or revised non-audit
modules pass individual guarded checks; maximum measured peak is 1975.7 MiB.
Default proof limits are unchanged. Source integrity, generated-summary and
whitespace checks pass.


### S3 linear ambient output scattering and accuracy handoff

`scatterPacket_exec`, `scatterLoop_exec` and `scatterBatch_exec` execute one
fixed structural publication program over arbitrary registers and lists.
A delimited control packet gives the gap before each disjoint window. The
program preserves that gap in a reversed accumulator, discards the old window,
consumes the corresponding solved row and appends it to the accumulator. One
final reversal restores the ambient output prefix; another restores all
controls. Every scratch register is restored and all native and left stacks
are unchanged. Only the consumed solver-output stream and ambient output
change. No per-row seek back to the beginning is charged or assumed.

The exact cost is `rowCount*(12*windowLength+23)+12*gapSum+6`, equivalently
`12*visitedVolume+23*rowCount+6`. `naturalOrigins_disjoint` proves that natural
cells of a fixed length have disjoint original-coordinate windows.
`windowGaps` converts their absolute origins into relative gaps;
`naturalScatterGaps_fits` and `naturalScatterGaps_volume` prove that their
visited volume fits one encoded ambient line. `naturalScatterCost_le` gives
`35*s*w+6` for publication of a natural group, including final reversals.
`naturalScatter_exec` consumes precisely the owned `B*L*w` solver-output prefix,
restores its borrowed source suffix and preserves the borrowed ambient-output
suffix.

`scatterRows_absolute` identifies every published row at its original absolute
origin. `scatterRows_absolute_off` preserves every symbol outside the selected
windows. `naturalScatterRows_word` proves exact word alignment, and
`naturalScatterRows_errorOn` transfers the packed solver's coordinate accuracy
to the physically scattered ambient line with the same error, without a batch
or class factor. The structural sweep also covers an empty control list.

This endpoint still takes the delimited publication controls as input. Their
executed generation from the computed origin packets, connection to the
protected group solver, empty-class branching and the complete class loop
remain open. Uniform fast solver/time and execution-wide storage bounds,
artificial halo cuts and complex/boundary/coupling/recovery/full-line composition
also remain open. S3 is incomplete and the proved saving is unchanged.

The linear-publication checkpoint passes all 9893 guarded S3 axiom-audit jobs
at 2.6 GiB combined peak. All nine new modules pass individual guarded checks;
maximum measured peak is 1841.4 MiB. Default proof limits are unchanged.
Source integrity, generated-summary and whitespace checks pass.


### S3 generated publication controls and protected setup/release

`publicationControls_exec` converts the existing unary gather advances into
publication gaps. It retains the first origin, subtracts the encoded window
length from each later advance, and emits the new delimited stream. Its fixed
loop is driven by the actual generated row count, preserving that count and the
original control stream, including their borrowed suffixes. All transient
registers are restored. The bound is
`12*(firstAdvance+remainingAdvances.sum)+21*rowCount+21`.

`naturalPublicationGaps` identifies the converted stream with the natural
publication schedule at the original ambient origins. The disjoint-window
geometry supplies every subtraction precondition. `naturalPublicationControls_exec`
proves execution and the bound `33*s*w+21`, including restoration of original
controls and count. The independent `publicationControls_restore` frame lemma
keeps the structural proof within default proof limits.

`protectedPublicationControls_exec` specializes this program to the outer
144-register bank. It computes the encoded window length from retained row and
word widths, emits controls on protected register 140 and releases its
counter. Its bound is `48*s*w+27`; every other register is restored, so the
existing gather and numerical solve can use their original private operands.
`protectedScatter_exec` supplies the matching outer-bank publication program:
it constructs its own window counter, consumes exactly the owned solved prefix,
preserves the source/output borrowed suffixes, publishes into ambient output
132, and releases both the counter and owned controls. Its bound is
`54*s*w+15`, with all other scratch restored.

These setup and publication programs are verified separately. Inserting the
control-generation stage between the existing origin/gather controller and RHS
gathering, then composing the numerical call, RHS retirement and publication,
remains open. Empty-class branching and the complete class loop also remain
open, as do uniform fast solver/time and execution-wide storage bounds,
artificial halo cuts and complex/boundary/coupling/recovery/full-line
composition. S3 is incomplete and the proved saving is unchanged.

The generated-control/protected-publication checkpoint passes all 9901 guarded
S3 axiom-audit jobs at 4.2 GiB combined peak. All eight new non-audit modules
pass individual guarded checks; maximum measured peak is 1927.7 MiB. Default
proof limits are unchanged. Source integrity, generated-summary and whitespace
checks pass.


### S3 complete nonempty protected class operation

`generateNaturalGroupInputBank_exec` and
`gatherControlledNaturalGroupInputBank_exec` expose the existing generated-control
handoff in raw preparation. The original `rawNaturalGroupInputBank_exec` now
composes these two halves with its original interface. This permits publication
setup to run before RHS gathering while reusing the same computed origins and
gather controls.

`protectedGroupInput_exec` executes that composition in the actual 144-register
caller, inserting the existing publication-control generator at the handoff.
The resulting private bank is exactly the closed solver input; the publication
controls remain on protected register 140. `protectedRawGroup_spec` now carries
those controls through the actual numerical solve, together with the generated
row count on 129, packed output framing and the existing accuracy guarantees.
The protected call charges the inserted setup bound `48*s*w+27` and preserves
all other outer metadata, including pending keys and their count.

`finishNaturalClass_exec` composes RHS retirement, ambient publication and
release of the current row length, row count and owned publication controls.
It charges at most `94*s*w+39`, restores the original ambient source and both
borrowed output/source suffixes, and returns every other scratch register.
`protectedNaturalClass_spec` executes the entire nonempty class operation:
header installation, generated preparation, actual solve, retirement,
publication and release. Its bound is the updated `protectedRawGroupCost` plus
`94*s*w+39`. It gives an exact final-register frame: only ambient output 132 is
published and owned per-class headers/controls 128, 129 and 140 are cleared;
all other right stacks, all left stacks and native input/output are restored.
The output on the physical ambient tape satisfies the same original-coordinate
core `ErrorOn` bound, without a class or row factor.

This endpoint requires a nonempty class and the retained word-width header.
Empty-class branching, the generated-key loop and its initialization remain
to be composed. Uniform fast solver/time and execution-wide storage bounds,
artificial halo cuts and complex/boundary/coupling/recovery/full-line
composition remain open. S3 is incomplete and the proved saving is unchanged.

The complete nonempty-class checkpoint passes all 9905 guarded S3 axiom-audit
jobs at 4.3 GiB combined peak. All six new or revised non-audit modules pass
individual guarded checks; maximum measured peak is 1982.2 MiB. Default proof
limits are unchanged. Source integrity, generated-summary and whitespace checks
pass.


### S3 shared origin probe and executed empty-class preparation

`prepareOriginControls_exec` factors the existing runtime width generation and
origin/count scan into a stage that retains both width headers. The original
`generateOriginControls_exec` now composes this stage with width release and
keeps its original API and bound. `completeGatherControls_exec` continues from
those retained origins, count and widths, constructing gather controls and
releasing the width headers. The original nonempty
`generateOriginAndGatherControls_exec` reuses these stages with its original
API and bound. The origin scan is performed once in either composition.

`probePreparedOrigins_exec` reads the actual generated row count while retaining
the origins and widths. `probeAndGatherControls_exec` uses that flag in a fixed
runtime conditional: a nonempty class completes gather controls from the same
origin packets; an empty class releases the widths and restores the original
bank. It returns the exact nonempty-class flag. Its bound is the original
origin-control cost, plus the nonempty-only advance-control cost, plus three
control steps. `probeNaturalGroupInputBank_exec` supplies the corresponding
ordinary-parameter bank interface.

`releaseUnaryHeaders_exec` structurally restores a bank after a distinct list
of private unary header copies. `releaseEmptyGroup_exec` instantiates it for
the outer caller and clears the current length on 128, charging
`2*(P+N+q+l+s+t+u+band+3*L)+23`. It preserves ambient source/output and all
pending key metadata. `conditionalGroupPreparation_exec` now executes header
installation, the embedded runtime probe/control preparation and the empty
cleanup branch in the actual 144-register caller. An empty class returns every
right stack to its original value except the released current length; a
nonempty class retains the exact controlled private bank and all outer
metadata. Native input/output and all left stacks are preserved, and the
returned flag is the computed class-emptiness decision.

This is the conditional preparation/empty-exit endpoint. Connecting its
nonempty controlled-bank continuation to publication setup, the actual
numerical solve and publication, then closing the generated-key loop and its
initialization, remains open. The existing complete nonempty-class theorem
still verifies independently. Uniform fast solver/time and execution-wide
storage bounds, artificial halo cuts and complex/boundary/coupling/recovery/
full-line composition also remain open. S3 is incomplete and the proved saving
is unchanged.

The conditional-preparation/empty-exit checkpoint passes all 9913 guarded S3
axiom-audit jobs at 10.7 GiB combined peak, including the existing complete
nonempty-class pipeline after the shared-stage refactor. All eleven new or
revised non-audit modules pass individual guarded checks; maximum measured peak
is 1963.1 MiB. Default proof limits are unchanged. Source integrity,
generated-summary and whitespace checks pass.


### S3 complete runtime-selected class and decoded-key operation

`protectedControlledGroupInput_exec` continues directly from the controlled bank
returned by runtime preparation: it generates protected publication controls and
gathers the RHS while retaining the existing origins and gather controls.
`protectedBatchSolve_spec` factors the actual numerical solve and saved generated
row count into one shared execution theorem. The original raw-group preparation
and solve wrappers now reuse these continuations with their existing APIs and
bounds. No origin scan or numerical argument is duplicated in the conditional
path.

`protectedControlledClass_spec` composes that prepared-bank continuation with
RHS retirement, ambient publication and release. `conditionalNaturalClass_spec`
now runs the complete runtime-selected operation: the computed row-count flag
selects this actual numerical continuation or the empty exit. Both branches
satisfy one exact register contract, including restored native/left stacks,
ambient source, output/source suffixes and pending scheduler metadata, with
per-class headers and publication controls cleared. The physical output has the
same original-coordinate core `ErrorOn` bound; the empty branch has no rows and
leaves ambient output unchanged.

`conditionalNaturalClassCost` charges conditional preparation, the nonempty-only
`protectedControlledClassCost` (or the empty branch's one-step action), and the
branch step. The controlled continuation bound includes `48*s*w+27` publication
setup, raw RHS gathering, `4*B+4` count preservation, the sized closed-batch bound
and `94*s*w+39` retirement/publication/release.

`processLengthKey_spec` joins the binary-key decoder to this complete conditional
class program. It consumes exactly one selected word of width `V`, constructs
and releases the current unary length, preserves the remaining key suffix and
count metadata, and charges `6*L+19*V+14` plus `conditionalNaturalClassCost`.
This is the actual operation the generated-key loop can repeat; it no longer
requires the caller to supply class nonemptiness or regenerate origin controls.

The counted generated-key loop and its initialization remain to be composed,
including preservation of earlier classes' published accuracy. Uniform fast
solver/time and execution-wide storage bounds, artificial halo cuts and
complex/boundary/coupling/recovery/full-line composition also remain open.
S3 is incomplete and the proved saving is unchanged.

The runtime-selected class/decoded-key checkpoint passes all 9919 guarded S3
axiom-audit jobs at 2.7 GiB combined peak. All nine new or revised non-audit
modules pass individual guarded checks; maximum measured peak is 1992.2 MiB.
Default proof limits are unchanged. Source integrity, generated-summary and
whitespace checks pass.


### S3 counted key loop and final whole-interior accuracy

`naturalClass_intervals_separated` proves that different length classes occupy
separated original-coordinate natural intervals. `naturalScatterRows_preserves_class`
uses that separation to preserve the exact encoded word reads on every other
class when one class is published. Thus an earlier accuracy bound survives
later publication with no extra arithmetic or key-count error.

`lengthKeyStep_spec` executes the actual counted iteration body: discard one
owned count symbol, decode/process one key, then inspect the remaining count.
It restores the private bank and exposes the unchanged remaining class reads.
`LengthKeyReady.of_frame` carries the retained-header/source/scratch invariant
between iterations. The only changed right stacks are the owned queue on 126,
count on 127 and ambient output on 132; all left stacks and native input/output
are restored.

`lengthKeyLoop_spec` structurally proves one fixed loop for an arbitrary distinct
key list. Each iteration invokes the actual runtime-selected solver/publication
program. The induction retains the final accuracy of every processed class by
preserving its physical reads through the remaining iterations. It consumes
exactly the owned count and packet prefix, leaves the borrowed key suffix and
output suffix intact, and handles an empty schedule directly. No saved counter
archive is required: the generated count is owned and consumed by the loop.

`runLengthKeys_spec` reads the initial count and enters that loop. Its bound is
`sum(keys.map (fun L => 6*L+19*V+14 + conditionalNaturalClassCost(...,L,...) + 3))+2`:
three per-key control steps, one initial count read and one terminal loop test,
in addition to the already paid decoder/class costs.
`runNaturalLengthKeys_spec` instantiates the exact positive distinct schedule,
including empty candidate classes, with the shared padding and binary-width
bounds. Coverage of the original interior transfers the loop's final per-class
accuracy to `ErrorOn (interiorSet ...)` on the final physical ambient output,
with the requested `1/2^target` bound and no class-count factor.

The loop theorem starts from the queued generated keys/count and retained
ordinary headers. Composing their executable initialization (including the
protected width headers) and final release remains open. Uniform fast
solver/time and execution-wide storage bounds, artificial halo cuts and
complex/boundary/coupling/recovery/full-line composition also remain open.
S3 is incomplete and the proved saving is unchanged.

The counted-loop/whole-interior checkpoint passes all 9927 guarded S3
axiom-audit jobs at 2.6 GiB combined peak. All eight new modules pass individual
guarded checks; the largest final-check peak is 1974.0 MiB. Default proof limits
are unchanged. Source integrity, generated-summary and whitespace checks pass.


### S3 initialized whole-interior execution and final release

`preparePositiveLengthKeys_exec` retains the generated word and arithmetic widths
alongside the positive distinct key packets and owned count. The existing
`generatePositiveLengthKeys_exec` API reuses this producer and clears the widths,
so its statement and cost remain unchanged. No second candidate or origin scan
is introduced to initialize the protected loop.

`protectedPrepareLengthKeys_exec` runs that producer in the private bank while
preserving all caller registers. `installKeyRuntime_exec` copies the two widths
into their retained caller headers, transfers the packet queue in order using
two moves, transfers the unary count, and clears the generated private operands.
Its exact cost is `6*(V+w)+4*keys.length+2*K+19`. The pure frame lemmas commute
these caller updates with private header copies without enumerating the full
register bank.

`initializeLengthKeys_exec` composes master-header copying, private key generation,
caller installation and release of the private header copies. It starts from
ordinary retained master parameters and blank private workspace, preserving the
raw source and borrowed queue suffix. `LengthKeyReady.initialized` establishes
the solver-loop invariant from the initialized state.

`solveNaturalInterior_spec` composes initialization, the counted natural-key loop
and `releaseKeyRuntime_exec`. The fixed program consumes exactly the generated
queue/count and releases both retained widths. Its exact final stack record is
`{ S with R := Function.update S.R 132 (E'++outputTail) }`: native input/output,
all left stacks, raw input, master parameters, borrowed suffixes and every other
right stack are restored. The physical final output satisfies the whole-interior
error bound `1/2^target` without a class-count factor. The execution bound is the
sum of initialization, counted-loop and final-release costs.

This closes the executable initialization/loop/release composition. Uniform
fast solver/time and execution-wide storage bounds, artificial halo cuts and
complex/boundary/coupling/recovery/full-line assembly remain open. S3 remains
incomplete and the proved saving is unchanged.

The initialized-interior checkpoint passes all 9935 guarded S3 axiom-audit jobs
at 2.7 GiB combined peak. All nine new or revised non-audit modules pass final
individual guarded checks; maximum measured peak is 1986.2 MiB. Default proof
limits are unchanged. Source integrity, generated-summary and whitespace checks
pass.


### S3 whole-interior setup, coordinate and cell cost ledger

`sizedClosedBatchBound_eq` separates the entire executed batch cost exactly as
`setup(L) + B*L*batchCoordinateCost + B*batchCellCost`. It covers generated
weights, four padded short-convolution records per cell, real multiplications,
payload movement, publication and final cleanup. The nonlinear numerical
construction remains in `setup(L)` and is paid once per length class.
The repeated coefficients are independent of the batch count, class length and
cell origins; their full arithmetic costs remain explicit.

`naturalPositiveLengthKeys_cell_count` proves that the selected classes contain
at most `t-s+1` cells in total. The existing exact coordinate-volume identity
counts every interior coordinate once. `naturalPositiveLengthKeys_cost_le`
combines these facts with the sublist of the four fixed length candidates:
shared setup is bounded by those four candidate setups, coordinate work by the
exact interior cardinality, and padded cell work by the number of natural phases.
There is no class-count factor on either repeated-work term.

`naturalClassCost_le` covers the actual empty/nonempty class branches, key
decoding, origin scanning, gather-control generation, ambient gather/scatter and
the numerical batch. `initializeLengthKeysCost_le` removes the selected-key
count from the setup bound using the four-key limit. `solveNaturalInteriorCost_le`
then bounds the actual initialized solver by `naturalInteriorCostBound`, including
initialization and final width release. The resulting whole-line ledger is
`initialization + four candidate setups + interiorCard*coordinateCost +
(t-s+1)*cellCost + loop termination + final release`.

This establishes the geometry-separated executed ledger, not the required fast
asymptotic estimate. In particular, the current coordinate coefficient includes
`(310*P+124)*tblC V w` for weight generation; its cost must be addressed rather
than hidden in an assumed fast rate. Fast time and execution-wide storage,
artificial halo cuts and complex/boundary/coupling/recovery/full-line assembly
remain open. S3 is incomplete and the proved saving is unchanged.

The whole-interior cost checkpoint passes all 9939 guarded S3 axiom-audit jobs
at 2.7 GiB combined peak. All four new modules pass final individual guarded
checks; maximum measured peak is 1995.2 MiB. Default proof limits are unchanged.
Source integrity, generated-summary and whitespace checks pass.


### S3 exact equal-origin weight/inverse reuse across RHS replicas

The current scalar whole-interior ledger exposes numerical weight evaluation
per coordinate. The new equal-origin batch entry preserves the exact existing
weight words and numerical error analysis, while moving that evaluation outside
the replica loop. Sharing requires identical ambient origin, cell length,
geometry and precision, not merely equal lengths. Each replica may carry a
different raw RHS. This is the full numerical reuse key for this cell primitive;
local halo/cut reuse and the outer grouped-line schedule remain separate gates.

`repeatWeightBanks_exec` uses counted copies to stage both halves of one exact
weight page, restoring the original page, row/batch counters and all borrowed
suffixes. `packRepeatedWeights_exec` releases that single source page and
publishes the two repeated banks in the existing runtime order.
`replicateWeightPage_exec` generates/releases the row-symbol count and restores
all other stacks, with cost `B*(70*L*w+77)+24*L*w+9*L+62`.
`repeatedWeightSetup_exec` generates the single numerical page from ordinary
unary headers, then executes this replication. It requires no supplied pi,
exponential, weight page or prepared table state.

`finishBatchSetup_exec` supplies the shared inverse continuation.
`repeatedBatchWeightedSetup_exec` generates word width and exact weights,
releases the owned unary origin, constructs one inverse and installs the
ordinary batch bank. `repeatedGeneratedBatchSetup_exec` then routes the distinct
raw RHS blocks into the existing arithmetic ABI. Its exact affine cost is
`setup(0) + B*(154*L*(2*q+8)+15*L+141)`: all weight and inverse construction is in
`setup(0)`, and the repeated coefficient contains only word transport.
`repeatedBatchInputBank_setup_exec` closes that entry from a concrete raw bank
with one unary ambient origin, rather than one binary origin packet per replica.

`repeatedGeneratedBatch_sized_exec` composes this setup with the existing actual
normalized arithmetic and publication. `repeatedClosedBatch_sized_exec` releases
the runtime pages/counters. `repeatedClosedBatch_spec` proves requested
`1/2^target` accuracy on every original-coordinate core for distinct RHS replicas,
with the same magnitude, geometry and solve assumptions as the prior cell
primitive. Every private stack is blank at return except the published output
and restored raw RHS/borrowed suffix; no replica-count error factor is added.

`repeatedClosedBatchCost_eq` separates the complete generated/cleaned execution as
`setup(0) + B*L*coordinateCost + B*cellCost`. With execution word width `w` and
precision `q`, the repeated coordinate coefficient is
`3*rmulCost(w)+885*w+4*(inputExponent+2*l+2)+433`; the cell coefficient is
`4*rpRecBound(q,l,w)+248*2^l*w+781`. Neither contains the table exponential
compiler or an inverse-construction cost. The exact numerical construction
remains fully charged once in shared setup.

The existing single-line `solveNaturalInterior` caller is unchanged and still
uses its original per-coordinate weight-generation ledger. Connecting grouped
RHS lines to the new equal-key entry, proving actual setup multiplicities and
amortization, fast asymptotic time and execution-wide storage remain required.
Artificial halo cuts and complex/boundary/coupling/recovery/full-line assembly
also remain open. S3 is incomplete and the proved saving is unchanged.

The equal-origin replica checkpoint passes all 9951 guarded S3 axiom-audit jobs
at 4.2 GiB combined peak. All twelve new modules pass final individual guarded
checks; maximum measured peak is 1967.3 MiB. Default proof limits are unchanged.
Source integrity, generated-summary and whitespace checks pass.


### S3 raw equal-origin replica gathering

`flatten_uniform_window` proves a generic physical-slice identity over arbitrary
fixed-width rows. `replicaAmbientStream_window` instantiates it for distinct
ambient RHS lines: the slice at symbol position `(n*s+origin)*w` is exactly
replica `n`'s `cellSourceRows` input at the same ambient origin. The proof requires
`origin+L≤s`, so no row reads through into the next RHS line.

`replicaSymbolOrigins_ordered` and `replicaSymbolOrigins_fit` establish one ordered
sweep over these windows. `replicaGather_exec` executes the existing restoring
gather engine, generates/releases its row-symbol count, and publishes the exact
numerical RHS batch in replica order. Native/left stacks, source, controls and
all scratch restore; total source movement is bounded by `B*s*w` for `B` replicas.

`unaryGatherControl_exec` and `repeatUnaryGatherControl_exec` generate delimited
control packets from retained unary dimensions. `generateReplicaControls_exec`
constructs the initial origin seek, repeated line strides and terminal zero
advance. It uses one owned copy of the positive replica count and restores every
source dimension and temporary counter. No binary table arithmetic or supplied
control stream is needed.

`rawReplicaGather_exec` composes runtime width/control generation, paid copying
of the complete ambient batch, the actual sweep, and release of every generated
count/control/width and source copy. It begins with raw consecutive ambient RHS
lines and ordinary unary dimensions. Its exact final frame changes only 110,
prefixing the gathered numerical RHS to the unchanged original ambient input and
arbitrary borrowed suffix. `rawReplicaGatherCost_le` bounds this transport by
`250*B*s*(2*q+8)` for a positive batch and nonempty in-bounds cell.

This closes the raw transport for one selected ambient origin. Repeating a full
ambient-batch sweep separately for every cell would introduce an extra factor;
that schedule is not claimed fast. The shared contract assigns grouped exposure/
publication and layout restoration to S4/R4. The fast outer composition still
needs an exposure/transposition schedule with proved multiplicities, and must
charge these transfers explicitly. The exact equal-key solver itself retains
its setup-once cost decomposition. Fast amortization/storage, artificial halo
cuts and complex/boundary/coupling/recovery/full-line assembly remain open.
S3 is incomplete and the proved saving is unchanged.

The raw-replica-gather checkpoint passes all 9957 guarded S3 axiom-audit jobs
at 2.7 GiB combined peak. All six new modules pass final individual guarded
checks; maximum measured peak is 1950.6 MiB. Default proof limits are unchanged.
Source integrity, generated-summary and whitespace checks pass.


### S3 generated artificial halo cuts and executed clipped cells

`haloStart`/`haloStop` clip the original ambient natural-cell intervals against
`[a+band,b-band)`. The active interior `haloInterior` is the original computed
interior intersected with those artificial endpoint guards. Empty and overlapping
guards give empty cells directly. The ambient modulus, phase numbering,
coefficient precision and matrix remain unchanged; no phase is restarted or
periodic wrap introduced at a halo edge.

`haloInterior_phase_iff` identifies each clipped interval exactly with its
ambient phase fiber in the selected interior. `haloCells_cover` proves the
positive generated phase list covers that interior. `halo_solver_geometry`
proves nonwrapping endpoints, original ambient interior membership, constant
phase and complete coverage of that phase inside the selected halo interior.
`haloCells_ordered` separates different phase intervals. `haloIntervals_volume`
and `haloCellPhases_volume` give the exact interior cardinality from the full
phase scan and from its positive clipped-cell list respectively.

Only intervals containing one of the two artificial endpoints can have a changed
length. `haloPhase_left_cut`/`haloPhase_right_cut` identify their ambient phases.
`haloLengthCandidates` contains the four original candidates and the two computed
clipped endpoint lengths. `haloLengthKeys_cover` and `haloLengthKeys_length_le`
prove a complete positive distinct schedule with at most six length keys.
`haloLengthKeys_pad` preserves the common original padding bound because clipping
cannot increase any interval length. These are computable metadata formulas;
their tape-level descriptor/key generation is still an execution obligation.

`haloBoundary` is exactly the selected halo vertices minus the computed interior.
`haloInterior_union_boundary` and `haloInterior_disjoint_boundary` prove the
partition. `haloBoundary_card_le` charges the original boundary vertices inside
the halo plus at most `2*band` for the two artificial endpoint guards. It makes
no local bandwidth, support/fill or boundary factorization claim; those remain
S5 obligations.

`repeatedHaloCell_spec` executes the generated/cleaned equal-key replica solver
on each selected clipped cell, deriving all geometry from the halo formulas and
generated phase membership. No free mask, interval cover, phase oracle or
per-cell padding bound is requested. Distinct replica RHSs satisfy the same
requested `1/2^target` original-coordinate core error on the selected halo
interior system, with no replica-count factor. This is an interior pass, not a
full halo solve: boundary/coupling/recovery and arithmetic-to-global locality
composition are not supplied by the theorem.

Grouped-line integration and paid setup multiplicities, fast time/storage,
tape-level halo descriptor/key generation and complex/boundary/coupling/recovery/
full-line assembly remain open. S4 still owns global locality and external
layout/exposure. S3 is incomplete and the proved saving is unchanged.

The clipped-halo-cell checkpoint passes all 9963 guarded S3 axiom-audit jobs
at 2.7 GiB combined peak. All six new modules pass final individual guarded
checks; maximum measured peak is 1947.6 MiB. Default proof limits are unchanged.
Source integrity, generated-summary and whitespace checks pass.

### S3 executed halo descriptor generation

The fixed 117-tape `generateHaloDescriptors` program starts from ordinary unary
parameters, generates both runtime widths, loads the five geometry headers,
computes the ambient phase constants, clips each cell at the halo endpoints and
emits only positive origin/length pairs in ambient phase order. The packet
representation and exact two-word descriptor length are proved. All temporary
stacks are released; only the descriptor prefix on stack 109 changes, preserving
its borrowed suffix and every other stack. Costs include width generation,
header loading, the bounded phase scan, output movement and release.

This closes descriptor generation, not the halo solver. Six-key tape scheduling,
grouped integration/amortization, uniform fast time and execution-wide storage,
and complex/boundary/coupling/recovery/full-line assembly remain open. S3 remains
partial.

Validation: all 9,970 stage audit jobs pass with only approved axioms; the
guarded audit build peaks at 2.7 GiB. All seven new modules pass individual
guarded checks, each at most 1855.1 MiB. Proof-integrity and plan checks pass.

### S3 executed six-key halo generation

The fixed `generateHaloLengthKeys` program now computes all six halo length
candidates from ordinary unary parameters, removes zero and duplicate lengths,
and publishes the exact `haloLengthKeys` packet list and its owned unary count.
The two extra lengths use the original ambient phases at the halo cuts. Endpoint
registers survive the four-candidate ambient calculation through explicit save
and restore instructions. The phase calculation and interval arithmetic also
cover a left cut beyond the ambient interval without resetting the phase.

Width generation, header loading, bounded arithmetic, six-word selection,
counting, packet movement and release are paid in the execution theorem. The
borrowed packet suffix is preserved; every other stack is restored except the
owned key count. A retained-width variant is available for the solver iterator.

S3 remains partial. Executing halo length classes, grouped integration and
amortization, uniform fast time and execution-wide storage, and complex/
boundary/coupling/recovery/full-line assembly remain open.

Validation: all 9,978 audit jobs pass with only approved axioms. The final
guarded audit build peaks at 2.7 GiB; all twelve new or revised non-audit
modules pass individual guarded checks, each at most 1866.5 MiB. Source
integrity, plan-status and whitespace checks pass.

### S3 clipped length classes and closed group accuracy

`haloLengthGroup` selects positive clipped cells of one length in ambient phase
order. Its generated origins satisfy the solver geometry contract. The generated
halo keys cover exactly the clipped interior through these groups, and uniform
per-cell error composes without a factor for the number of keys.

`generateHaloClassControls` starts with ordinary unary geometry and a positive
length, generates its widths, emits the exact class origins and owned unary
count, then releases all scratch. The origin packet representation matches the
closed batch solver. `closedHaloGroup_spec` executes that solver for a nonempty
class on the clipped interior of the same ambient matrix, with accuracy, cost,
output size and cleanup proved.

The control producer and closed group solver remain separate execution pieces.
RHS gathering/publication and the key-loop composition still need integration.
Grouped amortization, uniform fast time and execution-wide storage, and complex/
boundary/coupling/recovery/full-line assembly remain open. S3 remains partial.

Validation: all 9,987 stage audit jobs pass with only approved axioms. The
guarded audit build peaks at 2.7 GiB; all nine new modules pass individual
guarded checks, each at most 1946.1 MiB. Source-integrity, plan-status and
whitespace checks pass.

### S3 restoring halo RHS gathering and advance conversion

Clipped class origins are ordered fitting windows in the original ambient line.
The exact encoded windows equal the closed solver's RHS rows. Their coordinate
volume is at most the ambient dimension. A shared structural execution lemma
now handles arbitrary ordered fitting windows; the natural and halo gather
contracts instantiate it.

`preparedHaloAdvanceControls_exec` executes the existing origin converter on
halo packets, constructs and releases its table bank, restores the origin queue
and count, and emits exactly the restoring sweep controls. Conversion ticks are
bounded by one encoded ambient line. `rawHaloGather_exec` copies the owned
ambient prefix, gathers the exact clipped-class RHS and releases copies and
controls. The original ambient prefix and arbitrary borrowed suffix remain
under the RHS. Its proved bound is `rawNaturalGatherCost q s`, including width
generation, counters, source copying, sweep movement and release.

Ordinary class metadata, advance conversion, gathering and the closed solver
still need one composed input-bank theorem. Publication and the halo key loop,
grouped amortization, uniform fast time/storage and complex/boundary/coupling/
recovery/full-line assembly remain open. S3 remains partial.

Validation: all 9,996 stage audit jobs pass with only approved axioms. The
guarded audit build peaks at 7.3 GiB; all ten new or revised non-audit modules
pass individual guarded checks, each at most 1948.8 MiB. Source-integrity,
plan-status and whitespace checks pass.

### S3 raw halo group composition

`rawHaloGroup_spec` now composes the ordinary unary-parameter caller with the
closed group solver. One pair of generated widths serves origin/count discovery
and advance conversion. The program generates every origin and sweep control,
gathers its own RHS from the ambient line, releases the widths and owned halo
endpoint headers, and reaches the exact closed solver input bank.

The executed solver returns the uniform cell error and exact encoded output
size, with only the solver output and RHS/source payload remaining. The original
ambient prefix and borrowed suffix remain under the gathered RHS. The cost
bound includes metadata, conversion, gathering, endpoint release and the closed
solver. The previously released-width metadata API is retained as a short
composition of the new shared-width producer and release.

Publication and the protected halo key loop remain open, alongside grouped
amortization, uniform fast time and execution-wide storage, and complex/
boundary/coupling/recovery/full-line assembly. S3 remains partial.

Validation: all 10,002 stage audit jobs pass with only approved axioms. The
guarded audit build peaks at 2.7 GiB; all seven new or revised non-audit
modules pass individual guarded checks, each at most 1971.1 MiB. Source
integrity, plan-status and whitespace checks pass.

### S3 halo publication and class preservation

The clipped equal-length windows are disjoint in ambient order. Their existing
origin advances yield the exact forward publication gaps, including word-level
alignment. The gap controls are generated by the existing converter, with its
source controls and count restored. `protectedHaloPublicationControls_exec`
constructs the encoded window counter and releases its temporary counters.

`protectedHaloScatter_exec` executes publication of the solved class into an
ambient output prefix, consumes exactly the owned solver rows, restores the
borrowed source/output suffixes, and clears the owned publication controls and
counter. The cost is bounded by `54*s*w+15`. The physical reads inherit the
solver's uniform error. Publishing a different length class preserves every
word and its established error on earlier classes.

The protected raw halo caller and key-loop composition remain open. This is
publication execution, not a completed whole-halo solver. Grouped amortization,
uniform fast time and execution-wide storage, and complex/boundary/coupling/
recovery/full-line assembly also remain open. S3 remains partial.

Validation: all 10,011 stage audit jobs pass with only approved axioms. The
guarded audit build peaks at 2.7 GiB; all nine new modules pass individual
guarded checks, each at most 1930.3 MiB. Source-integrity, plan-status and
whitespace checks pass.

### S3 complete protected nonempty halo class

The 144-stack caller retains halo endpoints on 141 and 142, copies them into
the private solver bank with proved costs, and preserves them with the existing
master parameters. The projected private state is exactly the ordinary halo
input bank. Gathering and endpoint release are factored into one reusable
controlled-bank continuation.

`protectedHaloClass_spec` now composes header installation, metadata and gather
controls, protected publication-control generation, raw RHS gathering, actual
closed numerical solve, RHS retirement, physical ambient publication and class
cleanup. Its final stack map preserves the raw source, borrowed suffixes, master
parameters and endpoints; only the published ambient output and consumed class
workspace change. Exact output volume and uniform error on every selected cell
are proved. All generation, movement, solve and release costs are included.

This covers a nonempty clipped length class. The generated-key loop must still
handle empty classes and compose coverage and preservation over every halo key.
Grouped amortization, uniform fast time and execution-wide storage, and complex/
boundary/coupling/recovery/full-line assembly remain open. S3 remains partial.

Validation: all 10,018 stage audit jobs pass with only approved axioms. The
guarded audit build peaks at 2.7 GiB; all eight new or revised non-audit
modules pass individual guarded checks, each at most 1987.0 MiB. Source
integrity, plan-status and whitespace checks pass.

### S3 counted halo key loop with empty classes

The class probe scans origins once and exposes the actual row count. Nonempty
classes reuse the retained metadata through advance generation, solve and
publication. Empty classes release widths, private endpoint and ordinary header
copies, and the current length without touching payloads or retained masters.
The conditional class operation has one exact frame and uniform-error contract
for both branches.

`runGeneratedHaloKeys_spec` now executes the counted loop over the generated
positive distinct halo key list, from the prepared outer bank. It consumes only
the owned key/count prefixes, preserves borrowed key/output suffixes, handles
empty classes and proves uniform accuracy over the entire clipped interior.
Previously published classes retain their exact physical reads, so the final
error has no key-count factor. Every class and loop operation is paid.

The halo grouped amortization still needs to transfer generated keys and widths
into this bank and release its runtime headers. Grouped amortization, uniform
fast time and execution-wide storage, and complex/boundary/coupling/recovery/
full-line assembly remain open. S3 remains partial.

Validation: all 10,030 stage audit jobs pass with only approved axioms. The
guarded audit build peaks at 2.7 GiB; all twelve new modules pass individual
guarded checks, each at most 2000.7 MiB. Source-integrity, plan-status and
whitespace checks pass.

### S3 initialized halo interior solver and whole-interior ledger

`solveHaloInterior_spec` is now one fixed initialized program from ordinary
retained master parameters, endpoints and raw ambient input. It generates its
positive distinct keys, count and both widths, transfers them into the outer
runtime, releases private header copies, executes the counted halo class loop
and releases runtime widths. Every stack except the ambient output is restored
exactly, including raw source, endpoint/master headers and borrowed suffixes.
Uniform error on the complete clipped interior of the original ambient matrix
is proved. No prepared key queue or count is an input.

The halo schedule has exact coordinate volume equal to the clipped interior
cardinality, at most one cell per original phase, and at most six key setups.
`solveHaloInteriorCost_le` separates these charges for the actual executed
program, including initialization, endpoint handling and final release. The
private header-release proof is shared with empty-class cleanup.

This is a geometry-separated ledger, not the required fast asymptotic estimate.
Grouped amortization and execution-wide storage remain open. Complex execution,
boundary/coupling/recovery and full-line assembly are also incomplete. S3 remains
partial.

Validation: all 10,038 stage audit jobs pass with only approved axioms. The
guarded audit build peaks at 2.7 GiB; all nine new or revised non-audit
modules pass individual guarded checks, each at most 2005.7 MiB. Source
integrity, plan-status and whitespace checks pass.

### S3 raw repeated halo cell and replica ledger

`rawRepeatedHaloCell_spec` now connects the restoring replica gather to the
shared numerical kernel. It starts from ordinary dimensions and a batch of
distinct raw RHS lines at one generated clipped cell, constructs its own controls
and exact gathered RHS, then executes one shared weight/inverse setup and every
replica solve. The raw source and borrowed suffix remain under the owned RHS;
output volume, uniform error and private scratch release are proved. The
caller still owns explicit retirement/publication of those prefixes.

The combined execution cost has an exact affine replica decomposition: adding
a replica repeats coordinate arithmetic and transport, not numerical setup.
Aggregating the ledger over generated halo cells gives exact replica-coordinate
volume from the clipped interior cardinality. A separate bound keeps the full
source scan for every cell explicit. It does not infer fast grouped execution
from this scan-based caller.

The shared contract assigns external exposure/publication to S4/R4. Iteration
over same-key replica groups, its actual setup multiplicity/amortization and
execution-wide storage remain open, alongside complex/boundary/coupling/recovery/
full-line composition. S3 remains partial.

Validation: all 10,043 stage audit jobs pass with only approved axioms. The
guarded audit build peaks at 4.3 GiB; all five new modules pass individual
guarded checks, each at most 1958.9 MiB. Source-integrity, plan-status and
whitespace checks pass.


### S3 counted replica halo schedule

`runReplicaHaloCells_spec` executes one fixed counted descriptor loop over all
positive clipped halo phases. Each descriptor decodes its ambient origin and
length, copies retained scalar inputs, gathers all distinct RHS replicas,
performs shared setup and every solve, retires gathered RHS and releases private
headers. The queue and count are consumed; all other stacks except the packed
output restore exactly. Arbitrary queue/output suffixes are preserved.

Returned blocks are related to the generated phase list in order, and their
physical packed prefix has exactly `B * haloInterior.card * executionWidth`
symbols. Selecting a coordinate from its original ambient phase block gives
uniform error on the complete clipped interior for every replica, without a
factor for the number of phases. The exact loop ledger charges one setup per
phase; increasing the replica count repeats only coordinate and per-cell work.

This caller requires the generated descriptor queue, count and retained scalar
bank already installed. Initializing that runtime, external publication and
execution-wide storage remain open. Full-source scans remain paid per cell;
the ledger is not a fast asymptotic bound. Complex/boundary/coupling/recovery and
full-line composition remain incomplete. S3 remains partial.

Validation: all 10,059 stage audit jobs pass with only approved axioms. The
guarded audit build peaks at 2.7 GiB; all six new modules pass individual
guarded checks, each at most 1982.0 MiB. Source-integrity, plan-status and
whitespace checks pass.


### S3 initialized raw replica halo interior

`solveReplicaHaloInterior_spec` now runs the complete clipped interior for a
positive batch of distinct raw RHS lines from ordinary retained parameters,
endpoints and replica count. The caller generates binary origin/length packets,
counts those generated packets, installs runtime widths and releases private
setup before executing the counted numerical loop. Endpoint stacks are borrowed
as replica scratch through priced save/copy/release operations and restored with
their exact original contents. No descriptor queue, loop count or width page is
supplied as an input.

Only the solved packed output prefix changes. Its exact volume and uniform
interior error for every replica are proved against solutions of the original
ambient matrix on the clipped interior. The full cost includes initialization,
all cell calls, endpoint handling and final width release. Its affine replica
identity separates one-time setup from coordinate/per-cell work and the six
additional count-handling operations per replica.

External publication remains S4/R4-owned. Full-source scans are still paid per
cell, so this is not the required fast time bound. Uniform fast time/storage,
complex execution, boundary/coupling/recovery and full-line composition remain
open. S3 remains partial.

Validation: all 10,065 stage audit jobs pass with only approved axioms. The
guarded audit build peaks at 2.7 GiB; all six new modules pass individual
guarded checks, each at most 2015.5 MiB. Source-integrity, plan-status and
whitespace checks pass.


### S3 fixed-point residual and recovery row arithmetic

`fixedPointRowPrepared_exec` and `fixedPointRowCall_exec` generalize the existing
integer row machine to an arbitrary grid precision without changing its program.
The integer contracts are now zero-precision specializations of the common
structural proof. The borrowed source, coefficient and RHS streams retain their
arbitrary suffixes, every scratch stack restores, and only the result prefix
changes. The actual cost is linear in the advertised row support times the
scalar multiplication/word cost.

`couplingRowCall_spec` derives operand and accumulator word fits from magnitude
exponents and a support-count bound. Its decoded error is at most one product
tolerance per support entry; subtraction is exact on integer numerators.
`couplingSupportRow_spec` adds separate RHS, coefficient and computed-input
errors. Input error is multiplied by row mass; coefficient and arithmetic errors
are charged by actual support, with no ambient-line cardinality substituted.
These contracts apply to both residual and recovery arithmetic on their computed
inputs, including the separately stated larger recovery magnitudes.

This is a restoring arithmetic kernel, not a closed coupling pass. Generating
matrix coefficients, selecting/staging the true support, iterating the residual
and recovery rows, and their full-line composition remain open. S3 also still
requires uniform fast time/storage, complex and prepared-boundary integration.

Validation: all 10,070 stage audit jobs pass with only approved axioms. The
full guarded rebuild peaks at 26.8 GiB; all seven new or revised non-audit
modules pass individual guarded checks, each at most 1924.9 MiB. Source-integrity,
plan-status and whitespace checks pass.


### S3 direct cross-cell coefficient execution

`PhaseCellLatticeArgs` gives an unreduced natural numerator and denominator for
the direct lattice exponent, retaining upward-tie nearest rounding. The
subtracted square is proved smaller before natural subtraction is used, and
`direct_sample` identifies the resulting corrected exponential exactly with the
existing `PhaseCellCrossCell.direct` coefficient of the original rounded matrix.
No rational normalization or ideal-exponential replacement is assumed.

`directCoefficientBody_do` executes argument construction, corrected exponential
evaluation and q-grid encoding in the 48-variable table machine. Semantic sample
precision P and arithmetic grid precision q are distinct. The host execution
constructs the word, prefixes it to the output stream, and releases the owned
63-register table bank with a paid cost. Norm, storage fit and grid error bounds
are proved for the produced coefficient; the cross-cell selection theorem
compares it to the selected original unaliased entry.

`couple_eq_offsetList` separately proves that enumerating retained signed lattice
offsets gives the exact original principal-system coupling. Repeated wrapped
residues contribute with their full multiplicity. This is the semantic support
contract for the forthcoming generator, not a supplied deduplicated column mask.

The direct host starts from an initialized binary parameter bank with explicit
workspace inequalities. Ordinary-header loading/width selection, signed-coordinate
lifting, the within-cell coefficient branch, generated masks/support and the
complete coupling row loop remain open. Fast time/storage and the remaining
complex/boundary/recovery/full-line assembly are still incomplete; S3 is partial.

Validation: all 10,078 stage audit jobs pass with only approved axioms. The
guarded audit build peaks at 2.7 GiB; all eight new modules pass individual
guarded checks, each at most 1903.9 MiB. Source-integrity, plan-status and
whitespace checks pass.


### S3 signed-offset direct coefficient caller

Integer-period identities now preserve nearest rounding, rational beta/potential,
phase selection and both branches of the selected coefficient. Every retained
signed offset is lifted to nonnegative source/target coordinates by a proved
multiple of the original ambient period. The wrapped source coordinate and the
original coefficient are unchanged; no new halo wrap or phase reset is introduced.
The table implementation proves the negative sweep subtraction cannot underflow.

`liftedCoefficientFromHeaders_exec` loads ordinary scalar/coordinate/precision
headers, generates pi and both q/P powers, executes the lift and direct sample,
and releases the owned table workspace. All native/left stacks, input and
parameter headers restore exactly; only the coefficient output prefix changes.
The execution cost includes loading, generated constants, evaluation and release.
`lifted_cross_coefficient_error` compares the generated q-grid word to the
original signed-offset cross-cell entry, with no precomputed pi, powers or
exponential argument supplied.

The caller still takes width counters satisfying explicit workspace inequalities.
Generating a uniform width selection, implementing the within-cell coefficient
branch and row masks/support, and iterating complete coupling/recovery passes
remain open. Boundary/complex/full-line assembly and uniform fast time/storage
are also incomplete. S3 remains partial.

Validation: all 10,085 stage audit jobs pass with only approved axioms. The
guarded audit build peaks at 2.7 GiB; all seven new modules pass individual
guarded checks, each at most 1952.5 MiB. Source-integrity, plan-status and
whitespace checks pass.


### S3 generated direct-coefficient workspace

`liftedCoefficientWidth_fits` proves one shared workspace width from arithmetic
word width, q, P and binary sizes of s,t,u and band. It covers every ambient row
index and either sign of every retained band offset, including lifted coordinates,
nearest-rounding products, squared distances and the exponential's largest
intermediate. The proof uses structural polynomial bounds; callers no longer
supply a separate inequality for each table operation.

`generateLiftedCoefficientWidth_exec` constructs that width from ordinary unary
headers. A generic list proof accumulates binary sizes, and the fixed header
schedule is instantiated last. Header scans and all scratch restoration are paid.
`closedLiftedCoefficient_exec` composes width generation, ordinary parameter
loading, constant/lift/sample generation and final width release. Only the
coefficient output prefix changes, with arbitrary suffixes preserved exactly.
`closedCrossCoefficient_spec` also proves the actual decoded word is within
`2^-q` of the original selected signed-offset cross-cell entry, using a derived
word fit and no supplied workspace or result-fit premises.

This completes workspace selection for the direct coefficient primitive, not
the coupling pass. The within-cell branch, phase selection, generated row
masks/support, coupling/recovery iteration, uniform fast time/storage and
complex/boundary/full-line composition remain open. S3 remains partial.

Validation: all 10,091 stage audit jobs pass with only approved axioms. The
guarded audit build peaks at 2.7 GiB; all six new modules pass individual
guarded checks, each at most 1926.4 MiB. Source-integrity, plan-status and
whitespace checks pass.


### S3 executed within-cell coefficient kernel

`withinCoefficientBody_do` constructs the two unreduced similarity arguments
and the Gaussian distance argument, evaluates the actual corrected samples and
emits one q-grid coefficient using natural multiplication and division. The
formula agrees exactly with the selected within-cell entry, including rational
zero-denominator behavior, and introduces no intermediate q-grid rounding.
A register permutation reuses the similarity argument proof while retaining
both stored samples and the q/P powers. The body costs `930*P+352` table steps.

`withinCoefficientHost_exec` lowers the body to the finite host, releases its
owned table bank and preserves an arbitrary output suffix. The selected
geometric budgets give coefficient norm at most `2^(8*p+1)` and the derived
word fit; q-grid error is at most `2^-q`. Integer-period invariance connects the
lifted within-cell word to the original signed-offset selected entry when the
phases agree.

`withinCoefficientWidth_fits` proves that the existing shared logarithmic
workspace covers every similarity and distance intermediate at all ambient
rows and signed band offsets. `liftedWithinCoefficientCode_do` generates pi,
the grid powers and nonnegative coordinate lifts from ordinary table inputs;
it needs no supplied operation-fit inequalities and costs `1084*P+4*q+768`.

The ordinary unary-header caller, workspace generation/release around this
branch, phase selection and generated row support/iteration remain open.
Uniform fast time/storage and complex/boundary/recovery/full-line assembly
are also incomplete. S3 remains partial.

Validation: all 10,103 stage build jobs pass, including the 18 new theorem
axiom checks with only approved axioms. The guarded audit build peaks at
2.7 GiB. All twelve new modules pass individual guarded checks, each below
2 GiB. Source-integrity, plan-status and whitespace checks pass.


### S3 closed coefficient selection for all retained offsets

`phaseArguments_do` computes the two natural comparison values
`nearestNatural j+k` and `nearestNatural k+j`; their equality is exactly the
original integer phase equality. `phaseCoefficientWidth_fits` covers both sums
with the same generated logarithmic workspace used by the numerical branches.
The table equality combinator pays for its two strict comparisons.
`selectedCoefficientBody_do` handles the unit diagonal and selects the actual
within-cell or direct cross-cell branch at the original lifted coordinates.
Its uniform table-step bound is `930*P+367`.

`liftedSelectedCoefficientCode_do` generates pi, q/P powers and the signed
coordinate lifts before this selection. It emits the q-grid word of the
original signed-offset selected entry, including offset zero, with no supplied
phase or operation-fit premises. Its bound is `1084*P+4*q+783` table steps.

The ordinary-header loader and workspace-generation/release proof are now
structural lemmas over an arbitrary proved coefficient program. The existing
direct header caller uses the shared loader, and its closed caller reuses the
same workspace-generation/release proof. `closedSelectedCoefficient_exec`
instantiates the complete program from ordinary unary headers, preserving all
outer stacks except the emitted coefficient prefix. At the selected semantic
precision, geometric budgets derive a uniform coefficient magnitude and word
fit. `closedSelectedCoefficient_spec` proves that the actual decoded prefix is
within `2^-q` of the original selected entry for every retained signed offset.
There are no result-fit, phase-selection or supplied workspace premises.

This closes coefficient generation for the retained offset primitive. Generating
whole row support/masks and input gathers, composing the coupling/recovery
iteration, uniform fast time/storage, and complex/boundary/full-line assembly
remain open. S3 remains partial.

Validation: all 10,114 stage build jobs pass, including the 15 new theorem
axiom checks with only approved axioms. The guarded audit build peaks at
2.7 GiB. All thirteen new or revised non-audit modules pass individual guarded
checks, each at most 1938.3 MiB. Source-integrity, plan-status and whitespace
checks pass.


### S3 generated alias-preserving coupling coefficient rows

`appendSelectedCoefficient_exec` executes the closed selected-coefficient
caller and transfers its emitted word from the input port to the row coefficient
port, restoring the input suffix and transfer scratch. A counted offset loop
increments its unary offset header before each call and retains every offset
`1,...,band` for either sign. Its controls are copied from the ordinary band
header and released after each pass.

`generateCouplingCoefficients_exec` composes the zero, positive and negative
passes. The physical prefix is exactly the selected coefficient words on the
reversed `couplingOffsets` list, including every colliding wrapped-column alias.
`prepareCouplingCoefficients_exec` also generates the row multiplier count
`2*band+1`. Only that count and the coefficient prefix change; all other
stacks, including the input suffix, ordinary headers and table banks restore.
The paid cost is at most `2*band+1` times the largest retained-offset call cost,
plus `24*band+21` for the loop and count controls.

`prepareCouplingCoefficients_spec` proves the exact `(2*band+1)*w` prefix
volume and actual decoded error `2^-q` for every emitted word, using selected
geometric magnitude/word bounds and an arbitrary existing output suffix.
`offsetCouplingRow_spec` specializes the restoring arithmetic to these generated
coefficient words. Its target is the original masked real-matrix coupling, not
a deduplicated column approximation; coefficient magnitudes and errors are
proved from the constructor. Computed-input and RHS errors and row mass remain
explicit.

Generating the corresponding masked input gathers, staging multiplication
readiness while protecting/restoring the geometry headers, and composing
coefficient generation with the row arithmetic remain open. Coupling/recovery
iteration, uniform fast time/storage and complex/boundary/full-line assembly
are also incomplete. S3 remains partial.

Validation: all 10,123 stage build jobs pass, including the 13 new theorem
axiom checks with only approved axioms. The guarded audit build peaks at
2.7 GiB. All nine new modules pass individual guarded checks, each at most
1933.0 MiB. Source-integrity, plan-status and whitespace checks pass.


### S3 executed original-geometry masks and restoring masked lookup

`haloInteriorAt_spec` and `haloMaskAt_spec` identify natural point tests with
the existing ambient halo interior and boundary sets. The endpoint guards use
`a+band ≤ k < b-band`; the phase test compares the original phases at
`k-band` and `k+band`. No phase is restarted at an artificial endpoint.
`haloMembershipMaskCode_do` executes both partition masks in at most 25 table
steps, preserving all six geometry inputs. The code checks `band ≤ b` before
subtracting, so empty or short halos need no underflow premise.

`tableBitHost_exec` publishes the computed binary bit as a unary control,
releases the complete private table bank and exposes that control as a branch
flag. `copyIndexedWord_exec` generates the symbol offset from the index and word
width, copies one ambient word and restores the raw source, arbitrary suffixes,
all counters and scratch. Its cost includes the actual source motion,
`k*(12*w+9)+10*w+22`; no uniform fast gather bound is asserted.

`maskedHaloLookup_exec` composes the actual geometry test, table release and
conditional input copy/encoded-zero emission. It consumes the unary mask,
clears the owned table bank and restores every outside register except the
output prefix. `maskedHaloLookup_spec` derives the stored word fit from input
magnitudes and proves that decoding preserves the existing input error on the
selected set and gives exact zero outside it. There is no supplied mask table
or assumed predicate execution.

This lookup starts from an initialized bounded geometry table and a retained
physical query index. Ordinary-header loading, generated workspace, wrapped
signed-offset addresses and the complete masked row-gather loop remain to be
connected. Protecting/restoring geometry during multiplication staging, the
combined coupling/recovery caller and iteration, uniform fast time/storage,
and complex/boundary/full-line assembly remain open. S3 remains partial.

Validation: all 10,135 stage build jobs pass, including the 15 new theorem
axiom checks with only approved axioms. The guarded audit build peaks at
2.7 GiB. All twelve new modules pass individual guarded checks, each at most
1920.6 MiB. Source-integrity, plan-status and whitespace checks pass.


### S3 closed wrapped masked input rows and aligned operands

`haloLookupFromHeaders_exec` initializes and loads the six ordinary geometry
headers before the executed mask/gather operation. A shared structural header
initializer is reused for both geometry and address queries.
`haloLookupWidth_fits` proves that the existing generated logarithmic workspace
covers every mask intermediate, without supplied operation-fit inequalities.

`couplingIndexCode_do` constructs the nonnegative lifted target for either
signed offset and reduces it modulo the original axis size. Its compiled
packet is converted to a unary physical index. `couplingIndex_cast` identifies
that index with the original wrapped column. `closedCouplingLookup_exec`
generates workspace, computes this address, loads/tests original halo geometry,
copies the masked word and releases every query header and table bank. Its
ordinary inputs contain no prepared geometry table, mask or wrapped address.

`generateCouplingInputs_exec` runs counted positive and negative offset passes,
including the zero offset once. Its physical input prefix is the masked ambient
source evaluated on the reversed original `couplingOffsets` list, preserving
all aliases and agreeing exactly with the coefficient row order. The raw source
and arbitrary suffix on its retained source port survive every query. All
counters, generated workspace, geometry and other stacks restore. Its paid cost
is `(2*band+1)*couplingLookupRowCost+20*band+16`; this envelope includes repeated
source motion and does not establish the uniform fast gather bound.

`prepareCouplingOperands_exec` composes the executed coefficient/count generator
with the complete masked input gather. Only the coefficient prefix, input
prefix and row count change. `prepareCouplingOperands_spec` proves exact volume
`(2*band+1)*w` for each prefix, coefficient decoded error at most `2^-q` against
the original selected entry, and masked-input decoded error at most the existing
input error. Storage fits follow from selected geometric budgets and input
magnitudes. There is no supplied operand-fit, mask-execution or schedule oracle.

Capturing the retained ambient source from the outer layout, protecting/restoring
geometry while staging multiplication readiness/RHS, running and releasing the
complete coupling/recovery row, and composing its iteration remain open.
Uniform fast time/storage and complex/boundary/full-line assembly are also
incomplete. S3 remains partial.

Validation: all 10,151 stage build jobs pass, including the 19 new theorem
axiom checks with only approved axioms. The guarded audit builds peak at
2.7 GiB. All sixteen new modules pass individual guarded checks, each at most
1934.8 MiB. Source-integrity, plan-status and whitespace checks pass.


### S3 raw coupling source capture and consumed row operands

`captureCouplingSource_exec` generates the ambient symbol count from the ordinary
axis-size and word-width headers, copies the physical input prefix to the
retained source port and releases the count. The original input and every other
stack are preserved. The paid cost is at most `s*(16*w+9)+16`.

`rawCouplingOperands_exec` composes this capture with aligned operand generation
and releases the source snapshot. Only the input/coefficient prefixes and row
count change; the retained source port returns to its original empty state.
`rawCouplingOperands_spec` derives exact prefix volumes and decoded coefficient
and masked-input error from this actual raw-input execution.

`retireCouplingOperands_exec` generates the common symbol count, consumes both
owned prefixes, preserves their arbitrary suffixes and releases the row count
and scratch, for cost at most `18*L*w+11*L+21`. `consumedIntegerRow_exec` composes
the existing arithmetic caller with this retirement: the result is published,
both prefixes disappear and their count is cleared. Its paid bound is
`L*(rmulCost w+61*w+32)+14*w+76`.

The arithmetic caller still requires installed multiplication readiness and
empty row-work ports. Protecting/restoring geometry, staging readiness and the
actual RHS, composing complete coupling/recovery iterations, complex/boundary/
full-line assembly and uniform fast time/storage remain open. S3 remains partial.

Validation: all 10,156 guarded stage-audit jobs pass, including the five new
explicit theorem audits with only approved axioms; combined peak is 2.7 GiB.
All five new modules pass individual guarded checks at at most 1939.1 MiB.
Source-integrity, plan-status and whitespace checks pass.


### S3 complete raw coupling row with protected geometry

`withSavedHeader_exec` parks an arbitrary header on its own left stack, executes
a framed call and restores the header exactly, for overhead `4*headerLength+4`.
The geometry ports are outside the private multiplier bank. No additional save
registers or prepared copies are required.

`couplingReadiness_exec` reads unary precision from the coupling precision port,
parks/restores the band header occupying the scalar setup port and generates the
three actual multiplier counters. `borrowedRHSRow_exec` borrows a physical RHS
prefix from its retained port, stages it above the untouched precision header,
executes the consumed row and removes the staged RHS. The retained source and
precision header survive. `generatedReadyRow_exec` composes this with readiness
setup and releases every generated counter. `protectedCouplingRow_exec` parks
and restores the three geometry headers needed as arithmetic scratch.

`rawCouplingRow_exec` now composes raw ambient-source capture, aligned masked
input/coefficient/count generation and the complete protected arithmetic call.
Only the result prefix changes: geometry, precision, raw input, borrowed RHS,
coefficient suffix, left stacks and all temporary storage restore exactly.
The explicit cost is operand-generation cost plus generated arithmetic cost and
`4*(s+t+u)+12` for geometry preservation.

`rawCouplingRow_spec` derives operand/result word fits from the geometric budget,
input/RHS magnitudes and support count. Its decoded result approximates the
original masked `b-couple(realMatrix,T,x,i)` with error at most
`L*2/2^q + rhsError + L*2^inputExp/2^q + K*inputError`, where `L=2*band+1` and
`K` bounds original coefficient row mass. All periodic aliases are retained;
there is no prepared readiness, mask, operand or result-fit premise.

This closes the single-row source-capture/geometry/readiness/RHS/retirement
integration gap recorded above. Generating the RHS sequence, executing complete
residual/recovery row iterations, composing the boundary solver and full complex
line, and proving uniform fast time/simultaneous storage remain open. Repeated
source scans are still paid in the current cost. S3 remains partial; the proved
multiplication saving is unchanged.

Validation: all 10,164 guarded stage-audit jobs pass, including eleven new
explicit theorem audits using only approved axioms. The combined audit peak is
2.7 GiB. All eight new modules pass individual guarded checks at at most
1946.6 MiB. Source-integrity, plan-status and whitespace checks pass.


### S3 initialized ambient residual/recovery row pass

`CouplingReady` centralizes the ordinary geometry/precision headers, raw source
and blank arithmetic workspace. Its frame lemma preserves that invariant across
RHS consumption, coordinate advance and output publication. It requires no
installed multiplication counters or prepared numeric tables.

`couplingRowStep_exec` executes the complete raw row, consumes one owned RHS word
and increments the physical coordinate. `outerCouplingRow_exec` embeds this
operation in the existing 144-register caller bank, leaving the outer count
outside the arithmetic footprint. `couplingRowLoop_exec` processes an arbitrary
consecutive RHS segment, preserves every other stack and produces exactly its
structurally defined row results in reverse order.

The shared counted-loop proof now supports varying per-iteration costs:
`countedLoop_exec_costs` bounds the executed loop by the sum of each actual
advertised row cost plus three controller steps per row and two endpoint steps.
The previous constant-cost theorem is a direct specialization of the same proof.

`reversePrefixInPlace_exec` executes coefficient-word reversal above an arbitrary
borrowed suffix, preserving bit order and releasing its generated symbol count
and scratch. `runCouplingRows_exec` generates the whole-line clock from the
ordinary axis-size header, executes every row, publishes in natural coordinate
order and clears the final coordinate and clock. Only the consumed RHS prefix
and new result prefix differ from the original bank; the raw source and all
geometry, precision, outer parameters and left stacks restore exactly.

The explicit bound is `couplingRowLoopCost(...,0,s)+32*s*w+34*s+28`.
`runCouplingRows_spec` derives operand/result fits from magnitudes and proves
exact output volume `s*w`, with uniform original-matrix error
`L*2/2^q + rhsError + L*2^inputExp/2^q + K*inputError` at every ambient coordinate,
where `L=2*band+1`. Row count does not amplify the error.

This executes either residual or recovery row passes from ordinary headers and
physical source/RHS lines. Connecting the solved interior/boundary lines and
retained original RHS to those input ports, composing the prepared S5 boundary
handoff and final interior solve, and full complex-line assembly remain open.
The current ledger still pays repeated source scans; uniform fast time and
simultaneous storage are unproved. S3 remains partial and kappa is unchanged.

Validation: all 10,172 guarded stage-audit jobs pass, including eleven new
explicit theorem audits with only approved axioms. The rebuild peaks at 24.9 GiB
combined across concurrent processes. All eight new modules and the revised
counted-loop module pass individual guarded checks, each at most 1945.3 MiB.
Source-integrity, plan-status and whitespace checks pass.


### S3 restoring source-line handoff and solver-input feed

`stageCouplingLines_exec` generates the ambient symbol count from ordinary
axis-size/width headers, copies the retained original RHS from port 110 to the
row RHS port, and copies the published solution from port 132 above the original
RHS on port 110. Both source lines and arbitrary suffixes survive. Its paid cost
is at most `26*s*w+9*s+26`. `retireCouplingLine_exec` removes the owned source
copy after the row pass, for at most `12*s*w+9*s+12`, restoring the original RHS.
All count/copy scratch is generated and released.

`borrowedCouplingPass_exec` composes those adapters with the initialized ambient
row pass. Only the result prefix on port 113 changes. Original RHS, published
solution, suffixes, geometry, precision, outer parameters and all other stacks
restore. `borrowedCouplingPass_spec` derives word fits and carries exact output
volume and uniform original-matrix error through this actual handoff.

`couplingRowWords_eq_chirpLine` identifies the generated stream with the encoded
ambient integer field `couplingRowField`. `couplingRowField_norm` bounds that
field by `2^couplingRowExponent`, giving a numerical input budget for subsequent
stages without assuming a result magnitude or prepared output field.

`feedCouplingResult_exec` moves the owned result prefix to port 110 without
changing its symbol order and restores the previous output suffix. The composed
`feedCouplingPass_spec` leaves that exact encoded ambient field above the
retained original RHS and preserves the published solution on port 132. Its
norm and uniform error are proved for the same executed result. Relative to
`runCouplingRowsCost`, the complete borrow/run/release/feed adapter adds at most
`50*s*w+27*s+50` steps.

These contracts require the published source line to have its stated integer
encoding. Deriving that representation from the interior solver's returned
physical blocks, transitioning ordinary runtime headers between stages, the
prepared S5 boundary handoff and final interior/complex-line assembly remain
open. Repeated source scans are still paid; uniform fast time and simultaneous
storage remain unproved. S3 remains partial and kappa is unchanged.

Validation: all 10,179 guarded stage-audit jobs pass, including nine new explicit
theorem audits using only approved axioms. Combined build peak is 4.3 GiB. All
seven new modules and the revised readiness module pass individual guarded
checks at at most 1945.8 MiB. Source-integrity, plan-status and whitespace
checks pass.


### S3 encoded interior output and executed coupling-header transition

The closed batch execution already writes exact `cstream` data. `EncodedStream`
now retains that integer-word witness through the clipped-group, protected-call,
conditional-class and decoded-key contracts. The natural-group interfaces keep
their existing byte-prefix contracts by forgetting this extra witness.

`cstream_take`/`cstream_drop`, `scatterRows_cstream` and the scaled-gap lemmas
prove structurally that aligned publication preserves the word encoding.
Borrowed source suffixes are excluded using the actual row count. The complete
halo key loop and initialized interior theorem now retain encoding preservation
from the existing encoded ambient output line. This changes no numerical
program, source movement, runtime count or error ledger.

`solveHaloInterior_encoded_spec` therefore returns an ambient integer field `D`
whose encoded line is exactly the actual published output. Its decoded physical
core-error guarantee and all restoration/cost properties are unchanged. The
input output-prefix remains a real pre-existing encoded line; no free zero
page or supplied format fact about the computed result is assumed.

`installCouplingHeaders_exec` reconstructs only the required coupling headers
from retained outer masters, including halo endpoints, and generates the word
width `2*q+8`. The original RHS, published line, outer masters and scratch
survive. Its paid cost is `4*P+12*q+4*(s+t+u+band+a+b)+42`.
`interiorForCoupling_spec` executes the actual halo-interior solver followed by
this header reconstruction and proves the resulting `CouplingReady` bank, exact
encoded published field and original physical core accuracy. The word width
matches the existing execution width algebraically.

The interior result is now connected at the byte-format and runtime-header
level. Deriving the reusable magnitude/normalized-value handoff for the returned
integer field, composing the S5 prepared boundary operation and recovery/final
interior solve, and full complex-line assembly remain open. Repeated source
scans and the uniform fast-time/simultaneous-storage bounds remain unresolved.
S3 remains partial and kappa is unchanged.

Validation: all 10,186 guarded stage-audit jobs pass, including thirteen new
explicit theorem audits with only approved axioms. The successful audit build
peaks at 2.7 GiB combined. All twenty-four new/revised Lean modules, including
the audit root, pass individual guarded checks at at most 2028.4 MiB.
Source-integrity, plan-status and whitespace checks pass.


### S3 bounded interior output and executed interior-to-residual composition

`publishedOutputWords_norm` bounds the actual published integer numerators by
`2^interiorOutputExponent`, where the exponent is
`executionExponent(p,l,target,rhsExp)+2*l+4`. The proof follows the existing
scalar product, exact rescaling, generated similarity weight and publication
permutation; it does not assume a result norm. The bound is independent of the
current cell length and number of cells.

`BoundedEncodedStream` carries the same actual byte prefix with an integer-word
witness and its normalized magnitude bound. The closed batch, clipped group,
protected class and counted key loop preserve that witness. Aligned scattering
inherits the common bound from the old ambient line and the new computed words.
`interiorOutput_width` proves that the existing execution width covers those
numerators. `encodedRange_ambient` and `publishedCellRead_encodedField` therefore
identify the returned ambient field's normalized values with its physical
reads exactly, rather than only proving that some word list encodes the bytes.

`solveHaloInterior_bounded_spec` returns that bounded field and the existing
core-error contract directly for its normalized values. The pre-existing
ambient output field has an explicit initial magnitude bound; the computed
result has none supplied. `interiorForCoupling_spec` now carries this numerical
handoff through the executed header reconstruction.

`interiorResidual_spec` executes the interior solve, reconstructs its coupling
runtime, borrows both actual lines, computes every residual row and feeds the
residual above the retained original RHS. It preserves the solved interior
line on port 132 and restores all other borrowed payloads and suffixes. The
residual is an exact encoded integer field with a derived norm bound. Its error
against the original `b-A_BI*x` expression is at most
`L*2/2^q + L*2^e/2^q + K/2^target`, with `L=2*band+1` and the derived interior
exponent `e`. There is no supplied magnitude, format or approximation hypothesis
about the executed interior result. The cost is the sum of the two existing
executed stage bounds.

The support-count, row-width and original coefficient row-mass budgets remain
explicit. Closing those budgets uniformly in the final parameter regime, the
S5 prepared-boundary operation, recovery/final-interior composition and full
complex-line assembly remain open. The current magnitude estimate is coarse;
complete shared-precision closure and uniform fast time/simultaneous storage
are still unproved. S3 remains partial and kappa is unchanged.

Encoding-only wrappers were superseded and removed; restore from `4e78d06f`.

Validation: all 10,189 guarded stage-audit jobs pass, including fifteen new
explicit theorem audits with only approved axioms. Combined build peak is
7.7 GiB. All twenty-four new/revised Lean modules, including the audit root,
pass individual guarded checks at at most 2029.2 MiB. Source-integrity,
plan-status and whitespace checks pass.


### S3 owned output initialization and restored residual endpoint

`initializeInteriorOutput_exec` generates the physical line length from the
retained precision/ambient-size masters, copies the actual RHS above the old
output suffix, and releases the count and width workspace. Its cost is at most
`16*s*(2*q+8)+9*s+12*q+44`; the original input and every other stack are restored.
`rhsExponent_le_interiorOutputExponent` derives the initial output magnitude
from the existing RHS bound. No pre-existing encoded output field is required
by `initializedInteriorResidual_spec`.

`releaseCouplingHeaders_exec` releases exactly the nine private headers installed
by the interior-to-coupling transition. It restores the original empty runtime
slots and retains every master and payload, at exact cost
`2*(P+3*q+s+t+u+band+a+b)+35`.
`restoredInteriorResidual_spec` composes initialization, interior solving,
residual formation and header release. The only final changes are the solved
interior prefix on 132 and the residual prefix above the retained original RHS
on 110; both old suffixes are preserved. The residual endpoints also retain the
derived interior magnitude and core-approximation facts needed by recovery,
alongside the residual magnitude/error bounds. The reusable output frame lemma
replaces the duplicate register proof in `interiorForCoupling_spec`.

This closes output allocation and private coupling-header release for the first
interior/residual transition. It does not implement prepared S5 setup/solve,
recovery/final-interior or complex assembly. Shared precision, final support and
row-mass budgets, repeated-scan fast time and simultaneous machine storage
remain open. S3 remains partial and kappa is unchanged.

Validation: all 10,193 guarded stage-audit jobs pass, including six new
explicit theorem audits with only approved axioms. Combined build peak is
17.8 GiB. All nine new/revised Lean modules, including the audit root, pass
individual guarded checks at at most 2032.8 MiB. Added-source integrity,
plan-status and whitespace checks pass.


### S3 real residual projection and precision-independent magnitudes

`realPrefix_exec` executes real projection by a counted transfer and mapped move.
It preserves the prefix order, the borrowed suffix, the counter and both scratch
stacks, at exact cost `6*prefix.length+6`. The pair-symbol map is proved to encode
`realPartWord`, so it removes only imaginary components without changing the
normalized real values. `realResidualProjection_exec` generates the common
ambient byte count from retained masters, projects both owned interior/residual
prefixes and releases all its runtime slots. Its cost is at most
`18*s*(2*q+8)+9*s+12*q+46`.

`couplingRowField_realPart` proves that this projection commutes with the exact
truncated row arithmetic, including masked input selection, because all selected
coefficients are real. `stableInterior_norm` combines the actual core-error
contract with diagonal dominance to bound the projected interior on its active
set by `2^(rhsExp+8*p+1)`. Unlike the earlier coarse bound, this exponent contains
neither the requested target accuracy nor the arithmetic precision.

`realInteriorResidual_spec` composes the restored interior/residual caller and
both actual projections. It derives matrix dominance from the existing full
ambient hypotheses (`2 ≤ p`, `8*p ≤ 2^u`, positive α and relative gap at least
`1/(4*p)`); it does not assume a bound on the computed output. Its two returned
prefixes are real integer fields. The interior magnitude is bounded on the
active interior; the residual has the uniform bound
`2^couplingRowExponent(rhsExp, rhsExp+8*p+1, 8*p+1, countExp)`. Both are independent
of arithmetic precision. The residual error now uses that sharper interior
exponent as well. `couplingRowField_error` factors exact decoding from the
integer-field error, avoiding repeated expansion of the computed row expression.

The storage-width premise is derived by `interiorResidual_width` from
`countExp ≤ executionExponent`; the support-count and original coefficient
row-mass budgets remain explicit. This removes the coarse output-magnitude
obstruction to recovery sizing. It does not close the complete shared precision
allocation, implement S5 setup/solve or compose recovery/final-interior and
complex assembly. Repeated full-source scans and uniform fast time/simultaneous
machine storage remain open. S3 remains partial and kappa is unchanged.

Validation: all 10,200 guarded stage-audit jobs pass, including sixteen new
explicit theorem audits with only approved axioms. Combined build peak is
2.7 GiB. All eight new/revised Lean modules, including the audit root, pass
individual guarded checks at at most 2034.1 MiB. Added-source integrity,
plan-status and whitespace checks pass; proof limits are unchanged.


### S3 executed recovery and second interior pass at shared precision

`restoredCouplingPass_spec` now runs either coupling branch from the retained
ordinary master bank. It installs its own private headers, borrows the actual
encoded solution and RHS, computes the full row pass, feeds its output and
releases those headers. The source prefix alone changes; the returned
`LengthKeyReady` invariant applies to the computed line. Its magnitude and
original-matrix error follow from the computed input contracts. The source frame
lemma and `couplingHeadersR_update` factor register arguments; the latter also
replaces the earlier nine-case frame proof in `restoredInteriorResidual_spec`.

`initializedInterior_spec` allocates its ambient output by copying the actual
input before solving; no pre-existing output field is supplied.
`retireAmbientSource_exec` consumes the owned ambient residual prefix to expose
the retained original RHS, preserving all other stacks and private scratch. Its
cost is at most `12*s*(2*q+8)+9*s+12*q+40`.

`recoveryRhsExponent` is the derived coupling exponent for the supplied boundary
magnitude. `recoveryFirstTarget` reserves that magnitude increase in the first
interior pass's accuracy allocation. `recovery_execution_sizes` proves exact
equality of the first/recovery arithmetic precision, stage precision and storage
width; no conversion or regenerated precision bank is assumed. The recovery
row width follows from this common sizing, without an extra fit premise.

`recoveryInterior_spec` composes paid residual retirement, boundary coupling,
header release, fresh output allocation and the second interior solve. It
preserves the original RHS beneath the recovery line and the boundary solution
beneath the new interior line. An exact reference solution of the computed
recovery system is obtained from dominance inside the proof. The theorem takes
only the exact halo target and the computed boundary magnitude/error contract;
it does not request a supplied recovery solution or arithmetic execution oracle.

`SchurDominance.recovery_solves_error` proves the recovery RHS perturbation costs
at most the inverse margin. Thus the executed interior error against the same
exact halo solution is at most `2^-target + 8*p*recoveryError`, where
`recoveryError = (2*band+1)*(2/2^q) +
 (2*band+1)*(2^boundaryExp/2^q) + K*boundaryError`.
The retained boundary values and computed interior values also have an explicit
uniform halo error `max(interiorError,boundaryError)` through `ErrorOn.union_ite`;
this is a numerical selection contract, not an executed final publication.

The S5 prepared setup/solve/release operation still has to produce the admitted
boundary line and its proved magnitude/error contract. Physical final-line
assembly, complex pairing, complete error allocation, automatic support/row-mass
budgets and uniform fast time/simultaneous storage remain open. In particular,
repeated full-source scans are still charged. S3 remains partial and kappa is
unchanged.

Validation: all 10,208 guarded stage-audit jobs pass, including eleven new
explicit theorem audits with only approved axioms. Combined build peak is
22.4 GiB. All eleven new/revised Lean modules, including the audit root, pass
individual guarded checks at at most 2036.8 MiB. Added-source integrity,
plan-status and whitespace checks pass; proof limits are unchanged.

### S3 physical publication of the recovered real halo

The publication program generates the interior membership mask from the halo
headers, splits the retained interior and boundary pages, and selects their words
in a single sequential scan. It projects the selected words to their real parts,
preserves the original suffix and releases its private headers and scratch.
`publishHalo_exec` proves the resulting physical stack and its explicit cost.

`publishedHalo_accuracy` connects the decoded published words to the numerical
halo error. `recoveryPublishedHalo_spec` composes this publication with the
executed recovery and second interior pass at their shared precision. The
published real line has the maximum of the boundary error and the proved recovery
interior error, and the original right-hand side remains retained.

S3 remains partial: the S5 boundary producer and its error contract, complex
assembly, complete error allocation, automatic support and row-mass budgets,
uniform fast time and simultaneous storage still need proofs. The publication
mask currently uses the existing coefficient-width workspace; a smaller geometry
workspace remains an optimization to establish before a fast-time bound.

Validation: all 10,221 guarded stage-audit jobs pass, including 22 new
explicit theorem audits with only approved axioms. Combined build peak is
33.9 GiB. All 15 new/revised Lean modules, including the audit root, pass
individual guarded checks at at most 2040.8 MiB. Added-source integrity,
plan-status and whitespace checks pass; proof limits are unchanged.


### S3 geometry-sized publication workspace

`generatePublicationWidth` now derives the mask workspace from the bit lengths
of the period and bandwidth. `publicationGeometryWidth_fits` proves it is wide
enough for the halo membership arithmetic. The generator scans the two unary
headers twice and restores them; it no longer depends on coefficient precision.

The closed mask execution uses this generated workspace and still releases all
private scratch. `closedPublicationMaskCost_halo_le` bounds its complete cost by
`4000*(5*t+1)*(4*Nat.size t+11)^2` for a halo inside an axis of length at most
`t`. This closes the publication-mask part of the cost ledger; it does not
establish the remaining uniform fast-time or simultaneous-storage bounds.

Validation: all 10,222 guarded stage-audit jobs pass, including four new
explicit theorem audits with only approved axioms. Combined build peak is
2.7 GiB. All five new/revised Lean modules, including the audit root, pass
individual guarded checks at at most 2038.0 MiB. Added-source integrity,
plan-status and whitespace checks pass; proof limits are unchanged.

### S3 executed pairing of real component lines

`pairComponentLines` generates a byte clock from the retained axis length and
word width, consumes two aligned real-component streams and publishes their
complex pairing in natural order. It preserves the borrowed suffix on each
source, restores its clock and scratch, and has cost at most
`10*s*w+9*s+8`. The structural symbol pass and encoding lemmas apply to arbitrary
lists, before instantiating the ambient-coordinate lines.

`pairComponentLines_spec` connects that actual execution to the decoded complex
output. Two component errors combine additively once, with no axis-length or
window-count factor; word-fit and accuracy hypotheses are required only on the
active coordinates. This supplies the final pairing operation. Running both real
solves from the original complex input, the S5 boundary producer, complete error
allocation and uniform time/simultaneous storage remain open. S3 remains partial.

Validation: all 10,226 guarded stage-audit jobs pass, including 13 new
explicit theorem audits with only approved axioms. Combined build peak is
2.7 GiB. All five new/revised Lean modules, including the audit root, pass
individual guarded checks at at most 2041.9 MiB. Added-source integrity,
plan-status and whitespace checks pass; proof limits are unchanged.

### S3 generated real-component inputs from the original complex RHS

`splitComponentPrefix_exec` consumes the complex input prefix once, copies its
imaginary component and restores its real component in natural order. Both
borrowed suffixes and all counters/scratch are preserved. The fixed outer caller
`splitComponentLine` generates and retires its own byte count from the retained
axis and width headers, with cost at most `16*s*w+9*s+16`.

`splitComponentLine_spec` connects the executed output tapes to exact real and
imaginary RHS values. Both component magnitudes are bounded by the original
complex magnitude, and their word fits follow from the original RHS budget;
component extraction incurs no arithmetic error or extra precision allowance.
`pairComponentWord_parts` proves that pairing the two extracted words recovers
the original word.

The inactive component must still be retained outside the real solver's scratch
bank while each complete real solve runs. That two-solve composition, the S5
boundary producer, final error allocation and uniform fast time/simultaneous
storage remain open. S3 remains partial.

Validation: all 10,229 guarded stage-audit jobs pass, including 12 new
explicit theorem audits with only approved axioms. Combined build peak is
2.7 GiB. All four new/revised Lean modules, including the audit root, pass
individual guarded checks at at most 2042.0 MiB. Added-source integrity,
plan-status and whitespace checks pass; proof limits are unchanged.

### S3 retained component workspace and solver-bank restoration

A fixed 148-register component controller now embeds the existing 144-register
real solver and keeps four registers outside its image. The embedding preserves
those outer registers at every executed solver endpoint. The two-port transport
lemma carries the real solver's exact source/output frame without adding steps.

`preparedComponentInputs_exec` reconstructs the private word-width header from
the retained precision, executes the complex-input split, parks the imaginary
RHS outside the real solver bank, and releases the private header. Its cost is
at most `retainedComponentInputsCost s (2*q+8)+12*q+27`; the retained splitter
cost is at most `20*s*w+9*s+20`. The returned low bank satisfies the original
`LengthKeyReady` invariant for the exact real RHS, including empty scratch.
The parked component's borrowed suffix and every other outer register survive.

`retainedRecoveryPublishedHalo_spec` runs the existing recovery and final real
publication inside this bank with its original numerical/error contracts and
unchanged cost, preserving the parked component registers. The complete
sequence still needs the S5 boundary producer and the transition that retires
owned source prefixes, saves the first output and installs the second input.
Full two-component solve composition, global error allocation and uniform fast
time/simultaneous storage remain open. S3 remains partial.

Validation: all 10,234 guarded stage-audit jobs pass, including eight new
explicit theorem audits with only approved axioms. Combined build peak is
2.7 GiB. All six new/revised Lean modules, including the audit root, pass
individual guarded checks at at most 2041.3 MiB. Added-source integrity,
plan-status and whitespace checks pass; proof limits are unchanged.

### S3 executed transition to the second component solve

`movePrefix_exec` relocates an owned prefix in natural order and preserves both
borrowed suffixes. `componentTransitionCore_exec` uses it to retire the recovery
RHS and original RHS pages, save the first published line in an outer register,
and install only the owned second-input prefix. The source, output and parked
input suffixes are preserved, and all relocation scratch restores.

`componentTransition_exec` reconstructs its word width from retained precision,
generates the byte clock, runs the transition and releases both private counters.
Its cost is at most `30*s*(2*q+8)+9*s+12*q+58`.
`componentTransition_spec` proves the resulting low bank satisfies
`LengthKeyReady` for the second input and the restored output suffix.

`retainedRecoveryTransition_spec` composes the actual retained recovery and
publication program with that transition. The first result's numerical error is
proved on the physical saved-output register, and the returned bank is ready to
run the second real solve. Moving the encoded result changes no numerical error.
The S5 boundary producer, composition of the complete second solve and final
pairing/release, complete error allocation and uniform fast time/simultaneous
storage remain open. S3 remains partial.

Validation: all 10,239 guarded stage-audit jobs pass, including six new
explicit theorem audits with only approved axioms. Combined build peak is
2.7 GiB. All seven new/revised Lean modules, including the audit root, pass
individual guarded checks at at most 2045.1 MiB. Added-source integrity,
plan-status and whitespace checks pass; proof limits are unchanged.

### S3 final complex pairing and owned-source release

`finishComponents` reconstructs the word width, generates and copies its byte
clock, retires the second solve's recovery/original RHS pages, pairs the saved
real line with the current imaginary line, moves the complex result to the output
port and releases both private counters. Its cost is at most
`34*s*(2*q+8)+9*s+12*q+60`. Both output/saved-page borrowed suffixes are
preserved, the source returns to its borrowed suffix, and all pairing scratch
and the copied outer clock restore.

`pairedCellRead_parts` proves directly that decoding the paired physical word
returns the two physical component reads. Thus
`pairedComponents_physical_accuracy` needs no additional integer-fit premise;
the two established physical errors add once.
`finishComponents_spec` combines this accuracy with actual execution and a
returned `LengthKeyReady` invariant for the released source.

`retainedRecoveryFinish_spec` composes the second retained recovery/publication
call with this finalizer. It consumes the saved first result, publishes the
complex line on the actual output port and carries its combined uniform halo
error, restored source ownership and solver readiness. The complete initial-pass
and S5 boundary execution for each component, full sequence composition, global
error allocation and uniform fast time/simultaneous storage remain open. S3
remains partial.

Validation: all 10,245 guarded stage-audit jobs pass, including seven new
explicit theorem audits with only approved axioms. Combined build peak is
2.7 GiB. All seven new/revised Lean modules, including the audit root, pass
individual guarded checks at at most 2043.6 MiB. Added-source integrity,
plan-status and whitespace checks pass; proof limits are unchanged.

### S3 automatic coupling mass and support-count budgets

`couplingOffsets_mass_eq_row` identifies the absolute mass of the actual reversed
signed-offset list with the original matrix row sum. Positivity permits this
identity while retaining every periodic alias. The selected rounded-operator
bound then proves `couplingOffsets_mass_le_two`, uniformly in the ambient row
and independently of halo size. No local/full-line cardinality substitution is
used.

`couplingCountExponent` is the binary size of `2*PhaseCellBand.width p u+1`.
Its support-count bound is automatic; its exponent is at most `8*p+3` and fits
`executionExponent` for every admitted initial target/RHS budget. The generated
offset lists and runtime counters already have this count.

The executed initial real residual, recovery, real publication, retained
transition and final complex-publication theorems now select this exponent
internally and use the proved mass bound 2. Their interfaces no longer require
a caller-supplied mass constant, mass proof, count exponent, support-count bound
or count-precision bound. The residual's propagated interior error is charged
with factor 2, and recovery's boundary-error contribution is `2*boundaryError`.

These support/mass budget obligations are closed. Prepared S5 boundary execution,
complete sequence composition, final error allocation and uniform fast
time/simultaneous storage remain open. S3 remains partial.

Validation: all 10,247 guarded stage-audit jobs pass, including six new
explicit theorem audits with only approved axioms. Combined build peak is
2.7 GiB. All nine new/revised Lean modules, including the audit root, pass
individual guarded checks at at most 2039.6 MiB. Added-source integrity,
plan-status and whitespace checks pass; proof limits are unchanged.

### S3 allocated dyadic recovery and complex-publication errors

`recoveryGuardBits p = Nat.size (8*p)+3` pays the complete inverse-margin
amplification of coupling roundoff and boundary error. `recoveryTarget` adds
these guard bits to the requested output target. `couplingRoundoff_budget`
prices all generated offsets and the boundary magnitude; the existing shared
execution precision automatically satisfies its bit requirement.

`selected_recovery_error_budget` proves the complete published halo error,
including the boundary/interior maximum, is at most `2^-target` whenever S5's
boundary error is at most `2^-(recoveryTarget p target)`. The boundary magnitude
is still the stated computed-input budget. The executed
`recoveryPublishedHalo_tolerance` theorem instantiates this allocation and
retains its exact source/output frame and paid cost.

The retained recovery and transition interfaces now expose the requested dyadic
error directly. The final complex recovery/publication interface reserves half
the final allowance for each physical component and proves the resulting complex
output error is at most `2^-target`; it no longer returns an unallocated sum of
component errors. Its precision and cost explicitly use that tighter allocation.

Recovery/publication and final pairing error allocation are closed under the
stated S5 boundary contract. S5's computed-Schur stability/precision and actual
boundary execution, complete initial-pass/full-sequence composition, and uniform
fast time/simultaneous storage remain open. S3 remains partial.

Validation: all 10,249 guarded stage-audit jobs pass, including six new
explicit theorem audits with only approved axioms. Combined build peak is
2.7 GiB. All six new/revised Lean modules, including the audit root, pass
individual guarded checks at at most 2042.5 MiB. Added-source integrity,
plan-status and whitespace checks pass; proof limits are unchanged.

### S3 executed initial Schur RHS and local backward-error handoff

`retainedSchurResidual_spec` now executes the initial real interior/residual pass
inside the component controller. Its proof constructs an exact interior
reference solver from dominance; the caller supplies no reference solution or
solver. The returned integer residual is real, has the derived dyadic magnitude
bound, decodes exactly from the actual source tape and approximates the exact
Schur RHS with the proved coupling/interior error. The source retains the
original RHS underneath, the interior output is retained, the outer component
registers survive and the low bank returns `LengthKeyReady`.

`stableInteriorResidual_width` factors the common width proof, now reused by the
initial numerical proof and physical residual decoding.

`halo_schur_stageInv` proves margin `1/(8*p)` and row mass at most 2 for the
Schur matrix of the actual clipped halo, using its generated interior and
boundary sets. It keeps the original ambient matrix and its global phases;
no full-line boundary-cardinality or bandwidth bound is reused as a halo bound.

`computed_schur_error` and `halo_computed_schur_error` convert a computed boundary
matrix's row perturbation `εA`, backward residual `δ` and supplied RHS error `E`
into forward boundary error. They derive the candidate magnitude
`(ρ+δ)/(μ-εA)` and error `(δ+εA*(ρ+δ)/(μ-εA)+E)/μ` for `εA<μ`.
This provides the numerical S3–S5 handoff on the actual residual. S5 still has to
construct its table, prove these perturbation/backward-error contracts and
execute setup/solve/release, including retirement of owned interior output.
Complete sequence composition and uniform fast time/simultaneous storage remain
open. S3 remains partial.

Validation: all 10,252 guarded stage-audit jobs pass, including seven new
explicit theorem audits with only approved axioms. Combined build peak is
2.7 GiB. All six new/revised Lean modules, including the audit root, pass
individual guarded checks at at most 2043.0 MiB. Added-source integrity,
plan-status and whitespace checks pass; proof limits are unchanged.

### S3 canonical boundary magnitude and allocated initial residual

`stableSolve_norm` factors the inverse-margin magnitude argument for a published
core inside any solved principal system. The existing interior bound reuses it;
`haloBoundary_norm` applies it to the actual halo solution and boundary subset.
A real boundary result within unit error is bounded by
`2^(rhsExp+8*p+1)`. The closed recovery/tolerance and retained-controller
interfaces now derive this magnitude from the proved boundary error and the
original RHS bound. They require the structural real-output contract instead
of a supplied boundary magnitude exponent/bound.

With that canonical magnitude, `recoveryFirstTarget_canonical` identifies the
shared initial target as `recoveryTarget + couplingCountExponent + 16*p + 3`.
`initialResidual_roundoff_budget` pays all offset roundoff at the existing
working precision. `initialResidual_error_budget` proves that the initial
residual error, including its interior contribution and subsequent inverse
margin amplification by `8*p`, costs at most one quarter of the boundary-error
allowance.

`retainedSchurResidual_spec` now selects this same canonical initial target and
carries the amplified quarter-budget bound on its computed Schur RHS, together
with exact physical decoding, magnitude and readiness. The remaining boundary
allowance is available for S5's computed-matrix and solve errors; those still
require proved setup/solve precision and executed construction. Complete
sequence composition and uniform fast time/simultaneous storage remain open.
S3 remains partial.

Validation: all 10,254 guarded stage-audit jobs pass, including five new
explicit theorem audits with only approved axioms. Combined build peak is
2.7 GiB. All nine new/revised Lean modules, including the audit root, pass
individual guarded checks at at most 2042.9 MiB. Added-source integrity,
plan-status and whitespace checks pass; proof limits are unchanged.

### S3 complex-input initial pass and computed-boundary tolerances

`preparedSchurResidual_spec` now composes the executed complex-input split,
parking of the imaginary RHS and the retained initial real interior/residual
pass. It starts from the original complex line and returns the allocated
physical Schur-RHS handoff with the original real RHS beneath it, the imaginary
RHS preserved outside scratch, interior output retained and readiness restored.
Its cost is the proved preparation cost plus the actual initial-pass cost; no
component input, exact interior solution or execution is supplied by the caller.

`boundaryErrorBits p target rhsExp` selects the row-perturbation/backward-residual
allowance from the requested tolerance, inverse-margin bits and actual Schur-RHS
magnitude. `boundary_error_budget` proves this allocation keeps the computed
Schur system dominant and pays its matrix/solve error together with the initial
quarter-budget.

`boundaryTableBits` additionally pays the bit length of the actual boundary
cardinality. `boundaryTable_error_budget` and `boundaryTable_row_budget` turn
per-entry table error into the required row error. `haloBoundary_tolerance`
combines those proved allocations with local Schur stability to give the exact
forward boundary tolerance required by recovery. Its boundary count is the
actual halo set, with no substituted full-line cardinality bound.

These are executable initial-pass composition and numerical boundary acceptance
proofs. S5's table construction, per-entry accuracy and bounded solve still
require executed implementations; full sequence composition and uniform fast
time/simultaneous storage also remain open. S3 remains partial.

The complete caller must also restore its borrowed original complex input; the
current component controller consumes explicitly owned private prefixes. That
ownership/restoration composition remains part of the full-sequence obligation.

Validation: all 10,257 guarded stage-audit jobs pass, including five new
explicit theorem audits with only approved axioms. Combined build peak is
2.7 GiB. All four new/revised Lean modules, including the audit root, pass
individual guarded checks at at most 2043.6 MiB. Added-source integrity,
plan-status and whitespace checks pass; proof limits are unchanged.

### S3 preserved original-input prefix

The complex finalizer now uses released low-bank register 140 for its copied
clock. Its readiness contract already proves this register empty, so callers no
longer need an empty register 146. The complete retained recovery/finalization
execution preserves arbitrary contents of 146 without increasing the register
bank or the existing time bound.

`saveOriginalPrefix_exec` copies the original complex input from 110 to 146
above its borrowed suffix, preserving the complete projected real-solver bank.
`restoreOriginalPrefix_exec` restores the original input above its borrowed
suffix and releases the saved prefix. Their exact costs are 10 bytes+10 and
6 bytes+6, respectively. `originalPrefix_roundTrip` composes the two operations
around an arbitrary executed owned-input computation, preserving its other
results and restoring both borrowed suffixes. This uses structural prefix
lemmas rather than new concrete checks.

The caller still needs to generate and clear the byte clock around these
operations and compose them around the actual complete two-pass sequence.
S5's executed table/solve, initial-interior retirement, uniform fast time and
simultaneous storage remain open; S3 remains partial.

Validation: all 10,258 guarded stage-audit jobs pass, including four new
explicit theorem audits with only approved axioms. Combined build peak is
2.7 GiB. All seven new/revised Lean modules pass individual guarded checks,
with a maximum of 2042.4 MiB. Added-source integrity, plan-status and whitespace
checks pass; proof limits are unchanged.

### S3 original-input preservation in the executed caller endpoints

`originalInputClock_exec` constructs the byte count from the retained precision
and line-length masters. `saveOriginalInput` and `restoreOriginalInput` generate
that clock, execute the counted prefix operation, and clear both temporary
counters. For width `w = 2*q+8`, their proved costs are respectively
`16*s*w+9*s+12*q+44` and `12*s*w+9*s+12*q+40`. Their readiness lemmas obtain all
low scratch conditions from `LengthKeyReady`, and restore the released bank.
Neither operation requires an externally supplied byte clock or empty backup
suffix.

The actual `preparedSchurResidual` now saves the original complex line on 146
before splitting its real and imaginary inputs and executing the initial real
Schur pass. Its execution, numerical error and physical-read contracts include
this saved prefix, and its cost pays the complete save program.

`retainedRecoveryFinish` now runs second recovery and complex finalization,
then restores the saved original line above its borrowed input suffix and
releases the backup prefix. Its execution contract preserves the complex output
and its requested dyadic accuracy, restores both borrowed suffixes and solver
readiness, and pays the complete restore cost. The former owned-input endpoint
is the explicit `retainedRecoveryFinishCore` used in this composition.

These are actual beginning/end caller compositions. The middle sequence still
requires S5's executed computed-table/solve and initial-interior retirement.
The saved complex prefix occupies an additional `s*w` retained symbols; its
simultaneous storage charge must be included in the outstanding global stock
proof. Uniform fast time and the complete two-pass/SolveSpec endpoint remain
open. S3 remains partial.

Validation: all 10,260 guarded stage-audit jobs pass, including the generated
clock, two complete prefix operations, two readiness lemmas and the owned-input
core audit. Combined build peak is 4.4 GiB. All five new/revised Lean modules
pass individual guarded checks at at most 2044.2 MiB. Added-source integrity,
plan-status and whitespace checks pass; proof limits are unchanged.

### S3 release of the initial interior result

`retireInitialInterior` generates the byte clock from the retained masters,
consumes exactly the owned line prefix on output port 132, and clears its two
counter stacks. It preserves the borrowed output suffix and every other stack,
including the computed residual, parked imaginary input, saved real component
and saved original complex input. Its proved cost is
`12*s*(2*q+8)+9*s+12*q+40`; no input-size counter is supplied for free.

`retireInitialInterior_ready` derives the scratch preconditions from the released
solver bank and restores readiness for the unchanged residual source. The actual
`preparedSchurResidual` now executes this retirement immediately after computing
the initial residual. Its exact final state restores output 132 to its original
borrowed suffix, while preserving all residual accuracy, magnitude and physical
read contracts and the saved complex/imaginary inputs. Its cost includes the
complete generated retirement program. The initial interior field remains an
existential mathematical witness used to describe the already-computed residual;
its physical stream is no longer retained across the boundary solve.

This closes initial-interior ownership release at the first complex-input
endpoint. S5 still needs executed computed-table setup and solve; complete
second-component sequence composition, scaling/final rounding and uniform fast
time/simultaneous storage remain open. S3 remains partial.

Validation: all 10,262 guarded stage-audit jobs pass, with explicit audits for
retirement execution and readiness. Combined build peak is 2.7 GiB. All four
new/revised Lean modules pass individual guarded checks at at most 2044.7 MiB.
Added-source integrity, plan-status and whitespace checks pass; proof limits
are unchanged.

### S3 executed transition through the second Schur RHS

`releasedSchurResidual` composes the actual retained initial interior/residual
pass with generated retirement of its temporary interior stream. It returns
only the computed residual above the original RHS on 110, restoring 132 and
all spectator banks exactly. Its numerical contract constructs the interior
reference solve internally, derives the residual magnitude and realness,
provides its amplified quarter-error bound on the actual halo boundary, and
identifies its physical read. Its cost pays both executed programs.

The first complex-input `preparedSchurResidual` now uses this shared caller,
removing its duplicate retirement composition with the same exact state and
cost. This is also the initial-pass caller for the second component.

`secondComponentSchur` executes first recovery/publication, saves its real result
on 145, retires the first component's owned RHS prefixes, moves the parked
second RHS from 144 to 110, and executes the released initial Schur pass on that
second RHS. Its single execution theorem supplies both the saved first-result
accuracy and the second residual's magnitude, realness, amplified boundary
error, actual physical read and solver readiness. Its exact state restores
132 to its borrowed suffix, releases the parked prefix on 144, and preserves
the saved original input on 146. It accepts encoded parked input with a proved
magnitude, rather than a supplied second interior solution, residual or
execution. The theorem works at the common allocated precision; the final
complex caller instantiates the component target one bit above its requested
output target.

This closes the executed first-recovery-to-second-initial-pass composition.
The remaining boundary results must still come from S5's executed computed
Schur table/setup/solve, with paid release and support/precision/storage proofs.
The complete two-boundary-call composition, scaling/final rounding, uniform
fast time and simultaneous storage remain open. S3 remains partial.

Validation: all 10,264 guarded stage-audit jobs pass, including explicit audits
of the released initial pass and the composed second-component execution.
Combined build peak is 4.3 GiB. All four new/revised Lean modules pass individual
guarded checks at at most 2046.5 MiB. Added-source integrity, plan-status and
whitespace checks pass; proof limits are unchanged.

### Local boundary support and rounded fill for the S3–S5 handoff

`halo_same_cell_interval` proves that a single ambient phase cell contains at
most `6*w` local boundary vertices between any two of its coordinates: the
existing ambient-boundary count contributes at most `4*w`, and the two
artificial endpoint guard bands contribute at most `2*w`. It uses the actual
`haloBoundary`, retaining ambient phases and periodic cuts. Empty/clipped
halos require no extra assumptions.

`halo_schur_cycRel` applies the existing elimination-support theorem to the
actual halo principal subsystem and its generated interior set. Every
eliminated coordinate is proved to be an ambient interior coordinate. It yields
a cyclic boundary-rank band of half-width `6*w`; folding the actual halo
boundary gives half-width `12*w+1` in `halo_schur_foldBRel`. This is a local
support theorem with charged artificial cuts, rather than a relabeled full-line
boundary result.

`bandBoundaryTable` masks an approximated boundary matrix to this proved folded
band. `bandBoundaryTable_error` proves that masking adds no entry error whenever
the target matrix has the proved support. `haloBoundaryTable_entry_error`
instantiates this for the exact local Schur matrix and the allocated entry
precision, so the masked table can use the existing boundary-tolerance handoff.
`bandBoundaryTable_factors` proves that zero-preserving rounded elimination
retains the band and its triangular order. `foldBRel_row_card` and
`bandBoundaryTable_factor_rows` bound supported entries per table/factor row by
`2*W+1`, hence `24*w+3` at the local width, independently of boundary cardinality.

These are support, numerical masking and rounded-fill proofs. They do not
construct table entries, folded coordinate maps or factor pages on tape.
Executed computed-Schur setup/solve/release, its precision and simultaneous
page stock, the two-boundary-call composition and the global S3 fast-time bound
remain open. S3 remains partial.

Validation: all 10,270 guarded stage-audit jobs pass, including explicit audits
for all ten new support, masking, fill and row-cardinality theorems. Combined
build peak is 2.7 GiB. All three new/revised Lean modules pass individual guarded
checks at at most 2043.5 MiB. Added-source integrity, plan-status and whitespace
checks pass; proof limits are unchanged.

### Executed natural boundary-coordinate enumeration

`boundaryOrderRow` runs the existing executed local halo-boundary predicate and
emits an unsigned ambient coordinate only when that predicate is true.
`boundaryOrderCode` enumerates the ambient coordinate range with a proved
`31*s+3` table-atom bound and retains the original geometry headers. It does not
accept a boundary list, membership mask or count from the caller.

`boundaryOrderHost` compiles that enumeration, publishes the coordinate words
in emission order and releases the entire geometry table bank. Its bound is
`(31*s+3)*tblC V V+2*s*V+62*V+65`. `boundaryOrderFromHeaders` loads the ordinary
unary geometry headers. `closedBoundaryOrder` additionally generates a
sufficient geometry-only width and clears it afterward, changing only the
output prefix on 109 and preserving its arbitrary borrowed suffix. Its checked
polynomial envelope is `5000*(s+t+band+a+b+1)*(V+4)^2`, with
`V = publicationGeometryWidth t band`. All setup, output movement and workspace
release are paid.

`boundaryIndices_order` identifies the emitted coordinate order with `bOrder`
of the actual halo boundary in the original ambient coordinates.
`boundaryIndices_exact` proves no duplicate coordinates and exact underlying
boundary set. `boundaryOrderSymbols_eq` identifies the emitted words with that
coordinate list, and `boundaryOrderSymbols_length` proves its exact length is
`|B|*V`, including an empty boundary.

This generates natural boundary coordinates. Folding them into the local band
order, generating rank/address maps, computing Schur entries and executing
factor setup/solve/release remain open. Enumeration explicitly scans the
ambient `s` coordinates; this cost has not been relabeled as halo length or
absorbed into a uniform fast bound. Complete S3 execution and simultaneous
storage remain open. S3 remains partial.

Validation: all 10,275 guarded stage-audit jobs pass, including thirteen explicit
new execution, cost and coordinate-order/volume audits. Combined build peak is
2.7 GiB. All six new/revised Lean modules pass individual guarded checks at at
most 2046.5 MiB. Added-source integrity, plan-status and whitespace checks pass;
proof limits are unchanged.

### Prepared boundary cardinality and the existing tape fold

`preparedBoundaryOrder` generates the geometry width on 115, runs the actual
boundary-coordinate generator on owned port 109, and applies the existing
restoring fixed-width word counter to generate unary boundary cardinality on
116. Its exact execution theorem retains these three owned outputs and restores
every other stack. The count is derived from the emitted coordinates; no
boundary cardinality is supplied. Counting costs `|B|*(6*V+6)+4`, in addition to
the paid width/header/enumeration programs. Empty boundary pages are admitted.

`boundaryOrderSymbols_cstream` identifies the generated coordinate symbols as
ordinary encoded Gaussian words with real part equal to the ambient natural
coordinate and imaginary part zero. `foldList_bOrder` proves that interleaving
the first half of the actual natural boundary order with its reversed second
half gives exactly `bFoldOrder` of that same boundary. Mapping this equality to
the coordinate words yields `boundaryIndexWords_fold`.

`boundaryFold_runs` instantiates the existing proved `bandFoldLineP` tape
program on those words. It consumes the owned natural-order page, produces the
canonical folded coordinate page and restores the other valuation entries and
all registers outside its bank. Its bound is
`60*(|B|+1)*V+60*|B|+60`, with explicit width, cardinality and half-count counter
preconditions. This reuses the structural linear fold rather than introducing
a second folding implementation.

The prepared-order page now supplies actual width and boundary cardinality.
Generating/loading the fold's half-count counters and composing the bank adapter
remain open; this is not yet a closed folded-setup theorem. Schur-entry response
generation, computed factor setup/solve/release and the complete S3 uniform
fast-time/simultaneous-storage endpoint also remain open. S3 remains partial.

Validation: all 10,287 guarded stage-audit jobs pass, including nine explicit
new list/encoding, fold-execution and prepared-page execution audits. Combined
build peak is 2.7 GiB. All four new/revised Lean modules pass individual guarded
checks at at most 2052.2 MiB. Added-source integrity, plan-status and whitespace
checks pass; proof limits are unchanged.

### Generated fold counters from the actual boundary page

`boundaryFoldCounters` uses the existing restoring unary division, copy and
subtraction programs to derive the floor half-count, parity and first-half byte
count from cardinality on 116 and width on 115. For `n` words of width `w`, its
exact final state adds `floor(n/2)` ticks on 0, `ceil(n/2)-floor(n/2)` ticks on 2,
and `ceil(n/2)*w` ticks on 3. Its temporary ceiling-count stack is cleared, its
other scratch is restored, and both dimension streams retain their exact input
symbols. It works for odd, even and zero cardinality without a parity premise.
The proved bound is `n*(4*w+23)+26`.

`preparedBoundaryFoldInputs` composes the actual width/header/enumeration/count
program with this counter generation. Its single execution theorem starts from
ordinary geometry headers and returns the owned coordinate page, its generated
width, its measured cardinality and all three fold controls. Every other stack
is restored. Its cost is the sum of the two executed programs, using the actual
halo boundary cardinality; no half-count or parity control is supplied for free.

The remaining fold-bank adapter must place these generated values and the
coordinate page in the existing `bandFoldLineP` layout and release the controls
after folding. The raw fold theorem alone is not yet a closed setup caller.
Computed Schur entries, factor setup/solve/release, full S3 composition and the
uniform fast-time/simultaneous-storage endpoint remain open. S3 remains partial.

Validation: all 10,289 guarded stage-audit jobs pass, including explicit audits
for the fold-counter execution and its composition with generated boundary
inputs. Combined build peak is 2.7 GiB. All three new/revised Lean modules pass
individual guarded checks at at most 2053.2 MiB. Added-source integrity,
plan-status and whitespace checks pass; proof limits are unchanged.

### Closed generated folded-boundary page

`BoundaryFoldPlacement` embeds the existing fold's complete register namespace
in the retained 148-register bank. Its thirteen active roles use the generated
coordinate/dimension ports and low scratch; the remaining roles may retain
arbitrary spectator contents. A structural left inverse proves the finite role
encoding injective, and permutation composition proves the placement injective
and disjoint from the fold contract's clean multiplier bank. No proof limit is
raised and no new folding algorithm is introduced.

`retainedBoundaryFold_exec` runs the existing canonical fold with this placement.
Its exact frame changes only the owned natural-coordinate source on 109 and
folded result on 6, preserving every other stack, including the retained
component streams on 144–147. The standard clean-workspace hypotheses are
explicit: low scratch/multiplier ports are empty and the left bank is empty.

`closedBoundaryFold_exec` now composes generated geometry width, header loading,
actual boundary enumeration and word counting, all half-count/parity/byte
counter generation, the physical fold, two paid moves back to the coordinate
page, and temporary-control release. It starts from ordinary unary geometry
headers and empty owned workspace. Its only final owned outputs are the
canonical folded coordinate stream on 109, generated width on 115 and measured
boundary cardinality on 116. Every other stack is restored exactly. Neither a
boundary list, a fold order nor any loop counter is supplied by the caller.

The proved bound is `preparedBoundaryFoldInputsCost` plus
`70*(|B|+1)*(V+1)+71`; enumeration's ambient-axis scan remains explicitly charged
inside the preparation cost. Empty boundaries and odd/even cardinalities use
the same program. The physical folded stream is identified with `bFoldOrder`
of the actual halo boundary, retaining its original ambient coordinates.

This closes generated folded-order setup. Folded address/rank access, computed
Schur entries and factor setup/solve/release still need execution proofs, as do
the complete S3 uniform fast-time and simultaneous-storage endpoint. S3 remains
partial.

Validation: all 10,292 guarded stage-audit jobs pass, including twenty-one
explicit placement, active-port, frame and complete setup execution audits.
Combined build peak is 2.7 GiB. All four new/revised Lean modules pass individual
guarded checks at at most 2055.1 MiB. Added-source integrity, plan-status and
whitespace checks pass; proof limits are unchanged.

### Folded-coordinate access and executed Schur-column accuracy

`boundaryCoordinate` instantiates the existing restoring indexed-word program
on the canonical folded page. Its execution theorem returns the encoded ambient
coordinate `bFoldAt B j`, proves membership in the actual boundary and proves
its folded position is `j`. It preserves the coordinate page and every other
stack except the borrowed output prefix, restoring all six temporary ports.
The unary rank is explicit, and the bound `j*(12*w+9)+10*w+22` charges the source
scan; this lookup is not a certificate of fast repeated table access.

`residual_column_eq_run` identifies the interior residual of an original matrix
column with the corresponding Schur column. `solver_lipschitz`,
`residual_lipschitz` and `schur_column_error` charge pointwise input-column error
through the exact interior solve and the stated row mass, separately from the
computed residual's execution error. `halo_schur_column_error` discharges those
bounds for the actual halo subsystem using inverse margin `1/(8*p)` and row
mass at most 2, giving amplification `1+16*p` without a halo-cardinality factor.

`releasedSchurColumn_spec` applies this result to the actual executed, released
initial Schur pass. It constructs its interior solve internally, runs the
interior/residual programs and retires the temporary interior stream. Its
physical residual read on each boundary row approximates the corresponding
exact local Schur entry with error at most
`2^-(recoveryTarget p target+2)/(8*p)+(1+16*p)*η`, assuming the encoded input
column has proved error `η` against that original-matrix column. All existing
execution, magnitude, residual and restoration contracts are retained.

`schurColumnBits p entryBits = entryBits+size(1+16*p)+1` allocates the input-column
precision. Together with the executed residual pass at target `entryBits`,
`schurColumn_total_budget` bounds the combined error by `2^-entryBits`.
Instantiating `entryBits` with the existing `boundaryTableBits` allocation gives
the required table-entry allowance.

The original-matrix column stream and its magnitude/error certificate still
need an executed producer. These results do not assume or produce a completed
Schur/factor table. Streaming address access, entry construction, factor
setup/solve/release, full S3 composition and uniform fast-time/simultaneous
storage remain open. S3 remains partial.

Validation: all 10,297 guarded stage-audit jobs pass, including ten explicit
new coordinate-access, column-identity, perturbation, execution-result and
precision-budget audits. Combined build peak is 4.0 GiB. All six new/revised
Lean modules pass individual guarded checks at at most 2055.7 MiB. Added-source
integrity, plan-status and whitespace checks pass; proof limits are unchanged.

### Constructive original-column inputs and the boundary-coupling column pass

`csyms_negative_power_two` proves the scaled negative unit's exact symbol
format using a signed-word slice: `q` zero pairs followed by `w-q` real sign
bits. `negativeUnitWord` generates that format from ordinary unary width and
precision, preserving those headers and its borrowed output suffix while
releasing temporary counters. Its exact cost is `10*w+2*q+18`.

`zeroWords` generates the byte count for a zero-word line, emits it and releases
the count, with bound `10*n*w+9*n+10`. `negativeUnitBasis` uses that operation
and `negativeUnitWord` to build an ambient negative basis vector at its retained
unary coordinate on 136, above the borrowed suffix on 132. It generates both
padding lengths, restores all headers and work ports, and costs at most
`10*n*w+17*n+2*q+40`. No basis page or byte count is supplied.

`negativeUnitField_words` identifies this stream with the ambient field that
is exactly `-1` at the selected coordinate after normalization and zero
elsewhere. Its realness and norm at most one are proved. `couple_negative_unit`
identifies boundary coupling against this field with the negative original
matrix column.

`originalColumnPass_spec` instantiates the actual restoring boundary-coupling
pass with this negative basis and a zero RHS. It produces the original-matrix
column on 113, including every periodic alias, preserving both source streams
and the borrowed output suffix. Its decoded physical error is at most
`3*(2*band+1)*2^-q`. The computed column is real, its general representation bound
is derived, and its sharper norm bound is `2` plus that same error; no separate
operand/result fit premises are inputs.

`originalColumn_precision` and `originalColumn_width` prove the shared executed
precision and word width satisfy this pass. `originalColumn_error_budget` pays
its error within `2^-schurColumnBits`; `originalColumn_schur_budget` combines
that with the executed Schur-residual allowance to obtain `2^-entryBits`.
`originalColumn_magnitude_budget` gives the RHS exponent 2 bound for the next
interior pass at that precision.

The construction primitives and column pass have execution proofs, but their
closed staging/release composition is still required: prepare the zero RHS and
basis in the caller, run the pass, retire both owned sources and publish the
column for its interior response. The selected coordinate must also be loaded
from the folded page. This pass retains its full ambient-row cost; no fast
repeated-column setup bound is claimed. Computed table/factor setup/solve,
complete S3 composition and uniform time/simultaneous storage remain open.
S3 remains partial.

Validation: all 10,304 guarded stage-audit jobs pass, including seventeen
explicit new format, stream-construction, field, original-column execution and
precision/magnitude audits. Combined build peak is 4.3 GiB. All eight new/revised
Lean modules pass individual guarded checks at at most 2056.5 MiB. Added-source
integrity, plan-status and whitespace checks pass; proof limits are unchanged.

### Generated original column with source release and readiness restoration

`originalColumnInputs` now composes zero-RHS generation with the actual negative
basis constructor. It starts from reusable coupling headers and the retained
unary coordinate on 136, creates both owned source prefixes and returns
`CouplingReady` for them. Its bound is `20*s*w+26*s+2*q+50`; no source page,
padding length or byte count is supplied.

`releaseColumnSources` generates one ambient byte count, consumes exactly the
owned RHS and basis prefixes on 110 and 132, clears that count, and executes the
existing result feeder from 113 to 110. Its exact frame restores both borrowed
source suffixes and the old result suffix, publishing the column above the
original RHS suffix. All temporary ports are restored. Its bound is
`30*s*w+18*s+30`, including result publication.

`generatedOriginalColumn_spec` composes these two programs around the actual
boundary-coupling pass. From ordinary coupling headers and a selected boundary
coordinate it constructs the sources, computes the original-matrix column,
retires both sources and publishes the computed column. The final state changes
only port 110; every other stack, including the selected coordinate, is restored
exactly. Its physical output carries the proved coefficient error, realness and
`2+error` magnitude bound, and it returns reusable coupling readiness for the
new raw RHS. Its cost is the explicit sum of preparation, the existing ambient
coupling pass and source release/publication. No original column or exact Schur
matrix is an input.

The folded-page coordinate still needs to be loaded into the unary coordinate
header, and the prepared page must be parked while arithmetic uses its low-bank
workspace. Coupling-header installation/release and composition with the
executed interior response remain open for this new caller. Table/factor
setup/solve/release, the full S3 endpoint and uniform fast-time/simultaneous
storage also remain open. The existing ambient-row pass cost is retained, with
no fast repeated-column bound claimed. S3 remains partial.

Validation: all 10,307 guarded stage-audit jobs pass, including explicit audits
of input generation, source release and the composed original-column caller.
Combined build peak is 2.7 GiB. All four new/revised Lean modules pass individual
guarded checks at at most 2057.2 MiB. Added-source integrity, plan-status and
whitespace checks pass; proof limits are unchanged.

### Generated Schur column with complete temporary-source release

`restoredOriginalColumn` installs the coupling headers from retained masters,
loads a copy of the selected unary coordinate from 139 into temporary port 136,
generates the original-matrix column, clears that copy and releases the headers.
Its exact frame changes only output port 110 and restores `LengthKeyReady`.
`retainedOriginalColumn` embeds this caller into the retained 148-port bank,
preserving the parked component streams and the selected coordinate.

`generatedSchurColumn_spec` composes that producer with the executed released
interior-response/residual pass at the allocated precision. It proves physical
output error at most `2^-target` against the actual halo Schur column, together
with realness, a coefficient magnitude bound and an explicit execution-cost
bound. The caller supplies ordinary retained masters, readiness and a selected
boundary coordinate; no original column, Schur matrix, interior solution or
execution is supplied. `releaseSchurColumnInput` then discards the intermediate
original-column prefix beneath the result and restores all its scratch ports.
The complete producer changes only port 110, publishing the Schur column above
the borrowed suffix, and returns reusable solver readiness.

This closes coupling-header restoration and the executed interior composition
for the generated-column caller. Folded-coordinate loading and page parking,
streaming band-table construction, factor/solve/release, the full S3 endpoint,
and uniform fast-time/simultaneous storage remain open. The explicit ambient
row-scan cost is retained; no fast repeated-column bound is claimed. S3 remains
partial.

Validation: all 10,312 guarded stage-audit jobs pass, including five new
explicit execution/readiness audits. Combined build peak is 2.7 GiB. All five
new modules and the audit root pass individual guarded checks at at most
2057.8 MiB. Added-source integrity, plan-status and whitespace checks
pass; proof limits are unchanged.

### Load the generated folded boundary coordinate into the arithmetic caller

`decodeNaturalWord_exec` consumes one owned paired real coordinate word,
converts its real bits to the binary ABI and performs the existing linear-cost
Horner unary conversion. It appends the coordinate ticks to the destination,
consumes the word and restores all conversion scratch, with bound
`6*x+17*w+12`.

`loadBoundaryCoordinate_exec` composes the actual restoring folded-page lookup
with this decoder. It preserves the folded page, its borrowed suffix, width,
lookup index and every other stack; only port 139 becomes the selected unary
coordinate. It proves boundary membership and inverse folded position. Its cost
is `j*(12*w+9)+27*w+6*x+34`, retaining both the page scan and unary decoding
costs. `loadBoundaryCoordinate_generatedWidth` proves that the width generated
by the existing geometry setup suffices, so no extra coordinate-fit assumption
is needed for the actual page. This closes the representation gap between the
folded-page coordinate and the generated Schur-column caller.

Page parking during arithmetic remains open: the retained page on 109 and its
headers on 115/116 conflict with the low arithmetic workspace. Streaming table
construction, factor/solve/release, the full endpoint and uniform time/storage
bounds remain open; S3 is partial. In particular, this linear unary coordinate
conversion is paid explicitly and supplies no fast repeated-access claim.

Validation: all 10,314 guarded stage-audit jobs pass, including the three new
explicit decoder/loader audits. Combined build peak is 2.7 GiB. Both new modules
and the audit root pass individual guarded checks at at most 2055.6 MiB.
Added-source integrity, plan-status and whitespace checks pass; proof limits
are unchanged.

### Resident folded page during executed Schur-column arithmetic

`boundaryArithmeticReg` embeds the 148-port arithmetic bank into 151 physical
ports, sending arithmetic registers 109/115/116 to fresh ports 148/149/150.
The prepared folded page and its width/cardinality headers remain resident on
physical 109/115/116, outside the arithmetic image. The map is injective and
`boundaryArithmeticProject_page` proves that arbitrary retained page/header
contents do not affect the arithmetic view. This resolves the workspace
conflict by static placement; it adds no page copies or execution steps.

`boundarySchurColumn_spec` runs the actual generated Schur-column program in
this placement. It preserves the existing entry accuracy, realness, magnitude,
explicit time bound and returned readiness. Its exact physical frame changes
only port 110, so it restores every other stack, including the resident page,
its headers and the parked complex-component streams. The three new physical
tapes provide arithmetic scratch, with its original restoration guarantees.

The caller still requires the selected coordinate and projected arithmetic
readiness. Composing the resident-page coordinate loader with this placement,
streaming the required band entries, constructing and releasing the factor
page, and the final solve endpoint remain open. The ambient scan cost remains
explicit; neither a fast repeated-column bound nor the full simultaneous
retained-page/scratch storage bound follows from this placement. S3 is partial.

Validation: all 10,316 guarded stage-audit jobs pass, including six new explicit
placement/frame/execution audits. Combined build peak is 2.7 GiB. Both new
modules and the audit root pass individual guarded checks at at most 2058.4 MiB.
Added-source integrity, plan-status and whitespace checks pass; proof limits
are unchanged.

### Indexed execution from the resident folded page through Schur-column publication

`residentBoundaryWord` and `loadResidentCoordinate` perform the restoring lookup
and paid unary decoding directly in the 151-port resident-page placement.
`selectResidentCoordinate` additionally consumes the lookup index on port 0,
freeing that arithmetic scratch port. It returns boundary membership and the
inverse folded position, with cost
`n*(12*V+11)+27*V+6*x+36`, where `x` is the selected ambient coordinate.
`LengthKeyReady.update_coordinate` proves that the retained coordinate is a
spectator of solver readiness.

`indexedSchurColumn_spec` composes this actual selection with the resident-page
Schur-column program and final coordinate cleanup. The caller supplies the
prepared folded page, its generated geometry width, a folded-page index and
ordinary projected readiness with that index removed. Boundary membership,
coordinate fit and the coordinate header are derived internally. The output
has entry error at most `2^-target` against the actual Schur column selected by
`bFoldAt`; realness, magnitude and reusable readiness are preserved. Its exact
frame consumes the lookup index and publishes the result on 110, restoring all
other stacks, including the page, headers, retained component streams and
coordinate port 139. The explicit bound adds selection, the existing generated
column cost and `2*x+2` for coordinate release. No coordinate, original column,
Schur matrix or supplied execution is an input.

The resident-page loader and arithmetic caller are now composed. The complete
page-setup-to-table loop, streaming the required band entries, factor/solve and
release, the final S3 endpoint, and uniform fast-time/simultaneous storage remain
open. Both ambient scans and unary-coordinate costs remain explicit; no fast
repeated-column claim is made. S3 remains partial.

Validation: all 10,319 guarded stage-audit jobs pass, including six new explicit
projection, coordinate-readiness, lookup/selection and indexed execution audits.
Combined build peak is 2.7 GiB. All four new/revised modules and the audit root
pass individual guarded checks at at most 2060.6 MiB. Added-source integrity,
plan-status and whitespace checks pass; proof limits are unchanged.

### Restoring computed-entry extraction and clipped folded-band storage schedule

`generateWordWidth_exec` factors the structural width reconstruction shared by
the existing coupling caller and the resident entry extractor. Both placements
instantiate the same program and proof; the existing `8*q+9` cost is unchanged.
`copyResidentEntry_exec` generates width `2*q+8` from retained precision, copies
the selected ambient word from computed column 110 onto the retained suffix on
132, and releases the width header. It restores the entire source column and
all other stacks, charging the generated offset and restoring source motion.

`selectedColumnEntry_exec` composes resident folded-page lookup, unary decoding,
entry copying and coordinate cleanup. Its exact frame consumes the row lookup
index and prepends one computed word on 132, preserving the page, computed
column and all other stacks. The extracted word's decoded real value equals
the corresponding physical published-column read exactly, so extraction adds
no numerical error and does not require an additional signed-fit hypothesis.
Its cost includes the folded-page scan, unary coordinate, ambient column scan,
width generation and cleanup.

`foldedBandIndices` gives the clipped contiguous rank interval for a column's
folded band. The membership theorem identifies its mapped rows exactly with
boundary membership and `FoldBRel`; each column has at most `2*W+1` scheduled
entries. Their packed words occupy at most `(2*W+1)*wordWidth` symbols. This is
a bound for the selected packed entries, not the complete machine's live
storage. The executable loop generating these row controls and accumulating
the complete table still needs composition. Factor/solve/release, the final
endpoint and uniform fast-time/simultaneous storage also remain open. S3 is
partial; the explicit source scans are not a fast repeated-access bound.

Validation: all 10,324 guarded stage-audit jobs pass, including ten new explicit
width, extraction and band-schedule audits. The shared-definition rebuild peaks
at 13.8 GiB combined. All six new/revised modules and the audit root pass
individual guarded checks at at most 2057.2 MiB. Added/revised-source integrity,
plan-status and whitespace checks pass; proof limits are unchanged.

### Executed folded-band accumulation loop with complete control release

`columnEntryStep_exec` copies the retained folded-row cursor into the lookup
index, executes resident-page selection and entry extraction, then advances
the cursor. It prepends one whole word to the retained table suffix on 132 and
preserves every other stack. Its cost includes cursor copying, the selected
entry routine and the cursor increment.

`columnEntryLoop_exec` uses the existing structural counted scan to accumulate
an arbitrary in-range contiguous folded-row interval. Its invariant tracks the
cursor and exactly the reversed prefix of copied whole words; the resident
page, ambient computed column, original table suffix and arbitrary counter
symbols are preserved. Its bound sums the actual per-entry costs and charges
the counted-scan overhead. `collectColumnEntries_exec` then consumes both owned
cursor/count controls, charging their lengths, and restores all other stacks
apart from the accumulated table prefix.

`collectFoldedBand_exec` specializes this executable collector to the clipped
interval `n-W` through `min rowCount (n+W+1)`. Its packed output is exactly the
reverse of the proved `foldedBandRows` schedule mapped through the computed
column, so the existing exact-support and `(2*W+1)*wordWidth` storage results
apply to the accumulated prefix. The column and folded page remain intact.

The caller still supplies ordinary unary cursor/count headers for that clipped
interval. Generating them from the retained column index, band and boundary
cardinality, composing column generation with collection/source retirement,
and the outer complete-table loop remain open. Factor/solve/release, the full
S3 endpoint and uniform fast-time/simultaneous storage also remain open. The
explicit cost pays repeated page/column scans and asserts no fast-access bound;
S3 remains partial.

Validation: all 10,328 guarded stage-audit jobs pass, including four new explicit
step, loop, cleanup and folded-band collection audits. Combined build peak is
2.7 GiB. All four new modules and the audit root pass individual guarded checks
at at most 2058.1 MiB. Added-source integrity, plan-status and whitespace checks
pass; proof limits are unchanged.

### Generate the clipped band controls and execute prepared collection

`bandIntervalEndpoints_exec` constructs unary `n-W` and `n+W+1` from borrowed
index/band headers. `clipUnary_exec` clips an owned count to a borrowed bound
and restores its scratch through structural unary arithmetic. Their composition
`clippedBandControls_exec` generates cursor `n-W` and count
`min rowCount (n+W+1)-(n-W)`, restoring all input headers and temporary controls.
All costs are explicit; the proofs retain the default heartbeat/depth limits.

`residentBandControls_exec` instantiates this construction in the resident bank.
It generates `W = 12*band+1` from retained geometry on 124, uses the boundary
cardinality on 116, derives both collector controls from the column index on 0,
and releases the temporary band header, complement and lookup index. The
ordinary geometry/cardinality headers and every other stack are preserved.

`preparedBandCollection_exec` composes that actual setup with the executed
folded-band collector. It no longer takes a supplied cursor, count or band-width
header. Its output prepends exactly the reversed folded-band words of the
computed column to table port 132. The column, resident page, page suffix,
retained masters and all temporary stacks are restored; only the owned lookup
index is consumed and the table prefix grows. Its bound pays setup, all entry
lookups/scans, accumulation and complete control release.

Composition with actual column generation and retirement, retaining the column
index across that lifecycle, and the outer complete-table loop remain open.
Factor/solve/release, the full S3 endpoint and uniform fast-time/simultaneous
storage also remain open. Repeated page/column scans are still charged
explicitly; S3 remains partial.

Validation: all 10,333 guarded stage-audit jobs pass, including six new explicit
endpoint, clipping, control-generation and prepared-collection audits. Combined
build peak is 4.1 GiB. All five new modules and the audit root pass individual
guarded checks at at most 2057.6 MiB. Added-source integrity, plan-status
and whitespace checks pass; proof limits are unchanged.

### Complete executed single-column table lifecycle

`tableReg` embeds the resident 151-port bank into a fixed 154-port bank, reserving
151 for the folded-column cursor and 152/153 for the outer counted scan. The
projection/frame lemmas prove that retained outer controls do not interfere
with embedded arithmetic. `retainedIndexedColumn_spec` copies the cursor into
the consumed lookup index and executes the actual indexed column producer,
preserving the outer cursor and both count controls. Only temporary source 110
changes; the numerical column accuracy, realness, magnitude and readiness are
retained.

`retireResidentColumn_exec` reconstructs word width and ambient byte count from
the retained precision/length masters, consumes exactly one owned column prefix,
and restores the borrowed source suffix and every scratch port. Its bound pays
width/count generation, full source motion and complete cleanup.
`collectRetireColumn_exec` joins prepared band collection with that retirement;
`retainedColumnCollection_exec` obtains the column index from the retained outer
cursor and lifts the actual combined execution into the table-loop bank.

`tableColumn_spec` now composes the whole lifecycle: obtain the selected column
from the resident page, generate its original/interior response, collect exactly
its clipped folded-band entries, release every temporary control and retire the
ambient column. Its final physical frame changes only table port 132, prepending
that column's packed band entries. The original source, resident page, headers,
complex-component streams and all outer controls are restored exactly, and it
returns the original source's solver readiness with the enlarged table suffix.
The decoded emitted words carry `2^-target` error against the actual selected
Schur column; extraction introduces no new rounding. The explicit time bound
includes both copies of the retained cursor and every generation, collection
and retirement cost. No column, Schur matrix, interior solution or execution is
supplied to this caller.

The outer complete-table loop and its global packed-page error contract remain
open, followed by factor/solve/release and the full S3 endpoint. Uniform fast
time and simultaneous retained-page/scratch storage also remain open; this
lifecycle still pays the explicit repeated source scans. S3 remains partial.

Validation: all 10,339 guarded stage-audit jobs pass, including ten new explicit
workspace/frame, retirement, retained execution and lifecycle audits. Combined
build peak is 2.7 GiB. All six new modules and the audit root pass individual
guarded checks at at most 2061.8 MiB. Added-source integrity, plan-status
and whitespace checks pass; proof limits are unchanged.

### Executed complete boundary-table loop and packed-page error contract

`scanInvariant_exec` supplies a structural counted scan whose invariant may
contain coefficients obtained from execution. It preserves the left bank,
tracks the actual per-iteration costs, and restores the count/saved-count ports.
This avoids assuming a predetermined coefficient field or execution trace for
every column. `TableLoopInvariant` combines the actual accumulated column list,
its decoded entry accuracy and the exact frame outside the table/cursor and
scan controls. The readiness transfer lemmas permit arbitrary accumulated table
prefixes and outer controls while retaining the original solver source.

`bandTableWords` specifies the physical column-block packing, including both
descending column order and descending folded-row order within each block. Its
append theorem matches actual stack accumulation. The packed prefix is bounded
by `columnCount*(2*W+1)*wordWidth`. `computedBoundaryTable_error` transfers the
produced column family to the full boundary matrix; band masking retains the
same entry error, with no additional numerical or cardinality factor.

`tableLoopStep_spec` joins the actual single-column lifecycle to cursor advance
and extends the packed-page invariant with the column actually produced.
`tableColumnsLoop_spec` executes all boundary columns and returns the entire
accurate column family and physical packed prefix. `buildBoundaryTable_spec`
generates the count from retained boundary cardinality, runs that complete
loop and releases every outer control. Its final exact physical frame changes
only table port 132. The original source, resident folded page and suffix,
geometry/precision masters, parked component streams and all scratch/control
ports are restored, and solver readiness is returned. The table is no longer a
supplied matrix, factor page, coefficient family or collection of executions.

The public builder proves `2^-target` decoded entry error for the masked actual
halo Schur table and a packed-prefix bound
`boundaryCount*(24*band+3)*wordWidth`. This is the retained table prefix's size,
not a complete simultaneous machine-storage theorem. Its time bound sums the
actual column-generation, gathering, retirement and scan/setup/release costs;
no fast repeated-source-access bound is claimed.

Composing the prepared folded-page setup with this builder, executing table
access/factorization/solve/release and joining the full real/imaginary endpoint
remain open. Uniform fast time, the full simultaneous storage bound and the
final S3 theorem remain open. S3 is partial.

Validation: all 10,346 guarded stage-audit jobs pass, including fourteen new
explicit scan, packing/error, frame/readiness, invariant and complete-builder
audits. Combined build peak is 2.7 GiB. All seven new modules and the audit root
pass individual guarded checks at at most 2064.7 MiB. Added-source integrity,
plan-status and whitespace checks pass; proof limits are unchanged.

### Folded-page setup composed with complete computed-table construction

`installBoundarySetupHeaders_exec` copies only the five geometry headers needed
by folded-page setup from retained masters 121/122/124/141/142. Its cost is
`4*(s+t+band+a+b)+21`; the matching release costs
`2*(s+t+band+a+b)+11`. Neither coupling precision/width nor multiplier headers
are unnecessarily installed. The payload commutation/frame lemmas permit the
new coordinate page to survive header release.

`tableBoundaryFold_exec` places the existing complete coordinate-page constructor
in the 154-port table bank without tying it to a second procedure table. The
constructor is instantiated with an empty procedure type and embedded into the
actual caller; no supplied execution, procedure oracle or new workspace is
introduced. `prepareBoundaryPage_exec` composes ordinary geometry-header setup,
coordinate generation/folding, cardinality and width generation, and complete
runtime-header release. Only the owned page on 109 and its headers on 115/116
change; masters, source, retained components and all scratch are restored.

`tableArithmeticProject_page` proves that these generated resident resources
leave the relocated arithmetic view unchanged. `constructedBoundaryTable_spec`
uses that fact to compose preparation with the actual complete table builder.
It starts from retained solver readiness, ordinary masters and empty owned page
ports; no folded page, width, cardinality, coefficient family, Schur matrix or
execution is supplied. Its final frame retains the generated folded page and
headers alongside the packed table on 132. It returns solver readiness, the
exact packed representation, the packed-table size bound and `2^-target`
decoded entry accuracy against the actual masked halo Schur matrix. All setup,
folding, table-generation and cleanup costs are explicitly included.

The page-setup/table-production composition is now closed. Executed access to
the packed table, factorization/solve/release and the full real/imaginary endpoint
remain open, as do uniform fast time, complete simultaneous live storage and
the final S3 theorem. The retained table-prefix bound alone is not the complete
storage contract, and explicit scan costs alone are not the uniform fast-time
bound. S3 remains partial.

Validation: all 10,351 guarded stage-audit jobs pass, including nine new explicit
header/frame, procedure-free folding, prepared-page and composed table audits.
Combined build peak is 2.7 GiB. All five new modules and the audit root pass
individual guarded checks at at most 2065.9 MiB. Added-source integrity,
plan-status and whitespace checks pass; proof limits are unchanged.

### Packed-entry addressing and restoring decoded access

`bandTableValues` exposes the word-level layout of the physical packed table;
`bandTableWords_values` identifies its symbol stream exactly. The append and
column-splitting lemmas account for the reversed column blocks and clipped,
reversed folded rows within each block. `packedBandWordCount` structurally
counts words using only boundary cardinality, half-band width, start and count;
it does not inspect coefficient values.

`packedEntryOffset` is the corresponding computable word address: the word
count of all later column blocks plus the selected row's displacement in its
reversed block. `packedEntryOffset_entry` proves that it selects exactly the
requested computed coefficient, and its address is below
`boundaryCount*(2*W+1)`. The address depends only on dimensions and folded ranks,
not on a supplied coefficient field, address oracle or execution.

`copyPackedWord_exec` generates word width from retained precision, executes
restoring indexed access to table port 132 and prepends the copied word on 143,
then releases its width header. The table, borrowed suffix and all other ports
are restored. `packedBoundaryEntry_exec` instantiates that actual program with
the proved packed address and shows that the physical copied word decodes
exactly to the corresponding entry of the masked computed boundary matrix.
No signed-fit assumption or extra numerical error is introduced. Its explicit
cost includes width generation, generated byte offset, restoring table scans
and cleanup.

The current lookup contract still requires an ordinary unary address header
whose length equals the proved dimension/rank address. Executing address-header
generation from runtime row/column controls, joining this lookup to fixed band
factor rows, factorization/solve/release and the full endpoint remain open.
Uniform fast time, complete simultaneous storage and the final S3 theorem also
remain open. S3 is partial; the mathematical address is not yet an executed
address generator.

Validation: all 10,355 guarded stage-audit jobs pass, including ten new explicit
layout/count, address, restoration and decoded-entry audits. Combined build peak
is 2.7 GiB. All four new modules and the audit root pass individual guarded
checks at at most 2068.7 MiB. Added-source integrity, plan-status and
whitespace checks pass; proof limits are unchanged.

### Executed rank-to-address generation and restoring packed-entry lookup

`packedSizeStep_exec` generates one clipped block size from runtime cursor,
band and boundary-count headers, adds it to an address accumulator, releases
its temporary controls and advances the cursor. `packedSizeLoop_exec` executes
a structural counted scan over the later columns; `packedBandWordCount_succ`
connects its growing accumulator with the coefficient-independent packed-size
function. `packedSizeSum_exec` then consumes the owned cursor/count headers,
restoring all other ports. Every block calculation, accumulator copy, scan and
cleanup is explicitly charged.

`packedSuffixControls_exec` derives `start = n+1` and `count = N-(n+1)` from
borrowed column-rank and cardinality headers. `packedSuffixAddress_exec` joins
that setup with the actual summation, so the later-column word count is no
longer supplied. `packedWithinAddress_exec` computes the selected row's reverse
block displacement by endpoint generation, unary clipping, decrement and row
subtraction, restoring all of its scratch. `generatePackedAddress_exec`
composes the two contributions and proves that the generated unary header has
exactly the computable `packedEntryOffset N W n m` length. The program reads
only runtime dimensions/ranks, not coefficients or a precomputed address.

`rankedBoundaryEntry_exec` now joins actual address generation to packed-word
lookup and final address release. It borrows the half-band width header on 94,
parks and restores its exact symbols while generating coefficient word width
from retained precision, and preserves row/column ranks on 108/107, cardinality,
table and suffix, and all scratch. Its final exact physical frame changes only
copied-entry port 143. The physical copied word decodes exactly to the selected
entry of the masked computed boundary matrix. No address header, address
execution or additional signed-fit/error hypothesis is supplied. The explicit
cost includes all address setup/scans, width parking/restoration, table access
and address cleanup.

This closes runtime rank-to-packed-entry lookup for in-band entries. Producing
fixed band-factor rows, including their zero padding and precision/word
representation, and joining factorization/solve/release to the full endpoint
remain open. Uniform fast time, complete simultaneous live storage and the
final S3 theorem also remain open. The lookup's ordinary half-band and rank
headers still need their factor-caller setup. S3 remains partial.

Validation: all 10,363 guarded stage-audit jobs pass, including nine new explicit
count-growth, block summation, control generation, complete address and ranked
lookup audits. Combined build peak is 2.7 GiB. All nine new/revised modules and
the audit root pass individual guarded checks at at most 2065.6 MiB. Added/revised-source
integrity, plan-status and whitespace checks pass; proof limits are unchanged.

### Preserve canonical real coefficient words and execute factor-input word paths

`ColumnFamilyFormat` records that every produced column is real and fits its
allocated coefficient width. The complete-table invariant now carries this
property through actual column accumulation; the existing numerical magnitude
bound and `stableInteriorResidual_width` derive it at each step. The loop,
complete builder and setup-composed constructor return it alongside the entry
accuracy and packed-page representation. This strengthens the produced-table
contract without changing the executed programs or their costs.

`feedFactorWord_exec` reconstructs coefficient width from retained precision,
moves exactly one owned lookup word from 143 onto the factor-input suffix on
140 in its original order, and releases its width control. Both borrowed tails
and all scratch are restored. `factorEntry_exec` composes actual ranked lookup
with that move. Its final exact frame changes only factor-input port 140; the
packed table, rank/width/cardinality headers and lookup destination are restored.
The emitted word is real, fits its width and has grid value exactly equal to
the selected masked computed boundary entry. The format evidence comes from
the actual complete table builder, with no separate fit or realness oracle.

`factorZeroEntry_exec` supplies the padding path: it generates one full encoded
zero word using the retained precision and restores its temporary width and
copy scratch. It also changes only factor-input port 140. Neither path adds
rounding, and both charge width setup, word motion/emission and cleanup.

The fixed-width factor-row loop and its runtime branch selection between
in-band lookup and padding remain open. The factorizer's initial window and
later input-row layout still need the composed execution contract, followed by
factorization/solve/release and the full endpoint. Uniform fast time, complete
simultaneous storage and the final S3 theorem remain open. S3 is partial.

Validation: all 10,366 guarded stage-audit jobs pass, including four new explicit
format-extension, word-feed, real entry and padding audits, plus the strengthened
existing loop/builder contracts. Combined build peak is 2.7 GiB. All nine
new/revised modules and the audit root pass individual guarded checks at at most
2066.5 MiB. Added/revised-source integrity, plan-status and whitespace checks
pass; proof limits are unchanged.

### Execute complete fixed-width factor rows with runtime padding selection

`unaryIfLt_exec` and `unaryIfLeSum_exec` provide borrowed unary comparisons
that restore their controls before executing either continuation. `factorChoice_exec`
uses runtime ranks, cardinality and half-band width to choose actual packed-table
lookup or zero-word emission. `factorWord_exec` therefore emits a canonical real,
width-fitting word for every natural row/column pair, including out-of-range and
out-of-band padding, while changing only factor-input port 140.

`factorRowLoop_exec` scans columns downward and prepends each emitted word,
producing ascending column order. `factorRow_exec` generates the full `2*W+1`
count, borrows the caller's starting-column cursor, emits the complete row, and
releases its controls. Its final exact physical frame changes only port 140:
the packed table, retained headers, arbitrary cursor symbols and all scratch
are restored. Explicit costs include runtime comparisons, lookup or padding,
count/cursor setup, scanning and cleanup.

`factorRowValues_grid` identifies these words exactly with the factorizer's
`winRow` of the zero-extended masked computed boundary matrix. The same row
contract supports the initial window's start-zero rows and later shifted rows;
all words are real and fit their allocated width. No additional rounding or
supplied row execution is assumed.

This closes individual fixed-width row emission. Composing the initial window
and later input-row page, executing factorization/solve/release, and proving the
full endpoint remain open. Uniform fast time, complete simultaneous live storage
and the final S3 theorem remain open. S3 is partial.

Validation: all 10,374 guarded stage-audit jobs pass, including 13 new explicit
comparison, selector, word, row execution and grid/format audits. Combined build
peak is 2.7 GiB. All eight new modules and the audit root pass individual guarded
checks at at most 2067.1 MiB. Added-source integrity, plan-status and whitespace
checks pass; proof limits are unchanged.

### Execute the complete initial-window and shifted-row factor input page

`factorWindow_exec` now generates the `W+1` start-zero rows of the initial
window, each with `2*W+1` words. Its outer scan descends the row cursor and
prepends whole rows, producing ascending row order. It generates its own count
from the retained half-band width and releases both count and row cursor.

`factorInputs_exec` generates all `B.card` shifted update rows. For start
`n = 1,...,B.card`, it derives row rank `W+n` from runtime width/start headers
and executes the existing complete row emitter at columns `n,...,n+2*W`.
The outer scan again prepends rows in natural order. Row-rank setup is released
at every iteration; the starting cursor and outer count are released last.
Neither loop assumes a supplied row execution or any coefficient oracle.

`factorPage_exec` composes these generators into the exact initial-window,
then update-row source page required by the band factorizer. The only final
physical change is the page prepended on port 140: the packed table and suffix,
retained headers, all scan controls and arithmetic scratch are restored. Its
explicit cost includes both generators and every inner row operation.

The page-value contracts establish row counts, common row length, realness,
width fit, exact zero-extended matrix windows and total coefficient count
`(W+1+B.card)*(2*W+1)`. The integer-row compatibility lemmas identify the
emitted Gaussian words exactly with `colC` of their real integer coordinates,
matching the factorizer's input representation without additional rounding.

`generatedFactorPage_exec` also derives the half-band header `12*band+1` from
retained master 124, executes the full page generator and releases that header.
Its exact final frame again changes only port 140; no supplied factor-width
header or setup execution is needed.

Full factorization/solve/release composition and its stability/precision
conditions remain open, as do uniform fast time, complete simultaneous live
storage and the final S3 theorem. S3 remains partial.

Validation: all 10,384 guarded stage-audit jobs pass, including 25 new explicit
window/input scans, full page, setup, shape, grid, format and integer-row audits.
Combined build peak is 2.7 GiB. All ten new modules and the audit root pass
individual guarded checks at at most 2072.3 MiB. Added-source integrity,
plan-status and whitespace checks pass; proof limits are unchanged.

### Compose table construction with the complete factor page and its stability interface

`constructedBoundaryFactorPage_spec` executes folded-page setup, every computed
Schur column, packed-table construction and the full factor-input page from the
ordinary retained-master invariant. The columns, accurate matrix, packed table,
factor-width header and emitted rows are all produced by this execution. The
final exact physical frame changes only the folded coordinate page and headers,
packed table and factor-input page. Clearing the consumed factor-page port
restores `LengthKeyReady`; this is a readiness statement, not an assumed page
consumption execution. The explicit cost includes the complete table builder
and generated factor page.

`boundaryTable_stageInv` converts the produced entry error into row error
`B.card * 2^-target` and the corresponding dominance/mass losses. The composed
constructor returns this invariant both on boundary coordinates and natural
factor ranks. `factorRankMatrix_band` proves the exact required band support.
The rank transfer uses a structural sum bijection over the folded boundary;
it does not evaluate or compare concrete matrix data.

`factorRankIntegerMatrix_value`, `factorWindowIntegers_windowZ` and
`factorInputIntegers_inputsZ` identify the actual emitted integer rows with one
zero-extended band matrix. `factorIntegerState_window` identifies every
intermediate `facState` with that matrix's integer elimination-stage window.
`factorIntegerStage_sizes` and `factorIntegerState_fits` adapt the existing
stage/Newton bounds to this actual computed matrix, including arbitrary positive
half-band width and the zero-padding cases. They derive all pivot, reciprocal,
truncated-product, row-entry and multiplier fits from the rank stage invariant
and explicit precision/Newton/width inequalities, rather than a supplied
per-step `FacFits` oracle.

`boundaryTable_factor_margin_budget` proves that the existing
`boundaryTableBits` allocation bounds total row error by `1/(16*p)`.
`boundaryFactor_stageInv_allocated` therefore gives the positive `1/(16*p)`
margin and `9/4` mass used by the factor-stage size proof.

The remaining precision/Newton/width inequalities still need their canonical
allocation proofs, and the actual factorization/solve/release programs still
need composing with this produced page and the full endpoint. Uniform fast
time, complete simultaneous live storage and the final S3 theorem remain open.
S3 remains partial.

Validation: all 14,579 guarded stage-audit jobs pass, including 17 new explicit
ready-handoff, constructed-page, band/stability, integer-state, size/fit and
allocated-margin audits. Combined build peak is 4.4 GiB. All eight new modules
and the audit root pass individual guarded checks at at most 2942.4 MiB, below
the 4 GiB per-module target. Added-source integrity, plan-status and whitespace
checks pass; proof limits are unchanged.

### Discharge canonical factor precision and execute prepared boundary factorization

`factor_execution_bits` proves that the existing execution precision, at the
`boundaryTableBits` entry target, exceeds `4*p + 2*Nat.size B.card + 36`.
The structural power bounds in `factor_roundoff_budget`,
`factor_stage_roundoff_budget` and `factor_record_width_budget` pay the Newton
rounding allowance, accumulated stage perturbation and every record's allocated
width `2*q+8`. No larger working precision or proof limit is introduced.

`factorNewtonSteps p q = Nat.size (256*p*(q+1))` supplies a concrete Newton
iteration count. A structural contraction proof shows that a block of `256*p`
powers halves the initial contraction factor; the chosen count therefore pays
the reciprocal error condition. `factorNewtonSteps_bound` proves the count is
at most `8 + Nat.size p + Nat.size (q+1)`, preserving logarithmic iteration cost.

`factorIntegerState_allocated_fits` joins these bounds with the allocated
positive dominance margin. It derives `FacFits` for every actual emitted-page
factor state without any remaining precision, Newton, width or per-state fit
hypothesis. `constructedBoundaryFactorPage_allocated_spec` attaches these facts
to the actual retained-master table/page execution, retaining its exact frame,
accuracy, format, readiness-after-consumption and explicit cost contracts.

`boundary_axisPrep_allocated_runs` instantiates the existing executed band
factorization and table-preparation machine with these exact computed integer
rows and derived fit facts. Its source is the full emitted Gaussian page; its
Newton seed is one fixed encoded `2^(q-2)` word, independent of the pivot. It
produces the forward multipliers, transposed backward columns and reciprocal
tables with the existing explicit preparation cost and frame. The hypotheses
are the ordinary machine readiness, seed and control/header layout, not a
supplied factorization execution or numerical-fit oracle.

Generating that physical factor workspace and its runtime control headers,
joining its register map to the constructed page, executing the real/imaginary
solves and releases, and proving the full endpoint remain open. Uniform fast
time, complete simultaneous live storage and the final S3 theorem remain open.
S3 remains partial.

Validation: all 14,584 guarded stage-audit jobs pass, including nine new explicit
precision, width, logarithmic Newton-count/error, allocated-fit, constructed-page
and executed factor-preparation audits. Combined build peak is 5.6 GiB. All five
new modules and the audit root pass individual guarded checks at at most
2942.9 MiB, below the 4 GiB per-module target. Added-source integrity, plan-status
and whitespace checks pass; proof limits are unchanged.

### Install a physical factor bank and generate its multiplier readiness

`boundaryFactorReg` places the factorizer's 69 roles on a fresh fixed bank of
224 total tapes, with its owned source mapped directly to physical port 140.
`boundaryFactorLegacyReg` embeds the existing 154-tape caller unchanged. A
structural decoder proves bank injectivity; the multiplier's 64 low scratch
tapes are disjoint. `boundaryFactorFr_legacy` proves that a factor run preserves
input/output, all left stacks and every legacy right tape except owned source
140, including the packed table, coordinate page and retained masters.

`boundary_axisPrep_physical_exec` now gives an actual `Exec` of the allocated
factorization/table-preparation program on this physical bank. Its output
contracts read the actual resulting stacks, rather than a supplied abstract
post-valuation. All numerical fits still come from canonical allocation, and
the frame protects the entire legacy caller. The ordinary factor workspace,
seed and dimension-header requirements remain explicit.

`boundaryFactorScalarReg` adapts the existing scalar setup program to this bank.
`boundaryFactorCountersFromWidth_exec` executes it with an empty call type, so
it works under any enclosing body table and introduces no call-body assumption.
It generates the word-width, precision and `topN` counters and restores all its
binary setup scratch. `boundaryFactorMultiplierSetup_exec` first reconstructs
word width from retained precision on 119, executes that generator and releases
the private width header. Its exact final frame changes only counter ports
160/161/162, and it returns `RsbReady`. No supplied word width, topN counter or
readiness execution is required.

Generating the remaining factor dimensions, logarithmic Newton-count header
and seed, lifting/composing the constructed-page execution into this physical
bank, executing real/imaginary solves and releases, and proving the full
endpoint remain open. Uniform fast time, complete simultaneous live storage
and the final S3 theorem remain open. S3 remains partial.

Validation: all 14,589 guarded stage-audit jobs pass, including 16 new explicit
register injection/disjointness, legacy frame, physical factor execution, scalar
adaptation and generated-counter/readiness audits. Combined build peak is
3.4 GiB. All five new modules and the audit root pass individual guarded checks
at at most 2948.1 MiB, below the 4 GiB per-module target. Added-source integrity,
plan-status and whitespace checks pass; proof limits are unchanged.

### Generate physical factor dimensions and compose them with table/page construction

`UnarySetup.exec` proves a structural straight-line setup interpreter for borrowed
unary additions/products, fixed pushes and cleanup. Each instruction charges its
actual arithmetic cost and restores its scratch; the list theorem carries the
exact resulting register function. Its frame lemmas preserve every unwritten
tape. This factors the repeated tape argument out of the concrete setup.

`boundaryFactorDimensions_exec` now generates the eight factor dimension/volume
headers from retained band/cardinality masters and generated word width. It
constructs `k=12*band`, `W=k+1`, `2*W`, the pivot count, `k*w`, `2*W*w`,
`(2*W+1)*w` and `(W+1)*(2*W+1)*w`. The temporary row-count header is released.
The proved explicit cost includes every scan and unary product. Multiplication
readiness and all tapes outside the declared header ports are preserved.
`boundaryFactorHeaderSetup_exec` composes this with generated multiplier
readiness; `boundaryFactorHeaderR_legacy` preserves every legacy tape exactly.

`boundaryFactorHeaderHandoff_exec` supplies the structural bridge from any
legacy table state with the proved frame to the fresh physical factor bank.
`constructedBoundaryFactorHeaders_spec` lifts the actual allocated table/page
construction into that bank and executes the combined header setup. It returns
the exact physical state, live input page, `RsbReady`, column accuracy/format,
packed-table storage bound, entry error, rank-matrix stability and all canonical
factor-state fits. No table, column family, readiness execution or factor
dimension header is supplied. The cost includes full construction and setup.
The handoff and width conversion are factored to keep default proof limits.

The logarithmic Newton-count header and encoded seed/mask still need runtime
generation. Complete factorization/solve/release composition, the full real and
imaginary endpoint, uniform fast time, simultaneous live storage and the final
S3 theorem remain open. S3 remains partial.

Validation: all 14,594 guarded stage-audit jobs pass, including 13 new explicit
structural setup/frame, dimension, readiness-preservation, legacy handoff and
composed physical-construction audits. Combined build peak is 3.4 GiB. All five
new modules and the audit root pass individual guarded checks at at most
2948.7 MiB, below the 4 GiB per-module target. Added-source integrity, plan-status
and whitespace checks pass; proof limits are unchanged.

### Generate Newton controls and encoded constants, completing physical factor setup

The unary setup interpreter now supports fixed natural division with the same
borrowed-input and restored-scratch contract. `boundaryFactorNewtonPrelude_exec`
derives `256*p` by dividing retained master `2^15*p` by 128, multiplies by
`q+1`, and releases the intermediate dimensions. `boundaryFactorNewtonHeader_exec`
uses the existing `unarySize_exec` halving routine to emit exactly
`factorNewtonSteps p q`, then releases its owned operand. Only the iteration
header on 191 changes; arbitrary master symbols and all scratch are restored.
Its explicit bound uses the existing `19*n+8` digit-count cost.

`csyms_pow_two` proves the exact single-real-bit representation of a power of
two. `setPowerWord_exec` executes that bit edit in an owned zero word, preserving
the position header, suffix and all scratch. `boundaryFactorSeed_exec` constructs
the zero word from generated word width, derives position `q-2` from retained
precision, edits it and releases the position header. The resulting word is
exactly `csyms A (2*q+8) ⟨2^(q-2),0⟩`, with no supplied word or seed execution.

`boundaryFactorConstants_exec` composes the Newton count, seed and full encoded
zero mask. Its exact final frame changes only ports 191, 218 and 186; multiplier
readiness is preserved. `boundaryFactorSetup_exec` joins this to generated
readiness and all eight dimension/volume headers, giving the complete physical
setup from retained precision/band/cardinality masters and clean workspace.
`boundaryFactorSetupR_legacy` preserves every legacy tape, including the input
page, packed table and all retained masters. The seed, mask and logarithmic
count have direct physical output contracts, and every setup operation is charged.

Replacing the partial header stage in the constructed-page caller with this
complete setup, composing actual factorization/solve/release, and proving the
full real/imaginary endpoint remain open. Uniform fast time, simultaneous live
storage and the final S3 theorem remain open. S3 remains partial.

Validation: all 14,601 guarded stage-audit jobs pass, including 11 new explicit
Newton-prelude/count, encoded power-bit/seed, complete constants/setup and frame
audits, plus the strengthened generic unary interpreter with fixed division.
Combined build peak is 3.4 GiB. All nine new/revised modules and the audit root
pass individual guarded checks at at most 2951.4 MiB, below the 4 GiB per-module
target. Added/revised-source integrity, plan-status and whitespace checks pass;
proof limits are unchanged.

### Execute complete boundary factorization from the constructed Schur page

`BoundaryFactorPrepared` collects the ordinary physical factor preconditions:
readiness, the generated seed and mask, every dimension/count/volume header,
and the empty scratch roles. `boundaryFactorSetupR_prepared` derives all fields
from the generated setup's exact frame and clean initial bank. Width conversion
is structural over an arbitrary valuation, avoiding expansion of concrete table
states under the default proof limits.

`initializedBoundaryFactor_exec` now executes complete setup followed by band
factorization and table preparation. Its caller supplies retained masters, clean
workspace and the actual encoded page, together with the already-proved matrix
accuracy/format invariant; no factor header, seed, mask, readiness execution or
per-step fit is supplied. It returns the actual forward multiplier, transposed
backward-column and reciprocal streams, consumes its full source page, retains
multiplication readiness and the line-solve dimensions, and preserves every
legacy tape outside the owned source port. Every setup and factorization cost
is included.

`boundaryFactorLegacy_input` derives the physical input contract from an
arbitrary legacy table frame and the retained-master invariant. Finally,
`constructedBoundaryFactor_spec` composes the actual folded-page/table/input-page
constructor, physical lift, generated setup and executed factorization. The
column family is produced by that execution. Its returned numerical contracts
include column accuracy/format, the packed-table bound and entry error; the
actual resulting tapes hold exactly the factors of that produced matrix. The
consumed factor-input port is restored to its original suffix, and all legacy
pages and masters retain the exact constructed-table frame. No table, column
family, matrix-entry or factorization-execution oracle is assumed.

The real/imaginary boundary RHS gathering and line solves, factor/table cleanup,
recovery/publication composition and full inverse endpoint remain open, as do
uniform fast time, complete simultaneous live storage and the final S3 theorem.
S3 remains partial.

Validation: all 14,607 guarded stage-audit jobs pass, including ten new explicit
setup-state, prepared-factor, initialized factorization, legacy-input and full
constructed-factorization audits. Combined build peak is 3.4 GiB. All six new
modules and the audit root pass individual guarded checks at at most 2954.5 MiB,
below the 4 GiB per-module target. Added-source integrity, plan-status and
whitespace checks pass; proof limits are unchanged.

### Folded boundary RHS triangular execution

`BoundarySolveReady` isolates the restored multiplier, width/count headers and
scratch required by the two triangular passes. `boundarySolveReady_of_factor`
derives this contract from the generated factor setup and the factorizer's
existing exact frame and explicit empty-port postconditions. Updating the RHS
port preserves the contract.

`boundaryPadRhs` appends the required zero look-ahead records to a gathered,
folded RHS without changing its order or the factor tables. Its structural
execution proof costs at most `4*N*w + 4*W*w + 8` steps.
`boundary_foldedSolve_runs` composes this actual padding program with the
forward/backward triangular passes. Only the RHS and solution ports change;
all factor tables and control headers are retained for subsequent RHS vectors.
The theorem still assumes coefficient and intermediate solve fit bounds; it
is not yet an allocated solve theorem for the constructed matrix.

Boundary RHS gathering, the constructed-matrix solve fit/error bounds and the
full constructed-factor-to-solve composition remain open, along with cleanup,
recovery/publication, the inverse endpoint and uniform time/live storage. S3
remains partial.

Validation: all 14,608 guarded stage-audit jobs pass, including six new explicit
workspace, padding and triangular solve axiom audits; combined peak 3.4 GiB.
The new module and stage root pass individual guarded checks at 2864.4 MiB
and 2956.8 MiB respectively. Source-integrity, plan-status and whitespace
checks pass. Proof limits are unchanged.

### Allocated numerical bounds for the computed boundary solve

`naturalLineSolve_sizes` proves solution and forward-substitution bounds for
an arbitrary natural-order integer band matrix, zero outside its finite rank
range. It uses the actual matrix's dominance invariant directly, without a
folded periodic matrix representation. The exact `exists_solver` theorem now
requires only a finite active set: its previously required ambient `Fintype`
instance was unused by the existing proof and is removed.

`boundary_line_execution_bits` and `boundary_line_roundoff_budget` show that
the retained execution precision also pays the triangular solve's stronger
perturbation budget. `boundary_line_allocated_sizes` specializes the natural
estimate to `factorRankIntegerMatrix`, deriving all precision, Newton-count
and perturbation premises from the allocated headers and the constructed
matrix invariant. A scaled RHS of grid norm at most `1/2` yields solution
values at most `8*p+1` and forward values at most `3*(8*p+1)+1`.

`naturalLineTables_factor` identifies the natural solve's multiplier columns,
upper columns and reciprocal records with the factorizer's emitted tables.
`naturalLineSolve_re` and `naturalLineSolve_im` identify its Gaussian runtime
solve with the scalar integer solve of each component. These are structural
identities, including the table counts; no numerical or execution oracle is
needed for this bridge.

The backward-head and coefficient fit bounds, gathered/scaled RHS construction,
full constructed-factor/solve composition, cleanup, recovery/publication and
the inverse endpoint remain open. Uniform fast time and complete simultaneous
live storage also remain open. S3 remains partial.

Validation: all 14,612 guarded stage-audit jobs pass, including nine new explicit
exact-solver, natural solve, allocated precision/size and table/projection axiom
audits. The solver generalization rebuilt dependents with combined peak 33.8 GiB;
the final stage build peaks at 3.4 GiB. Individual guarded checks of the five
new/revised proof modules peak at 2881.2 MiB or less; the final audit root
checks at 2956.8 MiB. Source-integrity, plan-status and whitespace checks pass.
Proof limits are unchanged.

### Allocated physical boundary triangular solve

`boundary_line_rcs_lower` proves that every actual computed reciprocal record
has grid value at least `1/4`. It identifies the record with its natural-rank
pivot, uses the allocated stage and Newton budgets, and pays the reciprocal
rounding error. `triangular_part_bounds` structurally bounds backward heads
from the computed solution and this positive reciprocal bound, for either
Gaussian component and arbitrary triangular tables.

`boundary_line_part` transfers the allocated scalar solution/forward bounds to
both Gaussian components. `boundary_line_allocated_rhsFits` derives all three
runtime RHS fit premises (forward heads, backward heads and rounded backward
outputs), and solution-record fits, from the matrix invariant and an input
component bound of `1/2`. It needs no per-step fit oracle.

`FacFits.tables` and `naturalLineTables_fits` derive every multiplier, upper
column and reciprocal coefficient fit from the existing factor-step proofs;
`naturalLineTables_widths` supplies their exact row widths.
`boundary_foldedSolve_allocated_runs` combines these facts with actual RHS
padding and both triangular passes. Every numerical fit premise is derived
from the constructed matrix invariant and the retained precision/Newton count.

`boundary_foldedSolve_physical_exec` executes that program on the fixed
224-tape factor bank. The gathered RHS port is consumed, the solution is
written on the output port, and all factor tables, control headers, endpoint
stacks, left stacks and every legacy tape are preserved. Its explicit time
bound is `4*N*w + 4*W*w + 8 + bandLinePassCost w N W`.

The caller still supplies the gathered/scaled RHS and the factor-bank layout.
Their full composition with constructed factorization, RHS gathering/scaling,
solve accuracy and recovery/publication remains open, as do cleanup, the
inverse endpoint and uniform fast time/simultaneous live storage. S3 remains
partial; kappa is unchanged.

Validation: all 14,619 guarded stage-audit jobs pass, including eleven new
explicit reciprocal, component/record-fit, coefficient-table and allocated
runtime/physical execution axiom audits. Combined build peak is 3.4 GiB.
All seven new modules and the audit root pass individual guarded checks:
new modules peak at 2865.5 MiB or less and the audit root at 2959.2 MiB.
Source-integrity, plan-status and whitespace checks pass. Proof limits are
unchanged.

### Generated folded RHS gather and physical gather/solve composition

`boundaryRhsWord_exec` decodes one rank's actual retained coordinate, copies
that word from the ambient RHS and retires the decoded coordinate. The
coordinate page, source line, rank, both widths and every lookup scratch tape
are restored. The cost includes coordinate lookup/decoding and source motion.

`boundaryRhsGather_exec` runs a descending rank clock. Each lookup prepends its
word, so the final stream is exactly the ambient RHS restricted to the natural
boundary rank order, without an extra output reversal. `boundaryRhsPrepare_exec`
generates this clock from the retained boundary-cardinality header and consumes
it completely. Neither a gather schedule nor a source-access execution oracle
is supplied.

`boundaryRhsPhysical_exec` places the gather on the fixed 224-tape bank, reads
the word width from the multiplier's retained width header, and writes directly
to the triangular RHS port (206). Every other physical stack is preserved,
including all factor tables, the source residual, the coordinate page and
retained masters. Its explicit bound is `boundaryRhsPrepareCost V w N s`.

`boundaryGatherSolve_exec` composes this actual gather with the allocated
physical triangular solve for an ambient RHS whose boundary components have
grid magnitude at most `1/2`. The vector is derived from the retained source
line and coordinate page, rather than supplied separately. It returns the
exact runtime solve of those gathered values, preserving all legacy tapes and
factor tables. The total paid bound is gather cost plus padding/triangular cost.

Normalization of the larger retained residual, full composition with the
constructed factorization, solve accuracy, cleanup and recovery/publication
remain open, together with the inverse endpoint and uniform time/live storage.
S3 remains partial; kappa is unchanged.

Validation: all 14,624 guarded stage-audit jobs pass, including seven new
explicit RHS lookup, gather, generated-clock, physical placement, state bridge
and gather/solve execution axiom audits. Combined build peak is 3.4 GiB. All
five new modules and the audit root pass individual guarded checks: new modules
peak at 2845.6 MiB or less and the audit root at 2961.8 MiB. Source-integrity,
plan-status and whitespace checks pass. Proof limits are unchanged.

### Physical residual normalization and normalized boundary solve

`normalizeBoundaryWord_bound` proves that the actual multiplier/truncation
`z ↦ tdivN q (z * 2^e)` sends component grid magnitude at most `2^E` into
`1/2` whenever `q = E+e+1`. `boundary_normalization_fits` derives source,
scalar and result fits at width `2*q+8`. The scalar's exact decoded value is
`2^(-(E+1))`; `normalizeBoundaryWord_scaled_error` bounds normalization error
against division by `2^(E+1)` by `2/2^q`.

`powerWordHeader_exec` constructs the encoded scalar from runtime width and
exponent headers, preserving those headers and its scratch. The structural
`boundary_normalize_runs` proof executes the real multiplier stream and restores
natural word order in place. Its explicit cost is
`N*(rmulCost w + 12*w + 8)+12`.

`boundaryNormalizePhysical_exec` composes scalar construction, in-place
normalization and scalar retirement on the fixed 224-tape bank. Its exact final
state changes only RHS port 206. The exponent header, factor tables, legacy
pages, endpoints, word-width header and every private scratch tape restore.

`boundaryNormalizeSolve_exec` composes this executed normalizer with the
allocated physical triangular solve. The caller supplies the raw residual's
component bound `2^E`, rather than a half-unit bound or a normalization-execution
oracle. The returned solution is the exact runtime solve of the actually
normalized residual words, with all numerical fit premises derived.

The exponent header is still a runtime input, with the proved relation
`q = E+e+1`. Generating it from retained magnitude/precision masters, composing
the raw gather and constructed factorization, unscaling/solve accuracy, cleanup,
recovery/publication and the inverse endpoint remain open. Uniform fast time
and complete simultaneous live storage also remain open. S3 remains partial;
kappa is unchanged.

Validation: all 14,629 guarded stage-audit jobs pass, including twelve new
explicit normalization bound/fit/error, runtime scalar construction, state/frame,
physical normalization and normalized-solve execution axiom audits. Combined
build peak is 3.4 GiB. All five new modules and the audit root pass individual
guarded checks: new modules peak at 2846.0 MiB or less and the audit root at
2964.7 MiB. Source-integrity, plan-status and whitespace checks pass. Proof
limits are unchanged.

### Generated normalization controls and raw boundary gather/normalize/solve

`boundary_normalization_precision` proves that half the allocated working
precision bounds the actual retained Schur residual's magnitude exponent. The
precision is even and at least two; half of it also exceeds the allocated
boundary-table accuracy by four bits. The normalization-roundtrip budget pays
amplification of the normalization rounding error by the inverse scale.

`boundaryNormalizationHeader_exec` generates the scalar exponent `q/2-1` by
halving retained precision counter 119 and dropping one tick. It preserves the
precision master and all scratch. `generatedBoundaryNormalize_exec` composes
header generation, scalar construction, actual in-place normalization, scalar
retirement and exponent-header retirement. Its exact final state changes only
RHS port 206. No exponent header is supplied by the caller.

`generatedBoundaryNormalizeSolve_exec` derives normalization readiness and its
half-unit input bound from the allocated precision and the retained residual
magnitude bound. `generatedBoundaryGatherSolve_exec` adds the actual restoring
ambient RHS gather. The vector, gather clock, normalization exponent and scalar
are all generated by the executed program. The returned solution is exactly
the triangular runtime solve of the actually normalized gathered residual.

The physical solve and generated callers now also expose their full factor-bank
frame, certifying preservation of private tapes outside the bank (including the
retired exponent header). Factor tables, source lines and all legacy tapes are
preserved, with explicit gather, setup, normalization and triangular costs.

Full composition with constructed factorization, unscaled solution accuracy,
executed unscaling, cleanup and recovery/publication remain open, together with
the inverse endpoint and uniform fast time/simultaneous live storage. S3 remains
partial; kappa is unchanged.

Validation: all 14,634 guarded stage-audit jobs pass, including nine new
explicit precision/magnitude/roundtrip-budget, generated-header, header-frame,
normalization and generated gather/solve execution axiom audits. The strengthened
physical and existing caller contracts also pass. Combined final build peak is
3.4 GiB. All eight new/revised proof modules and the audit root pass individual
guarded checks: proof modules peak at 2846.8 MiB or less and the audit root at
2965.5 MiB. Source-integrity, plan-status and whitespace checks pass. Proof
limits are unchanged.

### Constructed factorization-to-solve composition

The prepared factorizer now returns its solve-readiness record and physical
frame. The initialized and fully constructed factorizer contracts derive all
normalization scratch emptiness, the retained precision master and clean
multiplier bank from the actual setup and execution. The constructed result
also returns the computed rank-matrix invariant, rather than requiring it
again as a solve premise.

`boundaryFactor_solve_tables` identifies the emitted page's three factor tapes
with the natural-order triangular solve tables. `constructedBoundarySolve_spec`
composes the actual Schur table/input-page construction, generated physical
factorization, ambient residual gather, generated normalization and triangular
solve. Its column family and factors are produced by that execution; neither
matrix/factor data nor a solver execution is supplied by the caller.

The final solution port contains exactly the runtime solve of the normalized
retained residual restricted to folded boundary rank order. The contract keeps
column accuracy/format, the masked matrix-entry error and stability invariant,
the packed-table bound, exact coordinate/table prefixes and retained factors.
It preserves endpoints, all left stacks and every legacy tape except the owned
coordinate/table pages and their two headers. Normalization scratch is empty,
and clearing the solution port restores the solve-readiness record for reuse.
All costs are the composed, executed construction/setup/gather/solve bounds.

Unscaled solution accuracy and executed unscaling, factor/table retirement,
recovery/publication composition and the inverse endpoint remain open, as do
uniform fast time and complete simultaneous live storage. S3 remains partial;
kappa is unchanged.

Validation: all 14,636 guarded stage-audit jobs pass, including three new
explicit private-bank, factor-layout and constructed boundary-solve execution
axiom audits; all strengthened factorizer contracts remain audited. Combined
build peak is 7.9 GiB. All six new/revised proof modules and the audit root pass
individual guarded checks: proof modules peak at 2936.5 MiB or less and the
audit root at 2966.8 MiB. Added-source integrity, plan-status and whitespace
checks pass. Proof limits are unchanged.

### Executed exact unscaling of the constructed boundary solution

`boundary_unscale_product` proves that the existing fixed-point multiplier with
scalar numerator `2^(q+q/2+1)` computes multiplication by `2^(q/2+1)` exactly;
its truncation divides an exact multiple of `2^q`. `unscaleBoundaryWord_value`
identifies the decoded scale. `boundary_unscale_fits` proves that the coarse
solution component bound `8*p+1` still fits width `2*q+8` after unscaling under
`p ≤ q/2`, which follows from the allocated precision. The scalar also fits
that same word width.

The shared structural `boundary_scalarInPlace_runs` proof now supplies both
normalization and unscaling, restoring natural record order and every other
port. The existing normalization program definition is unchanged.
`boundaryUnscaleHeader_exec` generates the scalar exponent from the retained
precision master. `generatedBoundaryUnscale_exec` constructs the scalar,
executes exact in-place solution unscaling and retires the scalar, exponent
header and private scratch. Its exact final state changes only solution port
217, with all setup and multiplier costs charged.

The constructed solve now returns its derived solution length/component bounds,
precision master and clean multiplier bank. `constructedBoundaryUnscaledSolve_spec`
composes the actual table construction, factorization, raw RHS gather, generated
normalization, triangular solve and generated exact unscaling. Its returned
unscaled solution words all fit the original allocated width. Matrix/error
facts, owned page prefixes, factor tables and readiness after output retirement
are retained for recovery and cleanup; endpoints, left stacks and the existing
legacy frame are preserved.

Accuracy of the computed unscaled solution against the exact Schur solve,
factor/table retirement, recovery/publication composition and the inverse
endpoint remain open. Uniform fast time and complete simultaneous live storage
also remain open. S3 remains partial; kappa is unchanged.

Validation: all 14,644 guarded stage-audit jobs pass, including fourteen new
explicit exact-unscale, scalar/word-fit, shared scalar execution, generated
header/physical execution, solution-bound and constructed unscaled-solve axiom
audits. The strengthened solve and shared normalization proofs remain audited.
Combined build peak is 3.4 GiB. All ten new/revised proof modules and the audit
root pass individual guarded checks: proof modules peak at 2943.9 MiB or less
and the audit root at 2967.9 MiB. Added-source integrity, plan-status and whitespace
checks pass. Proof limits are unchanged.

### Natural-order computed-matrix forward error

`naturalLineSolve_error` now bounds the decoded integer solve against any exact
solution of the computed rank matrix, with half-unit RHS, by
`62000 (2p)^3 N^2 (2^-q (1 + 180 / β²))`. The proof transfers the actual window
factorization to the generic rounded band solve and checks agreement of the
machine's unguarded Newton rules with the analysed guarded rules. It uses the
existing precision assumptions, without the extra error-at-most-one premise
needed by the coarse size theorem. Empty boundaries are included.

The individual guarded check passes at 2838.8 MiB. All 14,645 guarded stage-audit
jobs pass, including the new explicit forward-error axiom audit; combined peak
is 3.4 GiB. This is the computed-matrix error only: perturbation from the exact
Schur matrix, normalized RHS error, and the final unscaled accuracy bound still
need composition. S3 remains partial and kappa is unchanged.

The same module now also proves `naturalLineSolve_perturbed_error`, combining
the integer solve's forward error with matrix row error ε and RHS error δ.
The additional error is `(δ + εX)/μ`, where μ is the computed matrix's dominance
margin and X bounds the original exact solution. The structural
`solves_perturbation_bound` proves this comparison directly through the residual
of the difference of the two exact solutions. It applies to arbitrary finite
active sets, including the empty set, and needs no matrix inverse representation.
The combined module passes its individual guarded check at 2841.8 MiB; the
structural comparison module passes at 1733.7 MiB. Specialization to constructed
Schur columns and the gathered normalized RHS remains required.

Validation of the combined error chunk: all 14,646 guarded stage-audit jobs
pass, including all three new explicit axiom audits. Combined peak is 3.4 GiB.
Plan-status and whitespace checks pass. Existing proof limits are unchanged.

### Allocated boundary accuracy and unscaled roundoff

`boundary_line_allocated_error` specializes the combined matrix/RHS error bound
to the constructed boundary rank matrix and canonical allocated precision. It
derives the degraded dominance invariant, Newton iteration budget, and numerical
smallness premises internally. Its individual guarded check peaks at 2835.0 MiB.
`boundary_line_roundoff_target` sharpens the existing unit-error estimate to an
arbitrary dyadic target. `boundary_line_error_precision` proves that the existing
allocated precision pays both this target and exact unscaling; consequently
`boundary_line_unscaled_roundoff_budget` bounds the unscaled solve-rounding term
by `2^-target`. This does not yet include matrix or RHS perturbation terms.
The budget module passes an individual guarded check below 2.8 GiB. No word
width, iteration count or proof limit was increased. S3 remains partial; kappa
is unchanged. The constructed Schur/RHS specialization, sharp solution magnitude,
recovery/cleanup and final time/storage bounds remain open.

Validation: all 14,648 guarded stage-audit jobs pass, including four new
allocated-error and unscaled-roundoff axiom audits. Combined build peak is
5.6 GiB. Plan-status and whitespace checks pass.

### Boundary-coordinate perturbation and scale transfer

`boundary_rank_row_error` transfers the constructed masked table's entrywise
accuracy ε to row accuracy `B.card * ε` for the actual integer rank matrix.
`boundary_rank_allocated_error` combines this with allocated Newton/solve error,
accepting the original boundary-coordinate matrix directly, pulled back by the
same `bFoldAt` indexing used by the physical solve. No independent rank-matrix
accuracy premise is needed. The module's individual guarded check peaks at
2823.8 MiB.

`boundary_normalized_rhs_error` propagates retained residual error δ through the
actual normalization word, yielding `2/2^q + δ/2^(E+1)`.
`boundary_unscaled_solution_error` transfers normalized solution error ε through
exact unscaling, yielding `2^(q/2+1) * ε`, with no added rounding. This module's
individual guarded check peaks at 2828.6 MiB. The final constructed endpoint
still needs to instantiate these lemmas for its actual Gaussian list components
and exact Schur solution, and combine the remaining perturbation budgets. S3
remains partial; recovery/retirement, uniform time and simultaneous live storage
remain open and kappa is unchanged.

Validation of the allocated/rank/scale error chunk: all 14,650 guarded
stage-audit jobs pass, including eight new explicit axiom audits. Combined build
peak is 5.5 GiB; each of the four added proof modules checks below 2.8 GiB.
Plan-status, added-source integrity and whitespace checks pass. Proof limits
are unchanged.

### Accuracy of the actual Gaussian solution list

`boundary_solution_part_error` transfers allocated rank-solve error to an actual
Gaussian list component using its structural projection identity.
`boundary_solution_norm_error` combines real and imaginary estimates into a
complex norm bound for the decoded output record, with at most twice the scalar
error bound. `boundary_solves_rank` reindexes an exact boundary solve in the
factorizer's actual folded order. `boundary_solution_coordinate_error` therefore
accepts exact real/imaginary solves on boundary coordinates directly and compares
output record i against `x (bFoldAt s B i)`. These results cover the actual
`bandSolveVec` list returned by constructed execution, rather than an independent
scalar solve. The individual guarded check peaks at 2839.6 MiB. Instantiation
with the actual normalized retained residual and combination of the remaining
perturbation budgets are still required. S3 remains partial; kappa is unchanged.

Validation: all 14,651 guarded stage-audit jobs pass, including four new
Gaussian-output and exact-coordinate reindexing axiom audits. Combined build
peak is 3.4 GiB. Plan-status and whitespace checks pass; proof limits are unchanged.

### Actual normalized residual through unscaled output accuracy

`boundary_normalized_rhs_spec` derives length, half-unit component bounds and
accuracy for the actual folded normalized residual list from the retained
residual's magnitude and error bounds. `boundary_normalized_solution_error`
feeds that list directly into the Gaussian-output accuracy theorem; no separate
normalized RHS oracle is required. `boundary_solves_div` scales exact boundary
systems structurally. `boundary_unscaled_solve_error` consequently compares the
computed unscaled Gaussian output word against an exact solution of the original
boundary-coordinate system. Its bound explicitly includes solve-rounding,
retained-RHS error, and constructed-matrix entry error. It uses the canonical
precision, Newton count, and actual normalized list throughout. The individual
normalized-solution and unscaled-solution modules check at 2824.7 MiB and
2833.2 MiB respectively; normalized RHS checks below 2.8 GiB.

The actual Schur-system execution endpoint still needs to instantiate this
combined theorem, simplify the three error contributions with retained column
and residual budgets, and derive the sharp solution magnitude needed by
recovery. Recovery/publication composition, retirement, uniform time and
simultaneous live storage remain open. S3 remains partial and kappa is unchanged.

Validation of the Gaussian-output/normalized-RHS/unscaled-error chunk: all
14,654 guarded stage-audit jobs pass, including eight new explicit axiom audits.
Combined build peak is 3.4 GiB; individual added modules check below 2.8 GiB.
Plan-status, added-source integrity and whitespace checks pass. Proof limits
are unchanged.

### Cancelled scale and polynomial perturbation budget

`boundary_unscaled_error_identity` cancels the inverse normalization scale from
the retained RHS and matrix perturbation terms exactly.
`boundary_unscaled_total_error_budget` bounds the complete scalar expression by
`2/2^target + 32p (2^-bits + δ + N ε X)`, using the existing canonical precision
and normalization budgets. `boundary_perturbation_target` proves that the
perturbation summand is at most `2^-(target+1)` when row error and retained RHS
error meet `boundaryErrorBits` and the original exact boundary solution obeys
`X ≤ 16p·2^rhsExp`. Thus these hypotheses give total error at most
`3·2^-target`, without exponential amplification of the matrix or residual error.
The module's individual guarded check peaks at 2851.9 MiB. The constructed
endpoint must still establish the stable exact-solution bound and retained RHS
budget, instantiate the combined numerical theorem and derive the magnitude for
recovery. S3 remains partial; kappa is unchanged.

Validation: all 14,655 guarded stage-audit jobs pass, including three new explicit
scale-cancellation and total-error-budget axiom audits. Combined peak is 3.4 GiB.
Plan-status and whitespace checks pass. Proof limits are unchanged.

### Dyadic solve target and stable recovery magnitude

`boundary_unscaled_solve_target` combines the complete actual normalized solve
with the polynomial budgets: entry error `2^-boundaryTableBits`, retained RHS
error `2^-boundaryErrorBits`, and exact solution magnitude `16p·2^rhsExp` imply
unscaled output error at most `3·2^-target`. The theorem refers directly to the
actual Gaussian solution word and exact boundary-coordinate system. It checks
individually at 2834.3 MiB.

`dominant_complex_solution_bound` derives the required exact magnitude from the
two real solves and dominance. `phaseCell_exact_solution_bound` specializes it
to the original phase-cell matrix using its proved gap, independently of the
larger retained residual. `boundary_computed_solution_magnitude` shows that an
output with the proved dyadic error fits the existing
`stableInteriorExponent p rhsExp`; recovery sizing therefore need not absorb
the normalization scale. The magnitude module checks at 1948.7 MiB.

The constructed Schur execution endpoint must still identify the restricted
full solution and instantiate its retained residual error, then use these
theorems to close accuracy and magnitude in its postcondition. Recovery,
retirement, uniform time and simultaneous live storage remain open. S3 remains
partial and kappa is unchanged.

Validation of the total-budget/dyadic-target/stable-magnitude chunk: all 14,657
guarded stage-audit jobs pass, including seven new explicit axiom audits.
Combined peak is 3.4 GiB; individual modules remain below 2.8 GiB. Plan-status,
added-source integrity and whitespace checks pass. Proof limits are unchanged.

### Native retained Schur postconditions imply numerical output accuracy

`boundary_exact_schur_solves` identifies the restricted principal-system solution
as an exact solution of the reduced boundary matrix. The retained residual's
weighted real error at the column target implies the needed boundary RHS budget
via `boundary_retained_rhs_budget`; `boundary_retained_rhs_accuracy` transfers
that real residual error to the complex norm used by the Gaussian solve.

`boundary_real_schur_target` combines these adapters with the actual normalized
Gaussian solve and exact unscaling. Its premises match native retained Schur
postconditions: original principal-system solve, dominance, input magnitude,
computed column accuracy, retained residual realness/magnitude and weighted
residual error. It derives the exact solution magnitude internally and proves
unscaled output error at most `3·2^-target`. No separate reduced-system solve,
complex residual oracle or exact solution magnitude premise remains. The two
modules check individually at 2836.5 MiB and 2840.3 MiB.

The execution endpoint must still instantiate the principal sets and run matrix,
align retained-residual and constructed-column precision, and attach the result
to its actual output postcondition. Recovery/retirement, uniform time and
simultaneous live storage remain open. S3 remains partial; kappa is unchanged.

Validation: all 14,659 guarded stage-audit jobs pass, including four new explicit
Schur/retained-RHS/native-target axiom audits. Combined peak is 3.4 GiB.
Plan-status and whitespace checks pass; proof limits are unchanged.

### Constructed execution returns accurate boundary output

`constructedBoundaryUnscaledSolve_spec` now includes a numerical postcondition
for the actual returned `solution` list and native tape 217. From an exact solve
on `haloVertices`, the retained residual's native realness and weighted error,
and the original RHS magnitude, it proves output record i is within
`3·2^-target` of the exact solution at `bFoldAt i`, and its decoded magnitude is
at most `2^stableInteriorExponent p rhsExp`. The theorem instantiates actual
constructed columns, their entry error and rank invariant; uses the proved
interior/boundary partition and dominance; and relates the mapped unscale list
to the actual output record. Execution, time, frame, factor tables and scratch
cleanup postconditions are preserved. The strengthened module's individual
guarded check peaks at 2940.9 MiB.

This closes conditional accuracy and recovery magnitude for the executed
constructed solve. Composition with the residual-producing execution, including
precision/header alignment, remains open. Boundary publication, retained
recovery, factor/table/page retirement, uniform time and simultaneous live
storage remain open. S3 remains partial and kappa is unchanged.

Validation of the native-Schur/constructed-output accuracy chunk: all 14,659
guarded stage-audit jobs pass, including four new native Schur adapter/target
axiom audits and the strengthened constructed solve audit. Combined peak is
3.4 GiB; individual new modules and the strengthened execution module remain
below 3 GiB. Plan-status, added-source integrity and whitespace checks pass.
Proof limits are unchanged.

### Physical two-output residual handoff

`exec_emb_two_outputs` structurally lifts a two-output execution through an
injective tape embedding, with its exact complete physical frame.
`boundary_retained_residual_lift` applies it through the arithmetic, table and
legacy embeddings used by the constructed boundary solver. The retained
residual's updates become exactly physical tapes 110 and 132; every other tape,
all left stacks, and I/O are unchanged, with the same execution step count and
preserved user state. This keeps the retained interior stream and larger-bank
workspace suitable for the next stage without supplying an independent frame
oracle. The individual guarded check peaks at 2900.4 MiB.

The next composition still must transport the retained residual's readiness
through these physical updates, instantiate its precision at the constructed
column target and join the two actual executions. Publication/recovery,
retirement, uniform time and simultaneous live storage remain open. S3 remains
partial and kappa is unchanged.

Validation: all 14,660 guarded stage-audit jobs pass, including two new explicit
two-output/physical-residual-lift axiom audits. Combined peak is 3.4 GiB.
Plan-status and whitespace checks pass. Proof limits are unchanged.

### Physical retained residual with readiness preserved

`embStk_updateR_inner` and `boundary_retained_project_outputs` prove that the
physical two-output poststate projects exactly to the native residual poststate.
`physicalRetainedSchurResidual_spec` now executes the complete retained residual
in the same 224-tape bank and procedure-table embedding as the constructed
boundary solve. It returns the actual interior and residual fields, exact
interior solver, weighted Schur residual accuracy, realness, magnitude and
published-read guarantees. Its physical state changes exactly 110 and 132, and
its final `LengthKeyReady` is transported to the actual physical poststate.
The native step bound and user state are preserved. The individual guarded
check peaks at 2909.0 MiB; the updated lift/projection module peaks at 2901.8 MiB.

Joining this physical execution with the constructed solve, at the column
target and common precision, remains open. Publication/recovery, retirement,
uniform time and simultaneous live storage remain open. S3 remains partial;
kappa is unchanged.

Validation of the physical residual handoff chunk: all 14,661 guarded stage-audit
jobs pass, including five new explicit lift/projection/physical-residual axiom
audits. Combined peak is 3.4 GiB; both added modules check below 3 GiB.
Plan-status, added-source integrity and whitespace checks pass. Proof limits
are unchanged.

### Executed retained residual and accurate constructed boundary solve

`retainedBoundarySolve_spec` now composes the actual physical retained Schur
residual execution with constructed columns, factorization, gather,
normalization, triangular solve and exact unscaling. Both stages use the same
column target and canonical precision. The starting RHS is bounded by four,
matching the boundary constructor's normalized arithmetic interface. The
residual's actual magnitude, realness, weighted error and transported readiness
supply all boundary-solve premises internally; no supplied residual field or
residual accuracy oracle remains.

The composed theorem returns the actual encoded solution on tape 217, exact
retained interior and residual stream prefixes on 132 and 110, output length and
word fit, user state, complete I/O/left frame, legacy frame outside owned ports,
precision master, clean multiplier bank and private scratch emptiness. For any
exact principal-system solution of the decoded original real RHS, it proves
output error `3·2^-target` and the existing stable recovery magnitude. The cost
is the sum of the two proved execution bounds. Its individual guarded check
peaks at 2924.7 MiB.

This closes the residual-to-accurate-boundary execution composition for the
normalized real RHS interface. Boundary publication/unfolding, retained recovery,
factor/table/page retirement, full inverse assembly, uniform time and complete
simultaneous live storage remain open. S3 remains partial and kappa is unchanged.

Validation: all 14,662 guarded stage-audit jobs pass, including the new explicit
composed retained-boundary execution axiom audit. Combined peak is 3.4 GiB;
the new module checks below 3 GiB. Plan-status, added-source integrity and
whitespace checks pass. Proof limits are unchanged.

### Real ambient boundary field for recovery

`boundarySolutionField` unfolds the actual computed folded solution list using
`bFoldPos`, takes each word's real part and fills the complement of the boundary
with zero. Structural theorems prove realness everywhere, zero support off the
boundary, word fit from the actual list, boundary-coordinate accuracy from the
proved folded output error, and the same global stable magnitude. The
published-read theorem proves that an encoded ambient stream of this field has
exactly the recovery read semantics. The final individual guarded check peaks
at 2904.6 MiB.

This is the numerical/encoding interface for publication; an actual program
still must materialize that ambient stream from the computed list. Recovery
precision alignment, publication/recovery execution, retirement, full inverse
assembly, uniform time and simultaneous live storage remain open. S3 remains
partial and kappa is unchanged.

Validation: all 14,663 guarded stage-audit jobs pass, including six new explicit
ambient-boundary-field axiom audits. Combined peak is 3.4 GiB. Plan-status and
whitespace checks pass; proof limits are unchanged.

### Executed inverse folding of computed boundary values

`boundary_unfold_physical_exec` reuses the structural inverse-fold machine in
the physical factor bank. With its half-count/parity headers and scratch ready,
it consumes the computed folded solution on tape 217 and puts natural boundary
order on tape 204, preserving every other physical tape. Its time is at most
`60 (N+1) w + 60 N + 60`. `boundary_unfold_field` identifies the real projection
of this actual output with the recovery field in ascending `bOrder` coordinates.
`boundaryFactorFr_two_updates` proves the complete physical two-port frame from
the virtual run. The new module checks individually at 2906.4 MiB.

Generation/retirement of inverse-fold counters, real projection, zero ambient
initialization and actual scatter publication remain open. Recovery precision
alignment, complete recovery/cleanup, full inverse assembly and final resource
bounds remain open. S3 remains partial and kappa is unchanged.

Validation of the recovery-field/inverse-fold chunk: all 14,664 guarded
stage-audit jobs pass, including nine new explicit field, ordering and physical
inverse-fold axiom audits. Combined peak is 3.4 GiB; both new modules check below
3 GiB. Plan-status, added-source integrity and whitespace checks pass. Proof
limits are unchanged.

### Generated and retired physical inverse-fold controls

`boundaryUnfoldCounters_exec` builds half-count and parity headers on 189/191
from the retained boundary count on 116 in at most `16N+22` steps, restoring
its private scratch. `generatedBoundaryUnfold_exec` composes those controls with
the actual inverse-fold program and retires them afterward. Its exact physical
poststate changes only the folded source 217 and natural-order destination 204.
`preparedBoundaryUnfold_exec` first retires obsolete factor header/destination
tapes 189/191/198/204, charging their actual lengths, then executes generated
unfolding. It therefore accepts arbitrary old factor headers rather than
requiring externally supplied controls or blank obsolete headers. The count
and word-width masters are retained. The counter module checks at 1823.5 MiB;
the complete generated/prepared module checks at 2924.1 MiB.

Real projection, zero ambient initialization and scatter publication still need
actual execution and composition with the solved state. Recovery precision
alignment, complete recovery/cleanup, inverse assembly and final resource
bounds remain open. S3 remains partial and kappa is unchanged.

Validation: all 14,666 guarded stage-audit jobs pass, including three new explicit
counter/generated/prepared-unfold axiom audits. Combined peak is 3.4 GiB; both
new modules check below 3 GiB. Plan-status, added-source integrity and whitespace
checks pass. Proof limits are unchanged.

### Actual retained solve followed by generated inverse folding

`retainedBoundarySolve_spec` now exposes its already-proved restored solve
workspace and exact boundary count. `retainedBoundaryRealUnfold_spec` consumes those
facts to compose the actual residual, constructed solve, exact unscale, obsolete
header retirement, generated counters and physical inverse-fold executions.
Natural boundary order is returned on tape 204 and tape 217 is empty. The
retained residual and interior prefixes on 110/132 and I/O/left frame are
preserved. The actual intermediate solve execution is included as a witness,
so the charged retirement lengths refer to the reached machine state. The time
bound adds those actual retirement lengths and the proved generated unfold
cost; uniform bounds on those lengths remain required.

The theorem also returns the recovery field's boundary accuracy, global stable
magnitude and word fit directly from its actual computed solution. The new
module checks individually at 2923.3 MiB; the strengthened solve module checks
at 2922.4 MiB. Actual real projection and ambient scattering, recovery precision
alignment/composition, retirement, inverse assembly and final uniform resource
bounds remain open. S3 remains partial; kappa is unchanged.

Validation: all 14,667 guarded stage-audit jobs pass, including the new explicit
retained-solve/unfold axiom audit and strengthened solve audit. Combined peak
is 3.4 GiB. Plan-status and whitespace checks pass; proof limits are unchanged.

### Executed real projection on the retained boundary path

`boundaryRealProjection_exec` generates the owned byte count from boundary count
116 and word width 160, projects the stream on 204 in place, preserves its
borrowed suffix and retires all private count/scratch. Its time is at most
`N (12w+9)+12`. `boundaryRealUnfold_exec` composes generated inverse folding and
real projection and identifies the encoded physical output with
`(bOrder s B).map (boundarySolutionField B solution)`.

The main new wrapper is `retainedBoundaryRealUnfold_spec`: it now composes
retained residual production, accurate constructed solve, unscaling, inverse
folding and actual real projection. Tape 204 holds the recovery field's values
in ascending boundary order. The retained interior/residual prefixes and
I/O/left frame are preserved; recovery-field accuracy, stable magnitude and
word fit are proved. Only this complete real-output wrapper is retained, with
no intermediate unfold-only wrapper. Individual checks peak at 2915.6 MiB for
projection, 2904.9 MiB for real unfolding and 2923.9 MiB for retained composition.

Ambient scatter publication and its generated controls, recovery precision
alignment/composition, complete retirement, inverse assembly and final uniform
time/live-storage bounds remain open. S3 remains partial; kappa is unchanged.

Validation of the retained-solve/real-unfold chunk: all 14,669 guarded stage-audit
jobs pass, including three new explicit projection/real-unfold/retained-path
axiom audits and the strengthened solve audit. Combined peak is 3.4 GiB; all
new and revised modules check below 3 GiB. Plan-status, added-source integrity
and whitespace checks pass. Proof limits are unchanged.

### Sparse ambient boundary scatter

`boundaryScatterOrigins` and `boundaryScatterGaps` give the disjoint one-word
publication schedule in ascending boundary order. Structural theorems prove
fit, exact length, word scaling and total gap volume. `boundary_scatter_field`
shows that scattering the packed boundary values into a zero line realizes the
zero-extended ambient field exactly; `boundary_scatter_cstream` proves the same
identity for the actual integer-word encoding.

`boundaryScatter_exec` executes that publication through the existing scatter
machine. With its gap controls and zero ambient prefix ready, it consumes the
packed source prefix, preserves the borrowed source/output suffixes, and writes
exactly the encoded ambient field. Its proved time is at most `35sw+6`.
Individual checks peak at 2920.6 MiB for data/order/encoding and 2898.4 MiB for
execution. Actual generation of the delimited controls and zero ambient prefix,
and composition with the retained solved state, remain open. Recovery precision
alignment/composition, complete retirement, inverse assembly and final resource
bounds remain open. S3 remains partial; kappa is unchanged.

Validation: all 14,671 guarded stage-audit jobs pass, including ten new explicit
boundary scatter data/encoding/execution axiom audits. Combined peak is 3.4 GiB;
both added modules check below 3 GiB. Plan-status, added-source integrity and
whitespace checks pass. Proof limits are unchanged.

### Generated zero ambient prefix and sparse publication

`boundaryPublish_exec` composes the existing structural zero-word initializer
with actual sparse boundary scatter. It generates an s-word zero ambient prefix
from retained dimension 121 and word width 160, then writes the ascending
boundary values into it. The packed prefix on 204 is consumed, its borrowed
suffix restores, and tape 132 receives exactly the encoded ambient boundary
field above its original retained contents. All count and initialization scratch
restore. Its time is at most `54sw+16`; the individual guarded check peaks at
2921.1 MiB. This removes the caller-supplied zero-prefix premise.

The delimited scatter controls are still supplied. The existing origin-advance
and publication-control converter is the next route for generating them from
retained coordinates. Coordinate preparation/control generation, composition
with the solved state, recovery precision alignment/composition, full retirement,
inverse assembly and final resource bounds remain open. S3 remains partial and
kappa is unchanged.

Validation: all 14,672 guarded stage-audit jobs pass, including the new explicit
zero-initialized boundary publication axiom audit. Combined peak is 3.4 GiB.
Plan-status and whitespace checks pass; proof limits are unchanged.

### Origin-advance conversion and locally cleaned publication

`boundaryPublicationGaps` identifies the exact boundary scatter schedule with
publication gaps of ascending origin advances. The advance-volume bound is at
most `sw`. `boundaryPublicationControls_nonempty_exec` runs the existing converter
on the physical boundary bank, restoring the source advances and count and
emitting the exact scatter controls in at most `33sw+21` steps.
`conditionalBoundaryPublicationControls_exec` handles both empty and nonempty
boundaries with bound `33sw+23`.

`controlledBoundaryPublish_exec` composes conversion, generated zero ambient
initialization, actual sparse scattering and control retirement. Only the packed
source prefix and ambient destination change: tape 204's borrowed suffix
restores and tape 132 receives the encoded recovery field above its original
contents. Origin advances, count, masters and scratch restore. Its total time is
at most `89sw+41`. Individual checks peak at 2930.4 MiB for converter/empty case
and 2926.7 MiB for the complete controlled publisher.

The origin-advance stream remains supplied. Preparation of retained coordinates
and generation of those advances, composition with the solved state, recovery
precision alignment/composition, complete retirement, inverse assembly and final
uniform resource bounds remain open. S3 remains partial; kappa is unchanged.

Validation of the generated-zero/control-conversion/publication chunk: all
14,674 guarded stage-audit jobs pass, including six new explicit publication
axiom audits. Combined peak is 3.4 GiB; all three new modules check below 3 GiB.
Plan-status, added-source integrity and whitespace checks pass. Proof limits
are unchanged.

### Direct coordinate-to-advance runtime step

The binary table advance generator needs a workspace fitting scaled coordinates,
while the retained coordinate page guarantees only coordinate width. The direct
unary route avoids enlarging that binary page. `takeNaturalCoordinate_exec`
consumes one actual encoded coordinate word, preserves the remaining packet
queue and width, appends its unary value and restores all conversion scratch,
with cost at most `6x+23V+18`.

`boundaryAdvancePacket_exec` computes the difference from the previous coordinate,
scales it by retained word width, emits a reversed delimited packet, updates the
cursor, and clears all local scratch. `boundaryAdvanceNext_exec` composes the
reader and packet emission into one fixed runtime step, changing only the
coordinate source, previous-coordinate header and packet accumulator. Its bound
is `x(10w+29)+23V+43`. It needs no scaled-coordinate binary-fit hypothesis.
Individual checks peak at 1819.8 MiB for the reader and 1888.2 MiB for packet and
complete step.

The counted loop and final stream reversal/terminal delimiter still need
execution and composition with natural retained coordinates. Coordinate-page
preparation, recovery composition/cleanup, inverse assembly and final resource
bounds remain open. S3 remains partial; kappa is unchanged.

Validation: all 14,676 guarded stage-audit jobs pass, including three new explicit
coordinate-reader/advance-packet/combined-step axiom audits. Combined peak is
3.4 GiB; both added modules check below 2 GiB. Plan-status, added-source integrity
and whitespace checks pass. Proof limits are unchanged.

### Counted coordinate loop and finalized origin advances

`boundaryAdvanceLoop_exec` proves the structural runtime loop over any ascending
encoded coordinate list, including empty input. It consumes the owned page
prefix and count, emits the reversed advance controls and leaves the cursor at
the last coordinate, preserving the remaining tape frame.
`generateBoundaryAdvances_exec` snapshots/restores the unary boundary count,
executes the counted loop, clears the cursor, reverses the packet accumulator,
and adds the terminal delimiter. Only coordinate source 109 and advance output
206 change; borrowed coordinate/output suffixes are preserved and all local
scratch restores. The generated stream is exactly
`gatherControls (originAdvances w 0 origins ++ [0])`.

The closed time bound is `N (bound (10w+29)+23V+54)+2 bound (w+1)+13`.
The direct route uses the retained coordinate width and unary scaling, requiring
no binary workspace for scaled offsets. Individual checks peak at 1926.4 MiB
for the loop and 1993.2 MiB for the complete generator. The folded retained
coordinate page still needs to be converted to ascending order and fed to this
generator; composition with publication/recovery and final cleanup/resource
bounds remain open. S3 remains partial; kappa is unchanged.

Validation: all 14,678 guarded stage-audit jobs pass, including two new explicit
coordinate-loop/finalized-advance-generator axiom audits. Combined peak is
3.4 GiB; both added modules check below 2 GiB. Plan-status, added-source integrity
and whitespace checks pass. Proof limits are unchanged.

### Retained coordinate-page preparation

`boundaryCoordinateUnfold_exec` reuses the generated inverse-fold program through
a finite tape permutation: coordinate source 109 and geometry width 115 replace
the solution source/width ports, while natural output goes to 206. The proof
establishes the exact physical poststate, preserving the solution words on 204,
arithmetic width on 160 and all unrelated tapes. Old auxiliary headers are
retired with their actual lengths charged. `embOvr_equiv_project` supplies the
structural full-bank lifting argument.

`unfoldList_foldList` proves the inverse-fold identity over arbitrary lists;
`boundary_unfold_coordinates` identifies the actual coordinate page with
ascending `bOrder`. `prepareBoundaryCoordinates_exec` then restores that ascending
encoded page to tape 109 using two reversals and leaves 206/217 empty. This is
the input expected by the direct coordinate-to-advance generator. Individual
checks peak at 2921.0 MiB for physical coordinate unfolding, 2711.1 MiB for the
structural ordering proof and 2909.8 MiB for complete preparation.

Composition of coordinate preparation, advance generation and publication with
the retained solved state remains open, followed by recovery precision
alignment/composition, complete retirement, inverse assembly and final resource
bounds. S3 remains partial; kappa is unchanged.

Validation: all 14,681 guarded stage-audit jobs pass, including six new explicit
coordinate-permutation/lift/order/preparation axiom audits. Combined peak is
3.4 GiB; all three added modules check below 3 GiB. Plan-status, added-source
integrity and whitespace checks pass. Proof limits are unchanged.

### Fully generated ambient publication from retained coordinates

`boundaryCoordinatePackets` identifies the actual ascending coordinate encoding
with the runtime reader's packets. `boundaryOriginAdvances_exec` specializes the
complete generator to the actual boundary order, deriving sorting, length and
coordinate bounds from boundary membership and the retained geometry width.
`generatedBoundaryPublish_exec` consumes that page, generates all origin advances
and scatter controls, initializes the zero ambient line, publishes the boundary
field and retires both control streams. It preserves borrowed coordinate/value
suffixes and every unrelated physical tape, with time at most
`generateBoundaryAdvancesCost N V w s + 93sw + 45`.

`preparedBoundaryPublish_exec` adds actual inverse folding of the retained
coordinate page. Its inputs are the folded coordinate page, ascending boundary
values and ordinary dimension headers; it needs no supplied origin advances,
scatter schedule or zero prefix. Tape 132 receives exactly the ambient recovery
field above its retained contents, while owned coordinate and packed-value
prefixes are consumed. Obsolete header retirement is charged by actual lengths.
Individual checks peak at 2905.9 MiB for boundary-specific advances, 2930.6 MiB
for generated publication and 2926.4 MiB for complete preparation/publication.

Composition with the retained solved-state endpoint, recovery precision
alignment/composition, complete retirement, inverse assembly and uniform final
time/live-storage bounds remain open. S3 remains partial; kappa is unchanged.

Validation: all 14,684 guarded stage-audit jobs pass, including four new explicit
coordinate-encoding/boundary-advance/generated/prepared-publication axiom audits.
Combined peak is 3.4 GiB; all three new modules check below 3 GiB. Plan-status,
added-source integrity and whitespace checks pass. Proof limits are unchanged.

### Retained solve through accurate ambient boundary publication

The physical handoff now exposes its derived `BoundaryPublicationReady`
certificate: retained ambient master, arithmetic/geometry widths, exact unary
boundary count, clean multiplier bank and publication scratch. Publication uses
ambient master 121, which the actual `LengthKeyReady` interface retains; arithmetic
header 97 is transient. The folded coordinate page and readiness are carried
through the executed real unfold.

`retainedBoundaryPublished_spec` composes actual retained residual production,
constructed columns/factors/solve, exact unscaling, real unfolding, coordinate
preparation, advance/control generation, zero initialization and ambient scatter
publication. Tape 132 contains exactly the ambient boundary field above the
retained table/interior stream. Owned coordinate and packed-value tapes are
empty; the residual stream, I/O and left frame are preserved. Published reads
have proved boundary error `3·2^-target`, and the published field is real with
the existing stable recovery magnitude. Cost witnesses include the actual solve
and unfold predecessor states, so header retirement is charged at reached tape
lengths. Uniform bounds on these lengths remain required.

Individual guarded checks peak at 2822.5 MiB for the handoff certificate,
2925.0 MiB for the strengthened solve, 2929.1 MiB for real unfolding and
2947.4 MiB for the composed ambient endpoint. Recovery precision alignment and
composition, complete retirement, inverse assembly and uniform final time/live
storage remain open. S3 remains partial; kappa is unchanged.

Validation: all 14,686 guarded stage-audit jobs pass, including the new explicit
retained ambient-publication axiom audit and strengthened handoff/solve audits.
Combined peak is 3.4 GiB; new and strengthened handoff/endpoint modules check
below 3 GiB. Plan-status, added-source integrity and whitespace checks pass.
Proof limits are unchanged.

### Shared boundary/recovery precision alignment

Recovery accuracy is now independent of its finer working target.
`recoveryPublishedHalo_tolerance_at_precision` and the retained-register version
execute with any working target at least the requested output target, while
requiring only the boundary tolerance allocated for that output target. Existing
same-target interfaces specialize these theorems. The generic error budget
separates interior approximation, arithmetic roundoff and boundary error.

`boundaryRecoveryTarget` reserves two solve bits beyond `recoveryTarget`.
The proved `3·2^-solveTarget` boundary error then meets recovery's tolerance.
`boundaryRecovery_published_error_budget` combines this error with the actual
`initialSchurTarget` arithmetic bank and proves the requested halo error. No
precision conversion or additional runtime program is required.

The numerical precision mismatch is resolved. Carrying `LengthKeyReady` through
the published physical endpoint and composing the actual recovery execution
remain open, followed by complete retirement, inverse assembly and uniform final
time/live-storage bounds. S3 remains partial; kappa is unchanged.

Validation: all 14,687 guarded stage-audit jobs pass, including seven explicit
new precision/alignment/error-budget audits. Final incremental combined peak is
3.4 GiB. Individual checks peak at 2002.2 MiB for recovery tolerance and
1998.4 MiB for retained recovery, and 1948.2 MiB for the boundary/recovery
budget. Source-integrity, whitespace and plan-status
checks pass. Proof limits are unchanged.

### Executed retained boundary solve through full halo recovery

The ordinary arithmetic `LengthKeyReady` invariant now follows from the physical
boundary frame. Real unfolding exposes that frame; ambient publication carries
it through and restores the recovery masters and required scratch. The published
boundary field also exposes its word-fit certificate for physical readback.

`physicalRecoveryPublishedHalo_at_precision` lifts recovery into the full
224-tape bank with exact updates on 110 and 132 and preserves every other tape.
`retainedBoundaryRecovered_spec` composes the actual retained residual, constructed
boundary solve, unscale/unfold, generated ambient publication and recovery.
With the allocated boundary solve target, the physical published halo reads have
error at most `2^-target` against every exact real principal solution. Both solve
and unfold predecessor executions are retained in the cost certificate, and the
recovery cost is added to the actual publication execution cost.

The residual on 110 and table/initial-interior streams below the recovered output
on 132 are still owned data. Complete retirement, real/imaginary assembly and
uniform final time/live-storage bounds remain open. This is a real-component
execution endpoint, not the complete S3 inverse. S3 remains partial; kappa is
unchanged.

Validation: all 14,690 guarded stage-audit jobs pass, including explicit physical
readiness, lifted recovery and composed recovery axiom audits. Combined peak is
3.4 GiB. Proof limits are unchanged.
Individual guarded checks peak at 2904.2 MiB for readiness transport, 2911.5 MiB
for physical recovery, 2957.4 MiB for the strengthened publication endpoint and
2941.2 MiB for composed recovery. Source-integrity, whitespace and plan-status
checks pass.

### Retire packed table and initial interior below recovered output

`retirePackedBandTable_exec` consumes the actual clipped packed page in reverse
column order from retained row-count, band-width and word-width headers. The
counted-loop invariant now exposes the remaining count after its pop; the former
loop theorem specializes the stronger structural proof. Each column's byte clock
is generated from its clipped interval, checked once, used for prefix retirement
and released. All scratch and the borrowed suffix are restored.

`retirePublishedBoundary_exec` parks the recovered ambient prefix on an empty
tape, retires the table and initial-interior prefix below it, and restores the
recovered prefix over the original borrowed suffix. Its cost is the explicit
column-retirement sum plus `18*s*w+9*s+18`. The reached solved/unfolded/published
states carry a derived `BoundaryRetirementReady` certificate; no new runtime data
are supplied by the specification.

`retainedBoundaryRecovered_spec` now executes this retirement after actual halo
recovery. Tape 132 contains the recovered real line directly above its original
suffix, with the same proved `2^-target` error. The residual stream on 110,
remaining factor/header bank retirement, real/imaginary assembly and uniform
final time/live-storage bounds remain open. S3 remains partial; kappa is unchanged.

Validation: all 14,695 guarded stage-audit jobs pass, including five explicit
new counted-loop/column/step/table/published-retirement axiom audits. The broader
rebuild peaks at 34.4 GiB combined; the final incremental audit peaks at 3.4 GiB.
Individual checks of the four retirement modules peak at 1930.6, 1916.5, 1924.8
and 1937.9 MiB. Source-integrity, whitespace and plan-status checks pass. Proof
limits are unchanged.
The retirement certificate, strengthened unfold/publication endpoints, composed
recovery endpoint and generalized counted loop check at 2814.7, 2963.3, 2975.9,
2946.8 and 1319.0 MiB respectively; every changed module stays below 3 GiB.

### Restored real-component workspace and executed component transition

`releaseBoundaryWorkspace_exec` retires the final ambient residual on 110 and
clears all owned boundary headers/factor tapes, charging their actual reached
lengths. The strengthened `retainedBoundaryRecovered_spec` now restores the
entire initial stack bank except the recovered real output prefix on 132. The
original RHS on 110, parked components, borrowed suffixes, I/O and left stacks
are restored exactly; the published error remains at most `2^-target`.

`cleanComponentTransition_exec` switches inputs after this restored real solve:
it retires the old RHS, parks the real output on 145, installs the next component
from 144 and releases its counters. Its explicit cost is
`24*s*(2*q+8)+9*s+12*q+52`. `retainedBoundaryTransition_spec` executes the complete
retained solve/recovery/release and this transition, proving the saved real
result's physical read accuracy and the ordinary `LengthKeyReady` invariant for
the next component. Parked registers lie outside the arithmetic image.

Second-component execution/complex pairing and original-input restoration still
need composition with these generated solver endpoints. Uniform final time and
simultaneous live-storage bounds also remain open, including bounds for the
actual retirement lengths. S3 remains partial; kappa is unchanged.

Validation: all 14,698 guarded stage-audit jobs pass, including four explicit new
release/switch/projection/composed-transition axiom audits. Combined peak is
3.4 GiB. Individual guarded checks peak at 1908.6 MiB for release, 1826.8 MiB for
clean switching, 2969.1 MiB for the restored solve, 2947.0 MiB for the composed
transition and 2908.0 MiB for projection/readiness. Source-integrity, whitespace
and plan-status checks pass. Proof limits are unchanged.
The strengthened published-frame module checks at 2973.2 MiB; every changed
module remains below 3 GiB.

### Executed second component and complex pairing with restored original input

The existing native pairing proof now lifts into the physical 224-tape bank via
an injective register embedding; its procedure-free execution is reused directly.
`cleanFinishComponents_exec` consumes the second RHS, pairs the saved real stream
with the recovered imaginary stream, releases the saved result and restores the
original input from 146. Borrowed suffixes and all other tapes are restored. Its
explicit cost is `34*s*(2*q+8)+9*s+12*q+60`.

`retainedBoundaryFinish_spec` executes the generated second-component solve,
recovery and workspace release before pairing. Two component error allocations
of `2^-(target+1)` yield physical complex error at most `2^-target`; pairing uses
actual decoded words without an extra fit hypothesis. The reached predecessor
states and the second solve's explicit stage cost bounds remain exposed.

`retainedBoundaryPair_spec` composes the actual first-component transition and
second-component finish. From prepared real/imaginary inputs and a saved original
page, it executes both generated solves, publishes the paired complex halo line,
restores the original source on 110 and retires the owned prefixes on 144/146.
The saved-result tape 145 and the remaining stack bank are restored exactly.
The composed theorem currently establishes execution, accuracy and ownership;
uniform time and simultaneous live-storage bounds remain open.

Composition of original complex-input preservation/splitting with this endpoint
still remains, together with the final ordinary-parameter inverse interface and
uniform resource gates. S3 remains partial; kappa is unchanged.

Validation: all 14,702 guarded stage-audit jobs pass, including explicit lifted
pairing, clean finish, second-component and composed two-component axiom audits.
Combined peak is 3.4 GiB. Individual guarded checks peak at 1805.2 MiB for lifted
pairing, 1841.3 MiB for clean finishing, 2947.1 MiB for the generated second
component and 2952.8 MiB for the composed pair. All new modules stay below 3 GiB.
Source-integrity, whitespace and plan-status checks pass. Proof limits are unchanged.

### Original complex input through the generated restored halo solve

`originalComponentInputs_exec` composes original-input preservation with exact
real/imaginary preparation and retains ordinary arithmetic readiness. Its native
execution is lifted structurally to the full 224-tape bank, leaving the boundary
page tapes outside the arithmetic image and changing only owned prefixes on
110, 144 and 146. Both native and physical preparation expose the explicit
preservation-plus-splitting cost.

`retainedComplexBoundary_spec` starts with one encoded complex RHS, derives both
component fields and their magnitude bounds, and executes preparation followed
by the generated two-component boundary/recovery pipeline. No separately
prepared real/imaginary streams or saved original page are assumed. The actual
paired output approximates every exact real/imaginary principal solution with
physical complex error at most `2^-target`. Every initial stack, source prefix,
parked suffix, I/O and left stack is restored except the owned result prefix on
132. The complete numerical execution and ownership path is now connected.

The main S3 status row now names this endpoint and its remaining acceptance
gates. Final inverse caller/setup and uniform fast time/simultaneous live-storage
bounds remain open; the composed accuracy theorem does not supply those resource
bounds. S3 remains partial; kappa is unchanged.

Validation: all 14,705 guarded stage-audit jobs pass, including explicit native
preparation, physical preparation and original-complex-input execution axiom
audits. Combined peak is 3.4 GiB. Individual guarded checks peak at 1956.7 MiB,
2908.9 MiB and 2941.3 MiB respectively; all new modules remain below 3 GiB.
Source-integrity, whitespace and plan-status checks pass. Proof limits are unchanged.

### Full complex inverse contract and dimension-only table retirement bound

`retainedInverse_spec` specializes the executed, restored complex solver to the
full interval. Its premise is the ordinary complex matrix equation
`Matrix.mulVec (fun i j => (realMatrix ... i j : ℂ)) z = decodedRhs`; its result is
an actual execution with physical coordinate error at most `2^-target` against
`z`. The source, borrowed suffixes, I/O and every stack except the owned output
prefix are restored. Real/imaginary row equations follow structurally from the
complex equation, without a second numerical backend.

Packed-table retirement now has a dimension-only bound:
`N*(40*N+36*W+12*(2*W+1)*w+88)+6`. The published-prefix retirement bound adds
`18*s*w+9*s+18`. The clipped controls and each column/step are bounded once,
then the counted sum is bounded structurally. The actual recovery, transition
and finish endpoints now use this bound, with
`N ≤ min (b-a) (2*band*(t-s+2))` proved from the interval and original phase cuts.
This eliminates the packed-retirement finite sum in favor of ordinary geometry.

This polynomial bound is an accounting step, not the final fast asymptotic
estimate. Closed inverse caller/setup, reached-header/factor-bank bounds,
complete uniform time matching and simultaneous live-storage gates remain open.
S3 remains partial; kappa is unchanged.

Validation: all 14,708 guarded stage-audit jobs pass, including eleven explicit
inverse/cardinality/retirement-budget axiom audits. Combined peak is 3.4 GiB.
Individual guarded checks peak at 1750.8 MiB for the geometry count, 1937.3 MiB
for retirement bounds and 2929.0 MiB for the full inverse contract. The affected
recovery and transition modules check at 2969.5 and 2945.2 MiB. Source-integrity,
whitespace and plan-status checks pass. Proof limits are unchanged.
The affected finish module checks at 2947.5 MiB; all new and changed proof modules
remain below 3 GiB.

### Bound obsolete unfold headers and simplify the publication cost interface

`boundaryUnfoldHeaderVolume` tracks only the four obsolete factor headers used
by unfolding. Factor initialization proves its bound
`12*band*w+N*(12*band+1)` from the prepared dimensions and clean scratch; factor
construction, triangular solving and exact unscaling preserve it structurally.
The retained solve now carries that derived fact. Real unfolding clears the old
headers, and its postcondition proves that the later coordinate-unfold retirement
volume is exactly zero.

`retainedBoundaryRealUnfoldCost` and `retainedBoundaryPublishedCost` now bound the
actual executions using only ordinary parameters. The two previous reached-tape
retirement sums are gone. The publication, recovery, transition and finish
interfaces no longer expose solve/unfold predecessor-state witnesses that those
sums required. The full complex and inverse callers still check against the
simpler interfaces. The prior predecessor-witness interface is available at
restore commit `42d0f452`.

The reached publication state remains exposed only for the factor-bank release
volume; deriving its dimension bound is still open. Closed caller/setup,
uniform fast asymptotic matching and simultaneous live-storage gates also remain
open. S3 remains partial; kappa is unchanged.

Validation: all 14,709 guarded stage-audit jobs pass, including the two new
header-volume preservation audits and the strengthened factor/solve/unfold/
publication/inverse audits. The final rebuild peaks at 10.3 GiB combined; every
affected proof module checks individually below 3 GiB (maximum 2975.8 MiB).
The header-volume module now imports only the resampling core and checks at
1772.8 MiB. Source-integrity, whitespace and plan-status checks pass. Proof limits
are unchanged.

### Factor-page and workspace-release volume lemmas

The forward factor-table length argument is now a reusable structural lemma.
`factorTableVolumes` derives the encoded sizes of the forward, upper and
reciprocal pages from the window dimensions. `BoundaryPermanentBound` bounds
registers that persist through solving; its factor-preparation theorem accounts
for prepared headers, clean scratch and the three factor pages. A register-cover
lemma then converts a persistent-register bound and cleared transient registers
into a bound on the entire released bank and its release cost.

These are support lemmas. Instantiating and carrying the persistent bound through
the retained execution is still open, so the public recovery interface still
exposes the publication state for its release cost. S3 remains partial; the
closed caller/setup, uniform fast asymptotic and simultaneous live-storage gates
remain open. Kappa is unchanged.

Validation: all 14,712 guarded stage-audit jobs pass, including seven new explicit
axiom audits for the structural length, register coverage, persistent bounds,
factor-page volumes and release budget. The rebuild peaks at 16.9 GiB combined.
The three new modules check individually at 2863.9 MiB (persistent bound),
2831.1 MiB (release volume) and 1786.9 MiB (factor pages); the refactored factor
module checks at 2491.9 MiB. Whitespace and plan-status checks pass. Proof limits
are unchanged.


### Derive the released-bank bound through the complete retained inverse

Factor initialization now derives `BoundaryPermanentBound` from generated setup
and the exact factor-page volumes. The bound is preserved through both triangular
solves, unscaling, real unfolding and ambient publication. Publication therefore
bounds the entire released register bank using only the ordinary dimensions.
`retainedBoundaryRecoveredCost` combines publication, recovery, packed-table
retirement and workspace release without a reached-state parameter.

The recovery, transition and finish contracts no longer expose the publication
state or its execution witnesses. The complete pair, original complex-input
caller and full inverse contract now carry total time bounds:
`retainedBoundaryPairCost` and `retainedComplexBoundaryCost`. Their bounds include
both real solves, input preservation/splitting, complex pairing and restoration.
The previous reached-state interface is available at restore commit `6c212ba7`.

This closes the reached-factor-bank volume accounting gap. The resulting bound
still requires matching to the uniform fast S3 budget; closed caller/setup and
simultaneous live-storage gates remain open. S3 remains partial; kappa is unchanged.

Validation: all 14,712 guarded stage-audit jobs pass against the strengthened
factor/solve/unfold/publication/recovery/pair/complex/inverse contracts, with a
3.4 GiB combined peak in the final rebuild. All thirteen changed proof modules
pass individual guarded checks below 3 GiB (maximum 2991.4 MiB). Changed-source
proof-integrity, whitespace and plan-status checks pass. Proof limits are unchanged.

### Executable scalar selection for the inverse caller

`tblRootSuccessor_do` and `tblBitCount_do` give structural table programs for
`Nat.sqrt x+1` and `Nat.size x`, including x=0, unchanged accumulators and derived
word fits. `tblBandParameter_do` composes integer division with the root search
to compute the canonical `PhaseCellBand.width p u` from only p and u in
`4*band+12` table atoms.

`inverseExecutionExponent_eq` identifies the retained inverse's selected working
exponent with
`target+2*l+24*p+4*Nat.size (8*p)+Nat.size N+Nat.size (2*band+1)+28`.
`tblInverseExponent_do` computes this affine expression from the three bit counts
in 42 atoms. `tblInverseDimensionWords_do` computes the actual q, stage count,
word width and scaled arithmetic parameter from that exponent and p in 31 atoms.
All programs have fixed syntax and proved fits; no parameter value is compiled
into their syntax.

These scalar selection components still need composition with boundary counting,
physical header installation and the retained inverse. The caller therefore
still takes its readiness bank; closed setup is not yet proved. Uniform fast time
matching and simultaneous live-storage gates also remain open. S3 remains
partial; kappa is unchanged.

Validation: all 14,715 guarded stage-audit jobs pass, including seven new explicit
scalar-selection axiom audits; the final rebuild peaks at 3.4 GiB combined.
Individual guarded checks peak at 1352.9 MiB (root/bit-count arithmetic),
1774.2 MiB (band selection) and 2027.0 MiB (precision and dimension words).
Source-integrity, whitespace and plan-status checks pass. Proof limits are unchanged.

### Compose scalar selection and install the inverse master headers

`boundaryCountCode_do` counts the actual halo boundary directly from ordinary
scalar geometry, before any coefficient or boundary page exists. Its result is
exactly `(haloBoundary s t band a b).card`, its accumulator is unchanged and its
atom bound is `31*s+4`. The count uses the already verified halo membership test;
it is not supplied by the caller.

`tblComputedInversePrecision_do` composes the three bit counts, affine exponent
and dimension-word programs. `tblInverseScalars_do` then composes band selection,
boundary counting and precision selection from only the eight scalar inputs
p, u, l, target, s, t, a and b. It preserves all eight inputs and proves the exact
band, boundary cardinality, working exponent, q, stage count, word width and
scaled arithmetic parameter, including every word fit. Its atom bound is
`4*band+31*s+4*(size(8*p)+size(N)+size(2*band+1))+116`.

`installInverseHeaders_exec` executes that fixed scalar program and converts its
results into the ten ordinary unary masters. It charges all table execution and
unary conversions and proves the exact header prefixes, untouched spectators,
input/output/left-stack restoration and retained binary-bank contract. The
header ports and scalar register map are structural parameters, so the setup can
be placed outside the retained solver without duplicating its proof.

Physical bank placement, cleanup of the derived scalar workspace and composition
with the retained inverse remain open; the public retained caller still takes
its readiness bank. Uniform fast time matching and simultaneous live-storage
bounds also remain open. S3 remains partial; kappa is unchanged.

Validation: all 14,719 guarded stage-audit jobs pass, including seven new explicit
composition/counting/header-installation axiom audits; final combined peak is
3.4 GiB. All five changed implementation modules pass individual guarded checks
(maximum 2240.6 MiB). Source-integrity, whitespace and plan-status checks pass.
Proof limits are unchanged.
