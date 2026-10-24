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
| [Proved Mathlib end-to-end multiplier](plan/C-mathlib-end-to-end.md) | — | ✅ 1/1 | ✅ 1/1 | 846 |

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

6. Compose the full arbitrary-coordinate router and audit its total cost and
   exact restored-bank contract. R3 remains open until all these gates pass.

The older Balanced design's rotation counts and minimal parameter choices are
historical; use the proved R1 schedule and the reservoir-compatible spacing above.
Raw descriptor/header generation, sparse-profile compilation, physical placement
and short-record fallback remain R3. Layout/support integration
remains R4. Completing R2 does not change the current multiplication kappa.

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
| S2 fast forward map | 🟡 partial machine | Implement the chirped-correlation formula using S1, with executable coefficient tables, overlapping input windows and a proved forward-resampling contract. | 3–5k |
| S3 fast inverse map | 🟡 math / ⬜ machine | Cell-interior products, boundary preparation/solve, coupling and recovery, with precision and actual line costs. Reuse the phase-cell mathematics and band primitives; fix the interface to S4–S5 before implementing a legacy whole-axis schedule. | 6–10k |
| S4 grouped/fused execution | ⬜ | Ordered core/halo neighborhoods, overlap/cropping, reusable setup, error composition and full-tensor support. Combine S2–S3 with R4 so exposure is not repaid per axis. Preserve reserved chunks and restore layouts before subsequent phases. | 8–16k |
| S5 boundary work | ⬜ | Fast boundary matrix operations required by the new parameter regime, including numerical stability, coefficient widths and actual tape costs. Specify this interface with S3–S4; the old band solve alone does not establish it. | 4–10k |
| S6 outer integration | ⬜ | New sizing and precision, both resampling directions, bulk CRT/exposure and every changed cost matched into the final machine. Depends on R4, S4–S5 and M4; closes M11 with M9–M10. | 3–6k |

Estimated remaining resampling/outer-integration total (S2–S6): **24–48k additional or substantially
revised Lean lines**, excluding R1–R4, M9–M10 and generated data. This is a lower-confidence
scope estimate, especially for fused execution and boundary work, not a delivery-time
estimate. The rows partition the intended work; shared helpers should be proved once.
S1 is complete independently of root imports and Routing. `ShortConv.Fixed.closed_exec`
packs raw batches, generates headers/counters, invokes one shared ring product and
clears generated workspace. Only the output changes; inputs, dimensions, scratch and
spectators are restored, including empty batches. `output_coeff` proves exact signed
coefficient recovery and `output_err` bounds rescaled error by `2r/2^p`. The fixed cost
is `ShortConv.Fixed.cost`; setup outside its per-record term is paid once per batch.

S2 has two verified machine contracts, not yet one complete forward map:

- **Correlation:** `chirpTableCorrelation_exec` generates G/K tables, gathers windows
  from the raw line, produces weighted/reversed operands, installs S1 dimensions,
  executes one shared product/extraction and erases all temporary streams/counters.
  Only the correlation destination changes. Its cost is `chirpTableCorrelationCost`;
  retained binary banks and multiplier templates are still supplied.
- **Output products:** `chirpOutputProducts_exec` executes both numerator shifts and
  the E/normalization products, reusing one E row and one normalization word. It emits
  exactly `chirpOutputNumerator`, with cost `chirpOutputProductsCost`. Signed fits follow
  from unit-disk correlations, bounded factors and `w ≥ q+l+Γ+5`. Factor tables and
  private scratch are restored; source/intermediate tapes remain owned working data.
- **Mathematics:** `chirpOutputWord_chirpAR` identifies integer postprocessing of each
  decoded correlation word with the analytic map, including the final partial block.
  `chirpComputed_approx` discharges computed-factor errors under explicit window and
  precision gates. Changed modules pass guarded checks and standard-axiom audits.

S2 completion still requires:

1. Generate initial binary banks and multiplier templates, output E/normalization
   setup and shift controls from the original caller inputs.
2. Join correlation and output execution; erase intermediates, execute final signed
   precision reduction and crop the final partial block.
3. Choose parameters to discharge precision/width gates, reuse setup across lines,
   and prove the complete forward correctness, error and actual cost comparison.

Detailed contracts are indexed in the
[chirp design notes](IntegerMultBounds/MathlibTM2/NearOne/DESIGN.md).
S2–S6 remain open; kappa is unchanged until the full affected machine costs close.

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
