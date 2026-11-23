# D. Sharper multiplication bound, by manuscript section

Part of the [bound scoreboard and work queue](../PLAN.md).

## Sources and section numbering

Section numbers below are **printed section numbers in the original OpenAI
manuscript**, pinned at `adc7f1241b42e322a6451854ab7e4b4c146bf78a`:
[PDF and source](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026).
The PDF contents and TeX include order were checked directly. In particular,
§7 is *Exact normalized polynomial products*, §8 is resampling, §9 is exact
integer multiplication, §11 is matrix transposition, and grouped rectangles
are Appendix A. Source filenames do not consistently equal section numbers:
`06-transforms.tex` contains both §§6 and 7. Earlier archived plan headings
used filenames as section numbers; do not propagate that mistake.

The sharper target is the **selected** community construction at revision
`0fdd7d82de03e43c9e5a1000dfbcd380d1b687d2`, not the older numerical witnesses
in individual notes. The [source pin](../docs/sharper-bound-source.json)
records the selected certificate, supporting sources and manuscript digests.
The original manuscript proves saving `2^-182`; our published, audited Lean
theorem proves `14229/2^46 ≈ 2^-32.20`. Its active compact parameters are
`epsilon=31/64`, `delta=2^-7`, `c=2^-2`, and `lambda'=1-459/2^40`. The selected upstream conditional saving is
`0.001672660197076918`; matching it unconditionally remains the goal.

## Diagnosis: where our current bound is lost

Write `a_b = 1 - tau = 296/10^11`, `a_c = 1 - sigma = 418/10^12`,
`d ≍ p^epsilon`, `K ≍ d^c`, and `p ≍ log n`. Larger exponent saving means
less asymptotic time; these are not measured timing speedups.

| Original section | Published compact restriction | Concrete bottleneck / next work |
| --- | --- | --- |
| §3.6, finite-network exponents | Bit saving `a_b`; complex saving `a_c`. | Replace the existing suppliers by selected PR589 and T16 words, with framed correctness, charged schedules and variable-rank moments. |
| §4.2–4.3, address interchange | Field moves inherit `tau`. | Direct CRT routing is complete; selected arbitrary-source routing still needs an actual schedule and costs. |
| §5.2–5.3 and Appendix A, layer control | **Binding margin `epsilon (1-lambda') = 513/2^43`, covering `2^-34`.** | Compact controls and full-depth execution are complete. Dimension/layer retuning is complete; selected suppliers, stopped recursion and local repair costs are structural follow-ups. |
| §6.2, transform layout | Saving `epsilon c a_b`, above the published bound. | Fourth-root chunks are integrated; selected coordinate routing and balanced prefixes are needed beyond this route. |
| §§8.2, 9.3, CRT and axis exposure | Saving `(1-epsilon) a_b`. | Direct routing is integrated; preserve it under new sizing and selected routing. |
| §8.1–8.2, Gaussian arithmetic | Saving `1/2 - 2^-7 - epsilon(1+2^-33)`, about `2^-7` at `epsilon=31/64`. | The sharpened logarithmic charge supports the dyadic dimension; selected near-one dimensions require faster inverse and bulk core/halo execution. |
| §7, packed ring products | Saving `epsilon (1-c)`, above the published bound. | Preserve the conventional subroutine, widths and logarithmic allowance under each retune. |
| §9.7–9.8, precision and assembly | The smallest surviving stage margin wins. | Link every improved estimate to actual fixed-machine execution, exact recovery and a standard-axiom audit. |

The old full-slot restriction `c < lambda' - lambda` belongs to the historical
M2 implementation; it no longer restricts the running compact branch. The
completed `2^-37`, `2^-36` and `2^-35` checkpoints successively integrated compact
execution, sixteenth-root dimensions and eighth-root dimensions with sharper
logarithmic costs. The published proof audit covers 125034 declarations and the
focused audit covers 572 contracts.

**Completed dyadic integration: `2^-34`.** Uses the dyadic rational dimension
`epsilon=9/64`, fourth-root chunks `c=1/4`, and
`lambda'=1-57/2^37`. The exact layer margin is `513/2^43`, above the public target
`512/2^43`; the Gaussian margin is `2^-7`. Sizing, executable parameter generation,
chunk generation, analytic envelopes, wider-machine costs and final theorem
closure have passed all 298 affected dependency checks and both final audits. Internal parameters remain exact
dyadic rationals; public savings remain powers of two.

`CompactGaussianRoute` refines this: the ceiling comes from the coarse
Gaussian estimate forcing `epsilon<1/6`. With the existing supplier and the
selected phase-cell Gaussian margin `min(1-ε-δ, r-δ)`, the candidate
`epsilon=5/8`, `c=1/4`, `lambda'=1-417/10^12`, `r=1/4` covers `2^-32` in all
five stage margins and the recurrence slacks, while no Gaussian improvement
alone reaches `2^-31`. M7 is therefore the next bound-moving milestone, worth
up to two dyadic steps without M6. At `epsilon=5/8` the executable dimension
stage, precision and guard growth, prime supply and bulk core/halo execution
must all be revalidated; the certificate is arithmetic only.

The checked `CompactSupplierCeiling.saving_lt_ceiling` proves that the existing
complex supplier together with the current coarse Gaussian restriction cannot
reach `2^-33`, even with nonnegative logarithmic loss and arbitrary admissible
dimension/layer retuning. Thus `2^-34` is the last dyadic checkpoint available
through this route; the selected supplier and structural milestones below are
necessary to continue toward the state of the art.

## Historical M1: retune the existing construction

**M1 — §§5, 6, 9:** `epsilon = 2^-30` and `c = 2^-34`, keeping the existing
primitive exponents and layer exponents. The public theorem at that milestone was
`MathlibTM2.mulInTime : MulInTime (2 ^ 93 : ℝ)⁻¹`.

The exact internal saving, exposed separately by `mulInTime_exact`, is
`296 / (10^11 * 2^64)`, between `2^-93` and `2^-92`. It is `2^67` times the
previous internal saving; the rounded public saving improves the previous
exact bound by more than `2^66`. These are improvements in the asymptotic
exponent saving, not measured runtime speedups.

Implementation completed:

1. Changed the root indices and value lemmas in `Mult/Sizes.lean`, and the
   executable root programs, stage proofs and step counts in `Fast/ParamProg.lean`.
   The existing sizing, width, finite-cutoff and cost proofs check unchanged.
2. Updated `Cost/Total.tot_kappa_eq`; exposed `MainStatement.mulInTime_of_bundles`
   and the explicit theorem in `Theorem.lean`. `statement : Statement` remains
   available through the stronger bound. The power-of-two corollary follows
   from the existing monotonicity of the logarithmic time exponent.
3. Verified the theorem's dependencies with the guarded targeted build and
   its import closure with `CompletedProofCheck.lean`, which also checks the
   explicit public bound and allows only the three standard axioms. Use these
   focused checks for this change; a full-library rebuild is unnecessary.

**Historical M1 bottleneck:** layout gave `epsilon c (1-tau)`, and quadratic
CRT limited epsilon. M2 has removed that routing restriction. The current
minimum margin remains the layout term; the next smallest is the layer term
`epsilon(1-lambda')`. M3 is the next implementation milestone.

## Section-by-section implementation work

#### §2 — The machine model and elementary streams

Reuse Mathlib `FinTM2`, the existing finite host/compiler, encodings, scanning,
stack frames and guarded audits. No new machine model is required. New
schedules must use a fixed number of stacks and labels; growing network,
owner and address descriptions must be runtime data or a fixed finite program,
with generation and interpretation priced explicitly. Preserve arbitrary
spectators, workspace restoration and standard binary input/output.

**Deliverable:** extend existing host contracts for each new stage, with an
actual-step bound and clean returned state. This is a requirement of M2–M8,
not an independent attempt to improve the exponent.

#### §3 — Two finite networks with a rank saving

**M6a — replace the scalar/frame suppliers.** The current implementation uses
Shared50 bit machinery and the h=25 complex branching certificate
(`Cost/Branching.lean`). The target instead combines PR589's punctured R439
bit word with the selected T16 complex owner packing. Formalize both exact
words from pinned data, their complete dirty-input linear maps, source
mutations, restoration, entrance/exit frames and physical occurrence order.
Use `Networks/FramedCircuit.lean`, `BoundedFramedCircuit.lean`, existing
projection-rank and finite-field algebra as foundations, not as already proved
adapters for these words.

The selected complex rank histogram is
`{1:349604, 2:60192, 3:62585, 4:20448, 5:11808, 7:7, 8:1152, 48:4866}`.
The selected complex parent width is 73; the PR589 bit parent width is 64.
The primitive endpoint savings are approximately `0.0016754626768081035`
and `0.0017334270395898442`, respectively. Prove the exact moment inequalities
for the full histograms and all surcharges; a total-rank inequality alone
loses the benefit of variable-rank children.

**M6b — prove the physical owner schedule.** T16 changes 193 placements while
retaining the scalar word, role widths and source-event times. Prove the
144 complete-call ownership schedule, lifetime/capacity constraints, frame
availability and mutable-source behavior. Check the actual selected inventory;
older SW4/72-call proofs explain ancestry but do not prove the selected schedule.

**Done means:** both supplier semantics and fully charged profiles are checked
in Lean, including bit H1–H5 and the native-complex pricing justification.
The conservative complex surcharge gives final saving `0.001672660194225008`;
that is a distinct fallback waypoint, not the exact selected target.

**Selected T16 finite geometry checked:** the hash-pinned 1004 binary bases
and their dual witnesses, all 2888 oriented span inclusions/dimension differences,
and their occurrence bindings to both complete native traces now pass Lean.
The doubled-space subspaces `L_U={(u,u+v):u in U,v in U-perp}` are isotropic
of dimension nine; nested intersections have the exact deficit declared by each
climb/center event. All 182 modules and the 16310-declaration standard-axiom audit
pass at default limits. The supplier's true recursive width is a symplectic
B-block rank, not complex operator or projector rank. Canonical Clifford/tableau
action, correspondence to that B-block rank, serialized global phases and
physical hosting remain explicit obligations; degenerate binary subspaces
are allowed and cannot be fed blindly to nondegenerate-projector interfaces.

#### §4 — Faster interchange of address chunks

**M2 — complete: direct nonadjacent axis routing, also §§8.2 and 9.3.**
The implementation chronology below records the original obligations and
intermediate states; the completion summary gives the final status.
The sharper [nonadjacent-axis note](https://github.com/CrocSwap/integer-mult-bounds/blob/0fdd7d82de03e43c9e5a1000dfbcd380d1b687d2/notes/nonadjacent-axis-note.tex)
uses the existing arbitrary-gap primitive to reverse axes with paired distant
swaps and expose each resampling axis with one swap and its inverse. It replaces
`d^2(1+ell^tau)` by `d(1+ell^tau)`, changing the saving from
`a_b-epsilon(1+a_b)` to `a_b(1-epsilon)`.

The current resampling machines already use two distant-field swaps per
nonfinal axis (`Fast/ResampAAll.lean`, `Fast/ResampBAll.lean`), so retain those
implementations and expose their sharper charge separately from `totCRT`.
`Fast/ResampASwap.lean` supplies a reusable arbitrary-gap host adapter, including
axis widths differing by one. Adapt it for the CRT headers, then replace
the adjacent walks in `Fast/CRTSwap.lean` and `Fast/CRTDrive.lean`; update
`Cost/MatchCRT.lean` and both resampling matchers. Audit the existing residual
`O(d^2 Tp)` arithmetic separately: reducing swaps alone must not silently
delete that term. Retain its exponent `2 epsilon` or prove the stronger
controlled-rotation schedule needed by later near-one epsilon parameters. Keep the original axis arithmetic order so
rounding and numerical correctness proofs can be reused. Price descriptors,
cleanup and all intermediate data movement. Merely tightening `totCRT` would
be unsound: the historical CRT machine performed the quadratic schedule.

**M2 implementation status:** the first bridge is proved in
`Fast/CRTGap.lean`. `crtSwapGapBox` and `crtSwapGapBoxBits` connect the
arbitrary-gap interchange to CRT record layouts; `crtGapHeaderP_runs`
constructs the middle-count header in `4g+8` host steps while restoring its
scratch register. `crtGapHdrBits_canonical` and `crtGapHdrBits_value` establish
the full header contract. `crtSwapGapPass_runs` proves the executable pass,
its volume/width cost, and restoration of all other registers. The pass assumes
prepared headers; it does not absorb their generation or cleanup for free.
The public fast-path aggregator imports this module, and `CRTGapCheck.lean`
audits the new contracts against the standard axiom set.

The driver is **not** a one-swap substitution. `crtFwdWalk_runs` moves
`i :: reverse(range i)` to `reverse(range i) ++ [i]`. For three axes,
`[2,1,0]` must become `[1,0,2]`; swapping the endpoints instead produces
`[0,1,2]`. More importantly, `crtRotP_runs` in `Fast/CRTRot.lean` expects
exactly `crtRevAx i` before the target: its address-validity count supplies
`crtKI`, the weighted mixed-radix control value. Arbitrarily reordering that
prefix changes the interpretation of the counter. The pure CRT content
lemmas in `CRTSpec.lean` remain reusable once that machine interface is proved.

**M2b progress:** `Fast/CRTControl.lean` now proves an alternative to the
order-dependent validity counter. Each physical field carries its place,
modulus bound, original mixed-radix weight and active-control flag. The
address evaluator recovers exactly `crtKI` and the original validity predicate,
even with higher spectator axes mixed into the prefix. `crtControlRotOut_top`
proves that all fibers together produce the same forward/inverse `crtRotC`,
including invalid controls and padded target slots. A direct multiplication
and remainder replaces iteration of `crtLo`; `crtControlShift_mod` proves the
same cyclic shift.

`Fast/CRTControlProg.lean` implements one descriptor in a fixed ten-variable
binary program: at most nine interpreter atoms, with scratch cleared and
spectators preserved. `crtControlStep_host` gives the actual host bound
`9 * tblC W w`; this is not nine Turing-machine steps. A separate three-atom
kernel computes the modular offset and complement. `CRTControlCheck.lean`
audits the semantic and executable contracts. No descriptor generation,
loading, fiber-loop or conversion cost has been silently included in these
kernel bounds. The subsequent loader/scanner and conversion contracts below
price these additional operations explicitly.

**Chosen driver design:** retain the fully reversed axis layout during the
triangular arithmetic passes. Expose each nonzero target by swapping it with
axis zero at the inner end, run the descriptor-controlled rotation, then swap
back. Finish the forward machine with paired distant swaps reversing the
whole axis list; perform that reversal first in the inverse machine. This
preserves the original target order and content maps while using at most
`2(d-1) + floor(d/2)` swaps in either direction. `Fast/CRTSchedule.lean` proves the exact forward/inverse route and count,
including exposure-prefix completeness and restoration. `Fast/CRTLinear.lean`
now implements each distant exposure and unexposure, including header
construction, upgrade and cleanup, with all scratch restored. Runtime unary
width generation and the complete driver remain to be assembled.

For each target, the new scan visits `2^(L-a_i)` fibers. There are at most `d`
descriptors per fiber, so the proved arithmetic kernel would contribute at
most `9 d 2^(L-a_i) tblC W w` before loading, offset conversion and loop costs.
`Fast/CRTControlBounds.lean` proves descriptor widths `L+1`, accumulated
values below `2^(2L)` even for invalid controls, and final products below
`2^(3L+1)`. Its budget invariant discharges intermediate overflow.
`Cost/CRTControl.lean` uses `mr_b_pow_le_r` to absorb any fixed polynomial
per-fiber budget over all axes into a constant times padded volume. The
actual scanner now supplies that budget through the contracts below.

`Fast/CRTControlTape.lean` proves the fixed four-word loader costs at most
`48 W + 56` host steps, with descriptor reversal saved for restoration.
The complete saved tape restores in `8 d W + 2` steps. A positive width
makes tape emptiness exactly descriptor-list emptiness; the arithmetic step
plus descriptor cleanup uses at most 13 interpreter atoms. These contracts
are included in the focused axiom audit.

`Fast/CRTControlBank.lean`, `CRTControlScan.lean` and `CRTControlScanner.lean`
now compose the loader with the interpreter and a fixed runtime `while` loop.
The concrete scanner has no assumed packet-execution premise: arithmetic
fit follows from the preserved budget, including invalid controls. Its output
is the exact control sum and sticky validity flag, with descriptor tape restored
and other registers preserved. The scan costs at most
`2^10 * d * (W+4)^2 + 4` actual host steps. `Cost/CRTControlScan.lean`
bounds the exact scan cost by `2^15*(L+1)^3` for `d≤L`, `W≤3L+1`, and
absorbs all fibers of all pipeline axes into `2^19*T` eventually.

`Fast/CRTControlOffset.lean` compiles the modular-offset kernel, converts
both directional lengths to unary, and clears those counters afterward.
Conversion costs `W*(4*S+22)+2*S+12`, separate from the three-atom
binary kernel and the `2*S+4` counter cleanup. This linear-in-modulus work
is **not** part of the polynomial descriptor-scan absorption. `Fast/CRTControlBridge.lean` now computes offsets directly in the scanner's
ten-variable bank, preserving its control sum and validity flag; the separate
five-variable interface is no longer required for this path.
`CRTControlConstants.lean` loads permanent target constants while preserving
sources. `CRTControlFiber.lean` selects rotation or copying from the binary
validity flag, and `CRTControlRotate.lean` composes offset computation,
materialization, physical movement and counter cleanup. `CRTControlPass.lean`
combines the actual scanner, constants load and rotation into one fiber with
no assumed execution contract. Descriptor tape and scratch return restored.

`Cost/CRTControlOffset.lean` separately bounds materialization plus cleanup
across all fibers by `2^7*d*T*p`, a linear number of full-volume record passes.
This does not include binary arithmetic or physical data movement; their
explicit bounds must be added when matching the complete pass.

`CRTControlReset.lean` loads the outer loop's binary address and establishes
the next fiber's canonical bank, costing `8W+8+10*tblC W w`.
`CRTControlLoop.lean` supplies a fixed indexed loop exposing that address to
each body, including initialization, runtime count construction and cleanup.
Its bound is `2^L*(bodyCost+4W+16)+6W+9L+17`. The body contract is discharged by `CRTControlAllFibers.lean`, including
output reversal and exact ordered execution of every fiber.
`CRTControlRotation.lean` specializes this execution to the original `crtRotC`
semantics with automatically proved arithmetic fits at width `3B+1`.
`CRTControlWorkspace.lean`, `CRTControlSetup.lean` and
`CRTControlAllWorkspace.lean` initialize and clear the bank and construct the
actual unary word width. The rotation wrapper changes only the data source
and restores every other register.
`Cost/CRTControlAllFibers.lean` bounds all passes, bank setup/cleanup and width
setup/cleanup by `2^21*(cw+1)*d*T*p` eventually, excluding descriptor generation.

`CRTControlGenerate.lean` provides actual packet emission, binary powers
without unary expansion, exposed-place/active-field arithmetic, and original
weight advancement. `CRTControlGenerateLayout.lean` proves that ascending
traversal with target omission and saved-zero insertion produces exactly the
required descriptors in physical exposed-axis order.
`CRTControlGenerateLoop.lean` now proves the concrete per-axis operation:
read both unary entries, construct the power directly in binary, emit/select
its packet, advance the original mixed-radix weight, and save the entries.
`CRTControlGenerateSetup.lean` provisions the bank and target constants from
unary inputs, preserving those sources. `Cost/CRTControlGenerate.lean` proves
that all target setup costs and all per-axis generation costs are each
absorbed by one padded volume eventually. Loop overhead and terminal stream
cleanup are included in the complete producer match below. `CRTControlGenerateTraversal.lean`
discharges the complete traversal's per-axis execution and derives all
arithmetic fits at width `3B+1`. `CRTControlGenerateTraversalLayout.lean`
proves its exact exposed descriptor tape, including parked-zero handling.
`CRTControlProducer.lean` now composes setup, immutable target-counter copy,
traversal and bank release into an exact descriptor producer. Only its tape
destination changes. `Cost/CRTControlProducer.lean` matches its actual budget,
including source restoration and descriptor disposal: all target producers
cost at most one padded volume eventually. The generator
kernels and one-fiber pass are audited; neither constitutes a new complete CRT
driver or a stronger public bound.

`CRTControlExposeRotation.lean` now composes the actual distant exposure,
workspace rotation and unexposure for a nonzero target, returning the fixed
reversed layout and restoring every register except the data source. Its
routing parameters and descriptor/constants tapes are still prepared inputs.
`CRTControlDriverSpec.lean` identifies descending and ascending target folds
with the existing `crtFwdC` and `crtInvC`, independently of physical layout;
target zero is an identity and can be omitted. `CRTReverse.lean` and
`CRTReverseFull.lean` execute the complete paired reversal, constructing the
opposite width stream and unary half-count at runtime and restoring every
register except data. `Cost/CRTReverse.lean` bounds the complete reversal by
a linear number of interchange budgets, including runtime setup and cleanup.
`CRTControlRouting.lean` ties the distant header widths
to the existing driver's upper/lower unary counters. `CRTControlStreams.lean`
constructs preserved ascending copies of the original descending entry streams.
The complete driver and its cost match are supplied by the direct-machine
modules below.

`CRTControlParameters.lean` now executes the complete conversion from unary
modulus, multiplier, axis width and total width into the two binary constants,
unary padding and fiber-address width. It preserves all inputs and returns
its arithmetic bank and temporary registers empty. Its checked disposal
returns the four outputs empty; preparation plus disposal over all targets
is absorbed by one padded volume in `Cost/CRTControlGenerate.lean`.

The existing resampling programs now have sharp matching theorems
`mt_rsa_stage_le_linear` and `mt_rsb_stage_le_linear`: their layout charge is
`totDirectCRT = T*p*d*(1+ell^tau)`, without the old extra factor of `d`.
`DirectGrowth.lean` proves the corresponding routing exponent margin
`(1-epsilon)*(1-tau)`. The old cost APIs remain compatibility wrappers;
the running main multiplier now uses direct routing and this aggregate scale.
The final retune below publishes the stronger saving.

`CRTControlTarget.lean` now composes unary parameter preparation, descriptor
production, routing-gap setup, distant exposure, rotation and full cleanup.
Only the data register changes. `Cost/CRTControlTarget.lean` bounds the sum of
actual nonzero target costs by a constant times `totDirectCRT` plus `T`.
`CRTDirectDrive.lean` implements both unary-stream traversal directions with
exact stream restoration and a sum of individual target costs, avoiding an
extra dimension factor. Its target-body contract is discharged by the concrete machine
instantiation below, including runtime setup and padding/reversal assembly. These contracts pass the focused standard-axiom audit.

`DirectTotal.lean` supplies the aggregate envelope with linear routing and
its logarithmic time-bound bridge, using the direct routing margin. It is
checked at the final M2 parameters and matched to the actual executable
pipeline. Legacy quadratic asymptotic bounds now require an explicit exponent
hypothesis; they do not justify the new public result.

`MainDirectCore.lean` connects both linear resampling bounds to the existing
source-transform core. `mn_core_le_linear` bounds its actual `srcCoreCost` by
the linear stage sum plus the explicit forward/inverse transform charges.
Those charges are discharged by the concrete direct-machine cost match.

`CRTDirectBacking.lean` embeds the 40 direct-driver registers and 25 arithmetic
bank registers into the expanded finite CRT register family. The seven
persistent input aliases are preserved; all 58 scratch slots belong to the
existing rest-empty contract. Focused checks of `CRTMachine`, `SrcStage`,
`MainRegs` and `DistSpec` confirm the old entry contracts supply that backing.

`CRTDirectSetup.lean` now constructs the ascending streams, cached axis-zero
width, dimension count, encoded record width and bank width directly from
legacy inputs. Its six-output frame and exact cleanup back to the original
register state are proved. `Cost/CRTDirectSetup.lean` bounds actual setup plus
all six-output cleanup by one padded volume eventually. The allocation
verification also refreshed all 19 affected dependency modules through
`MainRegs` and `DistSpec`, with no full build.

`CRTDirectMachine.lean` instantiates both weighted loops with the actual target
program, without an assumed target execution contract. `CRTDirectMachineCore`
adds runtime initialization and stream restoration; only data changes.
`CRTDirectMachineSetup` proves the setup result supplies its ready-state
contract. `Cost/CRTDirectMachine` bounds the actual loop by
`(mtCrtControlTargetC + 2) * totDirectCRT`, including all metadata.
Padding/reversal and complete legacy entry composition are supplied below.

`CRTDirectMachineFull.lean` composes padding, concrete traversal and paired
reversal forward, and reversal, inverse traversal and deletion backward.
`CRTDirectEntry.lean` adds actual runtime setup and complete cleanup: both
entry theorems start from legacy inputs and update only data, with no execution
oracle. `Cost/CRTDirectFull.lean` bounds both full entries by a fixed constant
times `totDirectCRT`. `CRTDirectSource.lean` and `SrcDirectStage.lean` now bridge the complete
entries to both source transforms, preserving their exact original semantics.
`Cost/CRTDirectEntry.lean` matches the named entry and generic-dimension source
costs. `MainProg`, `MainChain` and `MainCorrect` now use these actual source
programs and preserve exact multiplication semantics. `MainTimeRuns`,
`MainTimeGlue`, `MainTime` and `MainStatement` match the running program to
`totDirectBound` and its logarithmic bound. The remaining 22 affected theorem-path modules were refreshed, and
`CompletedProofCheck.lean` passed for 111885 declarations (peak 4.3 GiB),
including the actual public fixed-machine theorem. No full build was used.

**M2 completion summary:**

1. **M2b complete:** actual all-fiber rotation, restored workspaces, runtime
   descriptor production and actual production/rotation cost matching.
2. **M2c complete:** runtime preparation, paired reversal, complete entries,
   both source transforms and the running multiplier use direct routing.
   Linear resampling costs are connected to the aggregate budget.
3. **M2d complete:** executable roots use `epsilon=2^-5`, `c=2^-32`;
   `lambda=1-3/10^10`, `lambda'=1-1/10^11`. The exact margin is
   `296/(10^11 * 2^37)` and the public saving is **`2^-66`**. Guarded theorem
   checks and the focused axiom audit validate the complete fixed machine.

The CRT charge is genuinely linear in the axis count, including all setup,
controls, physical movement and cleanup. M2 preserves the exact multiplication
semantics and improves the public exponent saving by `2^27` over historical M1.
It does not claim a corresponding wall-clock speedup. M3 is next.

#### §5 — Fast simultaneous synthetic butterfly layers; Appendix A

**M3 — compact dirty controls.** Replace full K-bit slot transports by compact
control fields of width proportional to `e log p`, following the
[compact-control layout](https://github.com/CrocSwap/integer-mult-bounds/blob/0fdd7d82de03e43c9e5a1000dfbcd380d1b687d2/notes/compact-control-layout.tex).
The target node overhead is `(e log p)^tau`, removing `K^tau`.
Reuse `Compact/*` algebra, dirty-control identities and exceptional-repair
mathematics where their contracts match. Build an adapter to the live Mathlib
`Node/Basis.lean` and `Cost/LayerCost.lean` contracts rather than reviving the
retired native controller architecture.

**Reuse route identified for M3:** the retained native modules
`Machine/ActivePrefixStageFullEarlyRun.lean` and
`Machine/ActivePrefixStageFullLateRun.lean` already execute complete selected
toggles, including descriptor synthesis, exceptional repair and cleanup.
`ActivePrefixStageFullSelected.lean` proves the literal address action, and
`ActivePrefixStageFullBudget.lean` bounds the actual runs by local volume times
`max(1,(f-1)*guard)^tau`. The live host's `foreign_exec` and placed-machine
bridge can import fixed native programs with constant-factor overhead.
Use these complete routines instead of rebuilding their arithmetic and repair.

This is not yet a compact Mathlib layer: their inputs require full reserved
front/control/back fields. Prove the live `encZ` layout supplies those ranges,
construct the original shape/node/slot descriptors, normalize the host bank
with charged cleanup, and discharge local density and payload-width premises.
The unified runtime bridge below handles singleton slots as well as both native orders.
Then replace the actual `slotXorProg` calls and their cost matching together.

**Checked host primitives:** `Node/CompactSwap.lean` executes a genuine
two-field interchange on bit streams, preserving arbitrary dirty fields,
spectators and the full register frame. `Cost/CompactSwap.lean` normalizes
its cost in compact width and volume with explicit bank-size bounds.
`Node/CompactRotParity.lean` physically packs block low bits using runtime
width counters and restores source/parameters/scratch, with exact linear cost.
The guarded checks and `CompactControlCheck.lean` pass for all four audited
contracts. These prepared primitives do not yet change the running layer or
the public saving `2^-66`; their subsequent native-stage and reservation
bridges are recorded below.

**Complete host-stage bridge checked:** `Node/CompactRotHost.lean` normalizes
placed native banks with exact frame restoration. `Node/CompactRotStage.lean`
instantiates it with the actual full early/late native executions; descriptor
synthesis, repaired action and cleanup are included. `Cost/CompactStage.lean`
and `CompactStageExec.lean` prove that the initial bank occupies at most forty
times local volume and that actual host steps retain the compact-width bound.
The fixed coefficient depends on the host bank and a uniform repair bound `D`,
not runtime dimensions. All thirteen focused axiom contracts pass.

`Node/CompactGeometry.lean` proves the actual native destination matches live
slot XOR, including untouched bits, with exact serialized rank and entry
transport. Native slot order is reversed relative to the live layer. This
baseline folds outer native rows into the address width. The new
`Node/CompactGeometryRecursive.lean` preserves unrestricted original rows and
payload offsets and proves the child invariant for one shared reserved shape.
`Node/CompactEncoding.lean` connects the actual native result to the live
three-bit coefficient serialization. `Node/CompactRotRuntime.lean` executes
the unified native dispatcher, including singleton slots, and
`Node/CompactSlotXor.lean` composes both codecs and transfers with that runtime.
The resulting actual host execution maps `encZ Z` to the required slot-XOR
encoding and restores the full frame; its cost includes all conversions.

`Cost/CompactRuntime.lean` supplies the uniform compact-width execution bound.
`Cost/CompactParameters.lean` derives repair allowance `D=1` from dyadic guard
and full row-address size inequalities. These are explicit caller obligations:
one shared guard must work throughout recursion, and the full address width
must fit both the payload and the cube of the chosen global size parameter.
`Fast/CompactSynRecArithmetic.lean` executes ceiling division and computes
front/back reservation counts, remaining active width and offset from runtime
registers, with exact costs and restored scratch. The row-axis count is still
an input. The focused audit covers these execution, cost and validity contracts.

**Runtime reservation records checked:** `Fast/CompactSynRecRows.lean` computes the
exact native row-axis reservation from the original runtime axis count.
`CompactSynRecPieces.lean` and `CompactSynRec.lean`
compose reservation arithmetic with active base-m pieces and an optional back
leaf, then restore all temporary counters. Only the serialized piece records
and their total exponent remain. `CompactSynSel.lean` proves their validity
at any sufficient shared row depth and their exact exponent sum.
`Cost/CompactSlotXor.lean` bounds complete symbol-stream execution with a fixed
power-of-two coefficient, including codecs and transfers.

`Node/CompactEncodingOffset.lean` folds low spectator address bits into the
coefficient index without moving the encoded stream. The shifted slot action
commutes with this reshape, and expanded payload and volume agree exactly.
This resolves the low-offset mismatch in the prepared compact executor.

`Fast/CompactSynRecRoot.lean` now composes the actual row-axis calculation,
reservation arithmetic, record production and cleanup. Its original-parameter
execution theorem checks without a supplied execution premise. A generic
intermediate composition avoids expensive reduction of the concrete constants;
the final guarded check uses about two GiB with unchanged proof limits.

`Fast/CompactSynRows.lean` now connects the actual padded row count: each
piece's base-row metadata is the exact quotient by its level's wire-count power.
The emitted record is literally unchanged. The native global padding proves
divisibility, and the active-axis bound proves sufficient shared depth.
Discharging reservation capacity at actual caller sizes,
top-level configuration and fallback, and header arithmetic,
caller size inequalities, the stopped branch and recurrence, and integration
into the running layer remain open. These checked bridges do
not yet improve the public saving `2^-66`.

**Reservation geometry and header generation checked:**
`Fast/CompactReservationGeometry.lean` derives one shared shape from the literal
runtime reservation counts. It proves the exact address width, back offset,
nonleaf digit and child layouts, and original pre-padding volume, under the
explicit capacity premise. `Fast/CompactSynCoverage.lean` proves that back and
active piece records together with the high row/front kernel cover the original
selected interval exactly. This is record coverage; executing the corresponding
new top configuration remains separate.

`Node/CompactHeaderBuild.lean` converts a finite family of runtime unary inputs
to canonical separator-prefixed headers while preserving sources and scratch.
`CompactHeaderBank.lean` identifies the thirteen original headers with the
native bank; the existing dispatcher still synthesizes its own derived headers.
`CompactHeaderClear.lean` restores the bank to empty.
`Node/CompactSlotPrepared.lean` composes build, actual encoded slot execution
and cleanup, with all three costs included. Only the live stream changes;
unary sources, scratch and the initially empty native bank are restored.
The computed-descriptor composition below now supplies these values. `Cost/CompactPrepared.lean` bounds header setup by `274 V` and cleanup by
`105 V`, where `V` is actual native bit volume. Complete prepared execution
retains the compact-width bound with coefficient `2^(slotExponent(T,D)+9)`,
independent of runtime dimensions. `Fast/CompactTopRows.lean` includes every
outside row and high spectator when padding: the resulting row count is at
most twice the original stock, is divisible by the global recursive divisor,
and validates the unchanged piece records.

**Runtime stage descriptor arithmetic checked:**
`Node/CompactDescriptorArithmetic.lean` and `CompactDescriptorPadding.lean`
compute width `L/(m*K)`, right spectators `(a0-oS-backBits)/K`, and left
spectators `active-m*width-right`, preserving inputs and restoring scratch
with exact costs. `compactDescriptorStage_exact` proves these are the desired
counts when `L=K*(m*k)`, `a0=oS+backBits+K*right`, and
`active=left+m*k+right`. The start offset excludes the selected residue;
`backBits=K*backChunks`, not merely the chunk count. Dispatch level-zero leaves
separately.

**Computed slot and top configuration checked:**
`Node/CompactDescriptorBankOps.lean` and `CompactDescriptorBank.lean` compute
all thirteen original header values from sixteen current/global unary inputs.
`Node/CompactSlotComputed.lean` composes descriptor computation, prepared slot
execution and cleanup, with exact costs and full source/scratch restoration.
The low offset is folded into payload without moving the encoded stream;
only the live slot-XOR stream changes. No supplied header-value oracle remains.

`Fast/CompactTopSelection.lean` proves the exact selected-bit permutation,
nonduplication, padded-piece validity and exponent sum. The six
`CompactTopConfig*` modules compute global depth and padded rows, serialize all
ten top fields and working width, then restore sources and scratch. Their
current interface still takes derived coordinates and the root exponent sum.
`Cost/CompactCallerParameters.lean` discharges repair packing for manuscript
`Sizes`, conditional on reservation, row-stock and width bounds; the running size generator has a different dimension/chunk regime.
`Cost/CompactCallerRuntimeParameters.lean` now proves repair packing directly
for actual `Mult.Sizes`, using its integer-root growth facts. Only precision
is identified with the manuscript regime. Row stock, coefficient sizes and
reservation premises remain explicit.
`Cost/CompactCallerCapacity.lean` proves actual reserved axes are eventually
below `d/M` for each fixed positive natural `M`, and certifies actual
nonterminal `synDp` rounds. Small selected sets still need capacity testing
or fallback; this does not assign a whole global reservation to every piece.
`Cost/CompactCallerRows.lean` bounds actual padded top rows and every descendant
quotient by the initial stock times `2^(rowBits+outsideBits+1)`. One bit pays
for padding; fitting this exponent into `6*b` remains a caller obligation.

`Fast/CompactTopCoordinates.lean` and `CompactTopSetup.lean` now compute all
remaining coordinates from original inputs, composing actual root records
with a fresh reservation-count pass and complete cleanup. They preserve
original sources and emit the piece record, exponent and four top coordinates.
`Fast/CompactTopOriginal.lean` now composes record setup, the role adapter,
configuration generation and cleanup from original inputs. Only piece record,
configuration and working width change; arbitrary outside-row source and all
original metadata are preserved. No derived-coordinate inputs remain.
`Cost/CompactCallerSelectedRows.lean` proves the exact top split: reserved row
bits plus original high spectators. The native address exactly matches the
reserved shape, so no extra high-address multiplier remains in native rows.
Actual padded descendant stock now supplies repair packing directly, under
the original address/row precision budget and coefficient-width premises.

**Next integration boundary:** connect the complete original-input constructor
to a compact-compatible top runner. `Fast/CompactTopReady.lean` proves the exact mask predicate, selection length,
computed shift, piece-width validity and complete reserved `topZ` semantics.
`Node/CompactBasisSlot.lean` computes the parent length from the divided live
length, seeds slot indices, executes the computed slot and clears its controls.
`Node/CompactBasis.lean` composes these actual steps to realize `basisMap`,
with summed execution costs and full frame restoration.
`Node/CompactBasisRegisters.lean` supplies a concrete finite register bank and
persistent reservation predicate, aliases the live layer counters, and proves
`compactBasisW_exec` changes only its selected wire. `Node/CompactFactorBasis.lean` and `CompactFactor.lean` now execute the full
factor with both compact basis passes, preserving global counters and proving
exact factor semantics. Only the existing child `CallSpec` remains as the
recursive induction boundary. `Cost/CompactBasis.lean` bounds every descriptor,
seed, header, native execution and cleanup cost at actual local volume times
compact width to `tau`; the fixed coefficient is `2^(slotExponent(T,D)+49)`.
The quadratic descriptor arithmetic is absorbed into the actual address volume,
not hidden in a full-width transport factor. `Node/CompactLayerProc.lean` now closes all recursive calls with the actual
compact factor; `CompactLayerGeometry.lean` derives child readiness from the
root layout and local packing/budget bounds. No recursive execution oracle
remains. `Cost/CompactFactor.lean` and `CompactFactorActual.lean` charge every
non-child factor stage to compact-width local volume with a fixed power-of-two
coefficient and retain child-cost coefficient one.

The generic `CompactTopProcRegs/Call/Kernel/Leaf` modules execute top field
reads, call cleanup and the top kernel while preserving persistent basis data.
The kernel's leaf call is discharged by actual `leafP_exec`.
`Node/CompactRegisterEmbedding.lean` gives one fixed union host bank with
shared ordinary registers and disjoint private banks. `Fast/CompactTopPlaced.lean`
executes the full original-input constructor there, preserving exact costs,
without assuming procedure-table compatibility. `Node/CompactLayerPlaced.lean` lifts the actual recursive layer to that host,
restoring the entire caller frame and preserving exact step counts.
`CompactTopProcRows/Pieces/Stages` and `CompactTopProc.lean` now execute all
seven top stages and prove both `topZ` and normalized `Hl` semantics for an
arbitrary persistent basis bank. Only per-layer `CallSpec` contracts remain
at this generic boundary, ready for the concrete compact-layer specialization.

`Cost/CompactLayer.lean` supplies a canonical rounded-up compact basis budget
and bounds the actual layer cost by an explicit scalar recurrence with the
original leaf term. `Cost/CompactLayerReady.lean` derives recursive readiness
using this proved budget and local packing, without an arbitrary cost premise.
`Fast/CompactTopPrecision.lean` proves the pre-shift array fits the exact
computed working width from the original numerator norm bound. Complete
caller specialization, actual initialization of persistent basis inputs,
and stopped recursion remain open.
`Cost/CompactLayerNormalized.lean` now proves the exact per-volume recurrence:
child coefficient `factorCount/NW`, compact basis ratio bounded by
`3*compactBasisConst*max(1,(bits-1)*guard)^tau` plus inverse volume, and explicit
linear address/payload overhead `1+(o+n)/(r*w)`. The actual level-zero leaf
term remains `200*u*(1+(o+n)/(r*w))`; no new stopping rule is claimed.
`Fast/CompactTopExecution.lean` now specializes all seven stages to the actual
placed compact layer, eliminating the generic execution/call-contract premise.
`Fast/CompactPieceGeometry.lean` supplies the actual piece offsets, recursive
layouts and kernel extent. `Cost/CompactPiecePacking.lean` derives recursive
readiness from original row/address precision and runtime sizes, including
canonical numeric budgets. `Cost/CompactCallerShape.lean` now derives the
primitive guard positivity, guard room and record capacity from the actual
runtime sizes, uniformly over selected dimensions and folded offsets.
`Cost/CompactLayerBound.lean` solves the normalized recurrence with a fixed
power-of-two coefficient, retaining the leaf term and explicit address/payload
condition. The resulting local charge has no full chunk-width power. `Cost/CompactTopBound.lean` now sums the actual base-m digit envelopes
geometrically without a logarithmic piece-count loss, and exactly separates
all executable top control work from kernel and recursive-call costs.
`Cost/CompactTopControlBound.lean` bounds both phase scans and the final
unit multiplication linearly in actual stream volume, retaining configuration
reads and unary headers explicitly. Widening and truncation now have checked
working-volume bounds, and `Cost/CompactTopRowControlBound.lean` bounds row
reshaping, padding and unpadding by actual stream volume.
`Cost/CompactTopRecordBound.lean` derives every piece header length from its
actual `TopPc.Ok` contract and charges dispatch, loop transitions and record
erasure. `CompactTopBlockBound/CompactTopOverhead/CompactTopControlVolume`
combine every nonrecursive top stage into the checked bound
`2^14 * (pieceCount+1) * paddedVolume`; no unspecified control-cost premise
remains. `CompactTopPieceCount` bounds the actual record count by
`2+log_m(d)`, including empty active/back cases; `CompactTopControlPower`
absorbs complete actual control work into padded volume times any fixed
positive dimension power, with a fixed dyadic coefficient. Complete
constructor/setup costs and complete multiplier propagation still require assembly.
`CompactTopActualBound/CompactTopAbsoluteBound/CompactTopCompleteBound` now
sum the actual reserved recursive calls, charge the actual widened kernel,
and combine both with all controls in a single padded-volume bound.
Absolute-to-relative coordinates preserve volume without counting the low
offset twice. `CompactTopOriginalBound/CompactTopOriginalVolume` bound
configuration serialization, literal source restoration and unary row padding.
`CompactTopOriginalGeometry` derives the row-division budget from actual
reserved axes plus three selected address bits. `CompactTopRecordSetupBound` now bounds actual record generation and
original-divisor computation by fixed polynomials with dyadic coefficients.
`CompactTopOriginalRuntime` derives the row-division budget from actual
integer-root sizes for selected intervals at least one chunk long. Complete
round-overhead absorption and multiplier propagation remain separate.
`CompactTopOriginalCompleteBound` combines every actual constructor stage
into `2^17*(G+m+1)*B^7 + 2^13*V`, deriving unary division from geometry.
Its scalar budgets still need to be discharged at the full caller.
Specializing that envelope to the actual canonical layer costs,
original-caller initialization and complete multiplier cost propagation
remain necessary before claiming another public saving.
`Node/CompactBasisSetupCounts.lean` and `CompactBasisSetupPlacement.lean`
compute and place the seven persistent reservation values.
`CompactBasisSetupFrame/Output` and `CompactBasisSetup.lean` now execute
the complete setup on the shared host with exact seven-register output,
source preservation and restored scratch. `CompactBasisSetupRest` and
`CompactBasisCleanup` close its rest invariant and exact cleanup.
`CompactGlobalBootstrapCounts/CompactGlobalBootstrap` compute the original
guard and dimension on the persistent bank and clear copied inputs;
`CompactBasisRefreshPlacement/Refresh/RefreshRest` refresh the five per-round
fields while preserving those globals, with exact cleanup and invariants.
Propagate the complete execution costs and discharge remaining caller sizing; record coverage alone
does not establish the complete reserved transform. M3 remains open and public
saving remains `2^-66`.

`Fast/CompactTopRuntimeExecution.lean` now discharges actual piece readiness,
packing, layout, primitive guard and record-capacity obligations internally.
Its inputs are original row/address precision, runtime size lower bounds,
reservation capacity and the actual prepared machine state; no per-layer
execution or arbitrary cost premise remains. `Fast/CompactSynRoundSources.lean`
executes the existing chunk-round arithmetic on the shared host to obtain
the stride, phase and current low offset from empty scratch, preserving the
compact bank. `CompactSynRoundGlobal/Rest/Regs/Park/Compose` now check the
individual global reads, rest setup/teardown, register contracts, stash,
configuration push/drop, unstash and sequential frame composition.
`Fast/CompactMainRegs.lean` supplies a fixed expanded main host, injects all
original stages, shares the actual source stream and separates the private
compact bank. Whole-round composition is checked below; integration with
the main-stage contracts remains, and the public machine has not switched
to this host.
`Fast/CompactMainBootstrapRead/CompactMainBootstrap` now execute the concrete
copies from the named original precision register and initial transform
dimension source, then initialize persistent globals with all costs explicit.
The complete chunk-round program is defined in `CompactSynLayerStep`;
`CompactSynLayerStepFrame/Sources` prove the actual singleton outside-row
setup, original counter/global sourcing and source cleanup. This is not yet
a theorem executing the complete round or multiplier.
`CompactMainBootstrapFrame` now verifies preserved original sources and
cleared input copies; `CompactMainConstants` covers the old and compact
state capacities. `CompactSynLayerStepProjection/Wires/Records/Refresh/
Prepare/Basis/Park/Clear/Cleanup/Seq` derive actual record production,
refresh inputs/invariants, source restoration, complete preparation and
parking, and exact final cleanup from the original round invariant.
`CompactSynLayerStepReady/TopRegs/Runtime/Unpark/Compose/Algebra/Cost/Execution`
now close whole-round execution, including the actual top call, restoration
and final cleanup. The theorem starts at the original synthetic round state
with initialized global dimension/guard and a blank compact bank; it returns
the entire original register file with only transformed I/O. Geometry,
precision and array bounds remain explicit caller obligations, but no
prepared-state execution or readiness oracle remains. `CompactSynLayerStepSemantics/Stream` also identify its selected coordinates
and output stream with the original synthetic butterfly round. `CompactSynCompare/Dispatch/MainLegacyRuns/SynDirect/SynMainProjection/
SynHybridRound` now execute the real counter-driven compact/direct choice,
derive both branch executions, retain original butterfly semantics and
restore the entire main file except its source stream. Selected-address fit
and row padding follow from the existing layout invariant and reservation
capacity. Forward/opposite round composition and full loops are the next
execution gate; the main multiplier is not yet switched.
`Cost/CompactTopCoordinates` translates the actual serialized records into
relative layer coordinates without changing row stock or counting the low
offset twice in volume.

Actual runtime cost integration now has checked `CompactCallerFullDimension`
reservation capacity for `d-1`, `CompactCallerWorkingWidth` for the complete
precision shift, and `CompactRoundVolume` for the factor-four padded-volume
envelope. `CompactRuntimePolynomial` absorbs fixed polynomial setup charges
into the actual coefficient count. `CompactSynLayerOverheadBound` includes
all actual overhead and record lengths. `CompactSynLayerOverheadRuntime`
absorbs its polynomial term into `2^15*V + 2*stash` given the caller scalar
polynomial bound. Uniform scalar-budget discharge,
round summation and the stronger public machine theorem remain unfinished.

**Conditional first numerical gate after compact integration:** retain
`epsilon=2^-5` and test `c=2^-3` only after the actual compact caller and
complete costs are proved. The local reservation term becomes
`d^(7/8)*guard`, while the checked active recurrence uses
`d^lambda*guard^tau`. `Cost/CompactInterimParameters.lean` checks exact
candidate stage margins for `lambda'=1-2^-32` and saving `2^-37`; layout
permits `37/3200000000000`, above that candidate layer margin.
The same certificate proves that the old full-width internal estimate
exceeds one at these chunks. Neither changing lambda' nor retaining its old
half-leaf condition repairs that estimate: replace it on the compact path.
Use compact execution only on chunk rounds, whose selected count is the
full original dimension and eventually pays the reservations. Keep the
existing direct early/terminal leaf schedule (no recursive pieces); its
exponent `1-epsilon+epsilon*c=249/256` has ample arithmetic slack.
Small global inputs still need the existing finite-input dispatch. These
are checked parameter inequalities, not a multiplication-time theorem:
actual scheduling, precision, complete control/setup absorption and
executable size generation must pass before updating the scoreboard.

**Actual caller integration gate:** `Fast/SynRound.lean`'s `SynV` starts
all scratch registers empty. The new constructor's `s0=d`, `s1=guard` and
`s7=offset` must therefore be computed or loaded from retained original
parameters, not assumed at multiplier entry. `SynP.D` stores the current
axis-list length; retain the original dimension when selections shrink, and
retain original precision to compute `guard=4*clog2(p)+6` (working width is
not that precision). The existing rest-state initializer also consumes
`p.kh` and `p.rh`, whereas compact configuration production returns only
piece/configuration records and working width: initialize the actual stride
and phase explicitly. Concrete global sources exist: `MainProg.mnUs` copies
original precision into unary `Main.mnIo .dpn` (also `mnRnd .pn`), retained by
`MainCorrect.MnMid`. The initial `SynV.p.D` contains the transform axis
count `d-1`, as established by `DistSynMain.dsyV₀` and `ConvBox.cvAx`; it
must not be treated as original `d`. `CompactMainBootstrapPipeline` now copies this source and charges one
additional tick on retained depth. `PipelineSource/Precision` prove the
actual `d-1` distribution source and the original precision from
`MainCorrect.MnMid.dpn`. `PipelineGlobals/Exit/Compose` provide one corrected
bootstrap per transform, preserved original globals across rounds, and
charged exit cleanup; the source-based composition derives entry execution
internally. `CompactMainBootstrapRuntime` identifies its words with the
exact runtime dimension/guard, and proves round I/O updates preserve them.
`CompactMainConstants` fixes a state capacity covering both the original main
and compact native programs. `Host.embProg` changes register/procedure layouts
but preserves this capacity, so the old `MnPr` programs cannot silently be
reused at a different `Q`. Either instantiate the polymorphic stages at the
new capacity and port their main contracts, or prove exact local-state
transport with an in-image invariant/normalization for `HS.st` and `HS.nxt`.
The existing `Host.liftQ` is for multitape programs. The new checked
`Host/StateTransport` and `Host/StateLift` supply exact host-program transport,
including current/pending states, with unchanged stacks and user data.
A charged one-step normalization admits arbitrary larger-capacity states.
`Host/StatePlacement` and `Fast/CompactMainTransport` now instantiate the
transport for the expanded main machine, with disjoint old/compact procedure
branches and concrete read/parameters/point/round/output wrappers. Their
execution contracts preserve original I/O and the private compact bank.
`CompactMainLayer` supplies the canonical compact procedure branch and
places the actual chunk round on the same main source stream at identical
cost, preserving the full surrounding main register file. The main
forward/opposite specifications, corrected bootstrap placement and complete
main assembly still require integration.
Then compose shared-host setup, record construction,
rest initialization, stash, top execution, pop, unstash and cleanup, charging
every stage and restoring the original round frame. Keep a proved fallback
for selections below the reservation cutoff.

**Checked scan/bootstrap checkpoint (2026-10-15).**
`CompactSynRound` and `CompactSynLoopF/O` now execute complete hybrid rounds
and scans with the original numerical semantics, restored counters and exact
full-register frame except I/O. `CompactSynInitialGeometry/Contract/Loops`
derive initial contracts from actual distributed-transform parameters.
`CompactMainBootstrapView/TransformFrame` derive setup execution from the
real precision and predecessor-dimension registers plus blank scratch, prove
that setup preserves the original synthetic view and establishes readiness,
and prove exact exit restoration. `CompactMainTransformPipeline` composes
these charged boundaries around a core. Full transform specifications and
main assembly remain unfinished.

The scalar caller fields now have a common quadratic precision budget;
`CompactCallerDivisorPolynomial` supplies an explicit dyadic polynomial
bound for the original divisor. `Mult/CompactSizes` provides parallel
eighth-root chunks, `CompactCallerRetunedCapacity` proves reservation
capacity, and `CompactCallerUniformRuntime` proves actual packing uniformly
for chunk sizes between the old size and original dimension. These are
foundations: the executable parameter/distribution bridge and compact total
recurrence still need integration. The legacy total recurrence must not be
reused unchanged at the larger chunk exponent.

The focused compact axiom audit passed for 351 contracts with peak RSS below
4.2 GiB; no full build or limit increase ran. Public saving remains `2^-66`.

**Concrete transform and retuned-cost checkpoint (2026-10-15).**
`CompactSynConcreteTransforms` now specializes both original transform
specifications to the canonical expanded main table, actual `dsyV₀` and
existing forward/opposite layouts. It derives layout execution, complete
scan contracts, bootstrap readiness and cleanup internally. Actual main-stage
and assembled multiplier integration remain separate.

`CompactCallerCombinedBudget/OverheadRuntime` discharge the scalar, divisor,
piece-validity and volume budgets for actual records. The uniform versions
cover every chunk between the legacy chunk and original dimension, with an
explicit eighth-root corollary. `CompactCallerUniformReadiness`,
`CompactPieceUniformPacking`, `CompactTopUniformRuntimeExecution` and
`CompactSynLayerStepUniformRuntime` derive shared shapes, descendant packing
and actual top execution for these larger chunks. Full retuned chunk/scan
composition and coherent executable parameter/distribution changes remain.

`CompactCallerGuardPower/LayerGrowth` prove that the actual original-precision
guard fits any positive original-dimension power, with dyadic coefficients,
and absorb its factor in the closed compact recurrence into the proposed
layer exponent. This replaces the obsolete chunk-width penalty at that
analytic step; a complete compact transform/total bound is still required.
The focused axiom audit passed for 378 contracts, with peak RSS below
4.2 GiB; all new modules passed guarded single-file checks. No full build
ran and no proof limits were raised. Public saving remains `2^-66`, with
`2^-37` the next integration target.

**Executable retuning and stronger top-cost checkpoint (2026-10-15).**
`CompactParamProg/Pipeline` compute the eighth-root chunk in the actual clean
parameter table, charge every operation and clear the arithmetic scratch.
`CompactDistRetune/Dist` run actual distribution and replace only the chunk
slot and its unary output. `CompactDistWires/Exec` rebuild the synthetic
initialization contract with the new chunk, block count, twiddle positions
and permutation; `CompactBundleMnLay` supplies the corresponding executable
forward/opposite layouts. These changes preserve the legacy route.

The uniform round/scan/full-transform contracts compose the same checked
programs at the larger chunk size. `CompactSynRetunedTransforms` derives
complete concrete forward/opposite specifications for the actual eighth-root
initial wires and layouts, without supplied geometry or execution contracts.
`CompactSynMainFrame/Entry` and `CompactSrcMachine/Frame/Base/Stages/MainStages`
derive source-stage entry from the existing main invariant and run actual
expanded source stages with exact costs. Expanded main-chain composition
and recursive entry-table assembly remain to be closed.

`CompactRetunedReservationGrowth` proves that the complete actual reservation
is bounded by a dyadic coefficient times any dimension power above seven
eighths. `CompactRetunedTopGrowth/Cost` combine this with guard absorption
and the closed recursive bound: the actual complete top program, including
kernels and controls, fits the proposed compact layer exponent. Full round,
loop and total cost matching remain; these top bounds retain explicit
concrete address-geometry premises. The focused axiom audit passed for 433
contracts with peak RSS below 4.2 GiB. All new modules passed guarded
single-file checks; no full build ran or proof limits increased. Public
saving remains `2^-66`.

The next checked bridge specializes the top-cost geometry to actual caller
records and proves the full-dimension capacity slack. The retuned distribution
bundle now runs from the original distribution precondition, with dyadic costs,
and establishes the placed transform entry state. Restricted-call transport
also permits replacing the main entry while preserving recursive layer execution.
`CompactGrowth`, `CompactStageGrowth` and `CompactTotal` prove the complete
analytic stage envelope at saving `2^-37`, including unchanged point products,
resampling and direct CRT costs. This remains conditional on matching actual
machine runtime to that envelope: full transform-cost matching and expanded
main-chain assembly remain open. Public saving is still `2^-66`.

Actual chunk-layer costs now discharge caller geometry and volume obligations;
the direct branch is also matched to the retuned convolution envelope. Complete
retuned source transforms execute under an arbitrary expanded main entry, and
legacy primitive transport preserves the private bank with one charged step.
The main-cost bridge accounts for unchanged primitive costs, fixed wrapper
normalizations and expanded-host cleanup. Its stronger asymptotic conclusion
still requires the actual source-run cost bound. Loop summation and whole-chain
execution assembly remain open; these contracts do not advance the public bound.

Both actual compact loop directions now fit the retuned convolution envelope
under an explicit stash budget. Expanded-host source costs are also matched,
and `compactMain_runs_time_isBigO` reduces the complete main-time estimate to
the sum of the two complete transform costs. Actual stash/layout/bootstrap
closure and whole-main execution assembly remain; the public bound is unchanged.

The complete cost estimate is now closed. `compactRetuned_transform_cost_le`
includes actual layouts, stored wires, original-source bootstrap, both loop
directions and cleanup. `compactRetunedTime_isBigO` instantiates the actual
retuned distribution and transform costs and proves the full main-time envelope
at saving `2^-37` without stage-cost hypotheses. The remaining condition in
`compactRetuned_mulInTime_of_exec` is eventual actual execution of the assembled
main within this estimate. Until that condition is discharged, the public
fixed-machine saving stays `2^-66`.

Prove complete temporary address ranges survive every role split, arbitrary
initial temporary values are restored, and exceptional extraction, sorting,
reinsertion and cleanup are charged at each node's own volume. Add an actual
stopping branch at `e < d^beta` and price the reserved/individual axes.
The target exponents are internal
`tau+(1-beta) max(sigma-tau,0)`, leaf `sigma+beta(1-sigma)` and reservation
`max(1-c,0)`, all strictly below `lambda'`. Current `MatchSynPcs` instead
matches recursion down to level zero, so changing its recurrence on paper
would not change the executed algorithm.

**M4 — linear semantic precision and selected workspace.** The older guard
uses `d^20`; the compact intermediate guard uses `d^(5-4 beta+zeta)`; the
semantic completed-child argument supports a **linear** `C0 d` guard. Prove
completed-child norm/denominator bounds on every role, then an induction on
maximum active child width including literal scalar work and parked operands.
Match it to the actual local word-width calculation; these three published
guards are not interchangeable implementation claims.

For variable-rank recursion, prove explicit simultaneous row-stock envelopes
and bootstrap cutoff validity. The upstream selected-stock audit leaves the
selected reserve coefficients unknown. Derive them from the actual selected
compiler, leaf borrowing and call depth; the enormous recorded headrooms
cannot substitute for that proof.

**Done means:** a Mathlib layer machine with the compact/stopped cost, linear
precision and proved workspace contracts. These remove constraints preventing
large c and, later, large epsilon; neither alone removes §6's layout loss.

**Stopped-piece scanner frame checked:**
`Fast/CompactStoppedScannerRecord.lean` wraps the existing charged rebase/record
program, preserving the digit scanner's arbitrary live quotient and prefix
lists and restoring its original unary power/depth counters. It uses spare
wires 24 and 29–31; live wires 27/28 and the supplied cutoff on 22 are preserved.
Its full-frame execution theorem and exact save/restore costs pass guarded
checking and the standard-axiom audit. The leaf count, serialized stopped
record, offset and accumulated exponent receive their proved updates. Runtime
cutoff provisioning, replacement of the complete digit loop, precision and
stopped-layer cost matching remain; this is not yet a stopped scanner theorem.

**Full supplied-cutoff scanner checked:** `Fast/CompactStoppedDigBody.lean`
and `CompactStoppedDigits.lean` execute the entire digit scan. Nonzero digits
emit the literal stopped record and recomputed exponent; zero digits emit
nothing. The tail clears the actual rebased leaf count, and every saved/live
wire is restored. Exact costs include each pass's live-prefix length and the
save/restore overhead. Both guarded checks and the three contract axiom audits
pass at default limits. Runtime cutoff computation, semantic stopped-piece
identification, precision, caller replacement and layer-cost absorption remain.

**Semantic stopped records and cutoff execution checked:**
`Fast/CompactStoppedDigitsSpec.lean` identifies emitted fields with `topPcRec`
of the existing actual `synPcs` mapped by `compactStoppedPiece`; their recomputed
exponents agree with summed `expSeq` and actual `expZ`. The semantic execution
corollaries retain the exact frame and cost. `CompactStoppedCutoff.lean` computes
`Nat.log m T` from a generic preserved source of positive length `T`, emits its
unary cutoff and returns scratch empty. Both modules and their seven theorem
axiom audits pass. The threshold is still supplied; selecting/generating it
from the global budget, composing the caller, precision and complete layer-cost
absorption remain explicit obligations.

#### §6 — Synthetic transforms and their tape layout

**M5 — remove the multiplicative layout loss.** The existing synthetic loop
pays `p K^(tau-1)`, giving saving `epsilon c a_b`. The selected assembly prices
coordinate movement as `p^tau polylog p`, giving saving `a_b`, and uses a
balanced prefix with saving `1-epsilon` instead of `1-epsilon(1+c)`.

Trace the balanced positional transform and arbitrary-source routing contracts
behind the selected outer engine. Implement the corresponding transform
schedule, not just the cheaper analytic formula. Prove both forward and
opposite transforms, original frequency order, untouched spectators and
restoration, retaining the synthetic-character and convolution identities.
Primary integration points: `Fast/SynLay*.lean`, `Fast/SynSel.lean`,
`Cost/MatchSynLay.lean`, `Cost/MatchSynPcs.lean` and `Cost/MatchSynLoop.lean`.
Keep `epsilon(1+c)<1` as a geometric condition even after balancing; the
selected analysis does not require its gap to exceed the final saving.

**Done means:** actual transform/layout steps obey the new charge and compose
with M3–M4. This removes today's active bottleneck and is essential even with
perfect finite suppliers.

#### §7 — Exact normalized polynomial products

Keep exact signed packing, the conventional fast multiplication subroutine,
negacyclic product semantics, normalization and truncation. Recheck input word
widths, carries, product separation and the logarithmic factors under the new
parameters and supplier guard constants. Integration points include
`MathlibTM2/Fast/RingProd.lean`, `Host/SSMul.lean` and `Cost/Growth.lean`.

**Acceptance within M4/M8:** the packed-product charge is below the requested
final exponent with strict room for logarithms and exact output semantics.
No separate supplier or polynomial-product rewrite is justified yet.

#### §8 — Resampling with the permutations left in the transform

**M7a — faster Gaussian inverse, with quantitative errors.** The local
`7/8+3 epsilon/2` estimate cannot allow the selected epsilon near one.
Trace the selected phase-cell/banded inverse argument: one global rounded
matrix, bounded inverse norm, short convolutions and boundary solves. Prove
the same matrix and rounding errors used by the implementation. Existing
`NLogN/Neumann*.lean`, Gaussian and resampling lemmas are candidates for reuse;
they do not by their names establish the new banded inverse theorem.

**Checked M7a foundation:** `NLogN/PhaseCell.lean` uses the existing
`nearest`, `beta` and `normExp`, proving the exact affine offset relation on a
constant integer phase, the Gaussian-distance/diagonal-potential factorization
of each lattice coefficient, positivity and upper bounds on similarity weights.
All 12 declarations pass the standard-axiom audit; guarded single-file checking
passes at default limits. This is not yet a statement about the full periodic
matrix: alias sums, truncation and rounded inverse/boundary algorithms remain.

`NLogN/PhaseCellScan.lean` additionally gives an executable integer
addition/comparison scan, exact remainder invariant and exact phase/offset
outputs at every natural physical index for `0<s<=t<2s`. At most one correction
is needed per step. Guarded checking and all seven theorem axiom audits pass;
tape encoding, physical cell/boundary selection and bit costs remain open.

`NLogN/PhaseCellIntervals.lean` proves phase monotonicity, physical cell
contiguity, the strict within-cell gap and the selected `4d+1` upper cardinality
bound, including truncated end cells. All nine theorem axiom audits and guarded
checking pass. Physical boundary extraction and any required full-cell lower
bound remain separate; no end-cell lower length is assumed.

`NLogN/InversePerturbation.lean` supplies the quantitative operator bridge:
an exact inverse of norm at most `M` and actual perturbation at most `eta`
with `M*eta<1` give a two-sided inverse of norm at most `M/(1-M*eta)` and
inverse difference at most `M^2*eta/(1-M*eta)`. The half-gap specialization,
guarded checks and both theorem axiom audits pass. The selected rounded
operator and its approximation bound still have to be constructed and proved.

`NLogN/PhaseCellRounded{,Error}.lean` constructs rational within-cell blocks
from shared P-grid Gaussian samples and rounded similarity weights, with literal
unit diagonals, band zeros and exact diagonal similarity. The actual floor
rounding guarantees imply in-band coefficient error at most `3 eta/r^2` under
a certified denominator bound `r+eta<=weight(k)`. Both guarded checks and all
14 theorem axiom audits pass. This floor is a noncomputable rounding
specification, not the selected corrected exponential evaluator; its four-unit
error, the selected lower weights, cross-cell and periodic terms, truncation,
row/operator norms and execution costs remain to be proved.

`NLogN/PhaseCellWeightBounds.lean` discharges the denominator premise from
the selected gap/normalization budgets: exact weights are at least `2^(-8p)`,
and precision `2^15*p` preserves positive rounded weights and proves the actual
ideal-grid entry-error bound. All six contracts pass guarded checking and axiom
audits. `PhaseCellExpSample.lean` separately reuses the executable `expPiNat`
Taylor evaluator, subtracts two and clamps at zero, proving downward rational
samples within four grid units. All seven theorem audits and guarded checking
pass. This corrected sample need not equal the ideal floor. Mapping actual
phase-cell rational arguments, replacing ideal coefficients, executing the
correction and matching its Mathlib backend costs remain integration work.

`NLogN/PhaseCellExecutableCoefficients.lean` now replaces ideal floor samples
with corrected executable exponential samples in an actual rational kernel and
entry constructor. Exact diagonal similarity, distance symmetry and coefficient
error at most `12 eta/r^2` are proved from explicit rational-target mappings and
positive denominator margin. Guarded checking and all nine theorem axiom audits
pass, reusing the exposed `PhaseCellRounded.ratio_error` estimate. Concrete
phase arguments and their selected margins are being connected; cross-cell,
periodic, tail/operator and tape-cost obligations remain separate.

`NLogN/PhaseCellRationalArgs.lean` computes nearest rounding by integer
division and constructs rational phase-potential/Gaussian exponents, proving
exact agreement with the existing real definitions and lossless nonnegative
natural encoding. All 15 declarations pass the axiom audit and guarded checking.
`PhaseCellConcreteCoefficients.lean` instantiates the executable coefficient
constructor with those actual arguments. At selected precision `2^15*p`, its
four-unit error leaves positive weights and yields exact similarity and entry
accuracy without mapping/denominator oracles. All fourteen theorem audits and
guarded checking pass. Cross-cell coefficients, periodic aliases, tails,
operator row bounds and tape costs remain integration obligations.

**M7b — bulk exposure and microbox tape execution.** Build ordered core/halo
windows of that same rounded matrix, bound truncation/locality errors, retain
period cuts and show tensor errors accumulate without a volume factor. Price
sequential window emission, factor-page reuse, overlapping tapes, cropping
and final prime-box order. The inherited construction uses core length about
`p^8`, halo about `p^3` and a band with `w^2 = O(p^(1-r))` where
`alpha^2 ≍ p^r`; the exact selected contracts must be bound before porting.

The target Gaussian arithmetic saving is
`min(1-epsilon-delta, r-delta)`, with `epsilon+r<1` and
`epsilon>(1-r)/2`; bulk exposure has saving `a_b`. Reprove prime supply and
normalization when epsilon increases: a cited short-prime-interval result
must be available as a proved local theorem or replaced by a sufficient
proved construction, not introduced as a custom axiom.

Primary integration points are `Fast/ResampA*.lean`, `Fast/ResampB*.lean`,
`Mult/Sizes.lean`, `Cost/MatchResampA.lean`, `Cost/MatchResampB.lean` and the
`NLogN` analytic library. M2's cheaper routing is a useful earlier waypoint,
but does not prove the new Gaussian or bulk bounds.

**Done means:** implemented forward/inverse maps satisfy the required errors,
normalization, fixed-machine time and selected parameter bands. This is a
major analytic and execution task, not an arithmetic certificate bridge.

#### §9 — Exact integer multiplication and its cost

**M8a — seven-stage bootstrap.** The selected assembler starts at saving
`384599/10^10` and iterates
`a_j = (1-s)s + s a_(j-1)` seven times, with
`s = min(bit_endpoint,(1-beta) complex_endpoint)-10^-27` and
`beta = eta = 10^-24`. Prove each transfer theorem on machines, including
stock, cutoffs, labels and the base construction at that saving. The base
saving `0.0000384599` is itself not supplied by our present theorem: it
requires the corresponding earlier construction or an alternative proved
base strong enough for the recorded seven-stage chain. Substituting our
current tiny saving silently changes the chain and its final certificate.

**M8b — close the selected 47 inequalities and exact recovery.** With the
bootstrapped bit saving `a` and complex saving `b`, the inherited balanced
outer engine chooses `q=a(1-2 eta)`, `c=q+eta/4`,
`epsilon=(1-eta)/(1+q)`, `lambda'=1-q` and an intermediate lambda.
At the selected witness, `epsilon ≈ 0.9983273398029231` and
`c ≈ 0.0016754626768081034`. Its limiting margin is `epsilon q`,
tending to `a/(1+a)`. This replaces our
current `epsilon c a_b`; simply substituting primitive endpoints in our
existing formula cannot reproduce the selected target.

The seven selected margins are:

| Charge, by manuscript section | Selected saving |
| --- | --- |
| §6 balanced prefix | `1-epsilon` |
| §§4, 6 coordinate movement | `a` |
| §5 compact phase layer | `epsilon q` |
| §8 bulk exposure | `a` |
| §8 Gaussian arithmetic | `min(1-epsilon-delta,r-delta)` |
| §§7, 9 scalar work | `1-epsilon-delta` |
| §9 dimension | `epsilon` |

The selected constraint ledger divides into the following **47** entries.
These are acceptance obligations, not 47 completed local theorems.

| Original sections | Count | Exact constraint names in the pinned assembly |
| --- | --- | --- |
| §3 and §5 primitive/stopping ranges | 6 | `bit_positive`, `complex_above_bit`, `complex_below_one_over32`, `beta_positive`, `beta_below_one`, `leaf_saving_above_bit` |
| §5 internal/leaf recurrence | 9 | `q_positive`, `q_below_internal`, `q_below_leaf`, `lambda_above_tau`, `lambda_above_sigma`, `lambda_above_internal`, `lambda_prime_above_lambda`, `compact_leaf`, `lambda_prime_below_one` |
| §5 compact reservations | 4 | `c_positive`, `c_below_one`, `q_below_reservations`, `compact_reservations` |
| §§5, 6, 8, 9 geometry, guard and prime supply | 7 | `epsilon_positive`, `epsilon_below_one`, `guard_width`, `K_geometry`, `K_dominates_log`, `record_suffix`, `prime_interval_packing` |
| §§8, 9 Gaussian precision and normalization | 9 | `phase_local`, `phase_boundary`, `gamma_sublinear`, `cell_above_band`, `alpha_positive`, `alpha_below_one`, `alpha_below_one_fourth`, `delta_positive`, `delta_below_one_eighth` |
| §§4, 6, 8 routing/window allowances | 3 | `short_record_fallback`, `small_field_exposure`, `artificial_boundary` |
| §§3, 5 literal work and row stock | 2 | `literal_scalar_guard`, `row_product_gap` |
| §9.8 final stage absorption | 7 | The seven margin names above, each with suffix `_above_kappa`. |

For each of the 47 constraints, attach its exact rational proof to the local
semantic/cost lemma it enables: identifying a stage is not yet a proof of its
contract. In particular, satisfying a number without that lemma does
not discharge the obligation. Reuse exact product recovery, chirp correctness,
CRT algebra and carry output only after the changed precision, scaling and
permutation contracts are established. Include small-input dispatch.

**Done means:** unconditional
`MathlibTM2.MulInTime (836330098538459 / 500000000000000000)`, one fixed
finite machine, all input pairs, actual-step bounds and the existing standard
axiom set. The source record's assembly hash checks out; cold supplier replay
and all these Lean bridges remain unfinished.

#### §§10–11 — Division, square root and matrix transposition

These are downstream consequences, not inputs to multiplication's saving.
Do not put their formalization on the critical path. After M8, adapt their
reduction interfaces and encoding overhead if those corollaries are desired.

## Execution order and decision gates

1. **M1 complete, historical:** public saving `2^-93`; exact internal margin between
   `2^-93` and `2^-92`, with the existing existential theorem preserved.
2. **M2 complete:** actual linear direct CRT and linear resampling costs feed
   the public fixed-machine theorem. Final retuning proves public saving
   `2^-66`, with exact margin `296/(10^11 * 2^37)`.
3. **M3–M5:** compact controls, width/stock contracts and balanced coordinate
   routing. Establish these interfaces first using the current smaller
   networks. Prove and record intermediate unconditional bounds after each
   complete integration; do not promise a numerical waypoint before costing it.
4. **M6 and M7:** port the selected suppliers and the sharper Gaussian/bulk
   pipeline against those established interfaces. Neither branch alone
   yields the goal; both feed M8. Source-contract analysis can begin earlier.
5. **M8:** prove the bootstrap base and stages, close all 47 linked obligations,
   validate exact recovery and publish the target theorem.

At every gate, record the achieved saving, the minimum remaining cost margin,
its manuscript section and the next binding lemma. A milestone can finish
without changing the bound, but must say which restriction it removed.
Retain reusable frame/rank/precision mathematics until its role is resolved.
Use only guarded Lean scripts, preserve proof limits and integrity, exclude
unrelated work, and commit/push each checked logical section. The original
planning update checked the selected bootstrap and final-margin
arithmetic against the pinned assembly. M1 and M2 have checked
Lean machine theorems and focused axiom audits; M3–M8 remain unfinished.

## Completed compact integration checkpoint

The public `MathlibTM2.mulInTime` now proves saving `2^-34` unconditionally,
after the dyadic dimension retune and fourth-root chunk integration. The earlier
eighth-root dimension and logarithmic retune proved `2^-35`.
The intermediate sixteenth-root result proved `2^-36`; the original compact
result proved `2^-37`.
`CompactFinal.compactRetunedPrefix_exec` composes actual input/parameter/distribution
execution, the fifteen-stage chain and canonical output. `CompactMainHost` bounds
all cleanup using a finite push constant and installs the completed main in the
actual recursive table. Small-input dispatch produces one fixed finite Mathlib
machine for every input pair. The source prefix uses thirteen normalization steps,
within the sixteen-step allowance. No execution or cost premise remains in
`compact_mulInTime`; earlier progress paragraphs above describe historical gates.
M3 remains yellow only for stopped recursion and local repair work needed for
later improvements; M4–M8 and the selected state-of-the-art goal remain open.

### Completed sharper logarithmic estimate and eighth-root integration

The old `epsilon<1/12` condition belonged to the coarse resampling cost
estimate. The checked sharper Schönhage–Strassen logarithmic loss is now
`delta=2^-5`, using logarithm exponent `2^-6` and dyadic coefficients `2^7`
and `2^14`. Actual multiplication and rounding costs use this sharper budget;
the Gaussian margin is `1/4-delta-3epsilon/2`, equal to `2^-5` at the actual
`epsilon=2^-3`. Both executable dimension-root calls use exponent three.

All 294 affected dependencies passed guarded single-file verification. The
complete-proof axiom audit passed for 124962 declarations and the focused
compact audit passed for 565 contracts. At that checkpoint the public theorem proved
`2^-35`; this includes every input, actual costs and fixed-machine assembly.

`CompactDimension.Eighth.supplier_obstruction` proves that the current complex
supplier cannot reach `2^-34` at this dimension, even with an ideal layer bound.
`fourth_root_gaussian_obstruction` proves that the present resampling estimate
cannot support `epsilon=2^-2` even at zero logarithmic loss. Both are checked:
the next structural improvements must address these restrictions rather than
only doubling the dimension again.

### Completed further dyadic parameter route

The actual multiplier now uses `epsilon=9/64`, `c=1/4`, logarithmic loss
`1/32`, and layer gap `57/2^37`, with public saving `2^-34`. The executable
dimension stage computes `d=iroot64(b^9)`, returning scratch clean; its widened
parameter word is `4*size(n)+32`. Literal prelude, setup, fourth-root overwrite,
distribution and machine costs are matched to those parameters. All 298 affected
dependencies and both final audits passed. Internal dimension/layer parameters
are exact dyadic rationals; the public saving remains a pure power of two.

The checked supplier ceiling still excludes `2^-33` with the existing supplier
and coarse Gaussian restriction. The selected-supplier and resampling milestones
are therefore required for progress beyond this parameter route.

### Selected-supplier integration boundary

Initial inspection found no Lean replay certificates for the selected suppliers.
The complete pinned PR589 scalar word, arbitrary-dirty endpoint, source/helper
restoration and finite661-register execution are now checked. Existing
Shared50/Paired49 and h25 proofs concern different suppliers. Selected framed
restoration remains open: actual occurrence-indexed frame updates and the
scatter COPY boundary must be interpreted explicitly before applying existing
framed/finite restriction machinery. T16 now has checked complete native-event
label continuity in both orientations; this does not prove its frame operators
or dirty scalar endpoint.
For T16, the physical owner schedule and its literal occurrence-indexed child
rank profile must also be proved. The existing uniform `factorCount` recurrence
cannot consume a variable-rank histogram by changing a scalar constant; it
requires a weighted moment recurrence including source/frame/owner costs.
`Layer/OccurrenceRecurrence.lean` now proves the occurrence-indexed induction,
per-call rank/size power estimate and exact uniform-volume moment identity.
All four contracts pass guarded checking and the standard-axiom audit. The
actual selected execution recurrence, decreasing child sizes, per-call ranks,
complete local/leaf costs and numerical moment certificate remain explicit
instantiation obligations. This work is separate from the small parameter
improvements above.

`Layer/SelectedMoments.lean` proves the exact selected bills with integer certificates for the rational powers: T16 at `a = 7/4178` (native, and with the conservative surcharge) and PR589 at `a = 10/5769` with its surcharge. The T16 occurrence list (144 scheduled calls plus residual inventory) is proved a permutation of the histogram from `selected_profile_cost`, giving the moment in `rank_moment_le` form; `M6/BitSchedule.nodeChildren_realizes` proves the PR589 schedule histogram, and `M6/BitNodeCost.five_moment_le_one` checks its five-class moment. `M6/BitDescriptorRecurrence.five_descriptor_closed` derives the child widths and volume weights from the role split and retained rank fields. Applying it to the tape machine requires proving that execution produces those descriptors and meets the per-node time bound. `Cost/BranchingMoment.lean` restates the layer branching hypothesis as the uniform occurrence moment, with h25 as its instance; the variable-rank moments enter only once the layer machine has per-occurrence child sizes. `Layer/VariableRecurrence.lean` is the size-indexed replacement for `Recurrence.recurrence_closed`: a node costing `C₁((Ke)^τ+1)` plus weighted child-occurrence costs, with `Σ w (r/m)^λ ≤ q < 1` and `Σ w (r/m)^σ ≤ 1`, costs at most `2C₁/(1-q) K^τ e^λ + C₀ e^σ u^(1-σ)`; ranks `≤ R < m` turn the single moment at `σ` into `q = (R/m)^(λ-σ)`. `t16_variable_closed` instantiates it with the checked T16 occurrence list (`m = 73`, `W = 14336`, ranks `≤ 48`) at `σ = 1-7/4178` and every `λ > σ`. The remaining premises are execution facts of a variable-child layer machine: child sizes `≤ (rank/73)` of the parent and the per-node cost inequality. A rank-`r` child `C^{⊗rf}` is exactly `r` commuting slot children, so T16 also fits the uniform recurrence: its total rank mass `1,041,408 = 73·14336 - 5120` gives `F/W = 72.643 < 73^{1-a}` for every `a < 0.00114`, far above the current layer bottleneck; the variable-rank machine is then needed only to reach the full `7/4178`.

T16 semantic progress (`Networks/Certificates/T16`): `PauliCanonical`, `PauliSchur`, `PauliCorrection`, `BinaryElimination` and `PauliLowering` give the canonical complex word of every native frame, soundness of the source's tableau-plus-zero-state test, and `edge_lowering` (every transition is a monomial, `S C_r S` and a monomial, up to a Pauli and a scalar, with `r` the certified rank), replacing the 2,896 serialized recipes. `Trace/Framed` and `Trace/Action` prove that both native local words act on arbitrary dirty inputs by `(X,Y,H,P) ↦ (X,Y+X,H,0)` and `(X-Y,Y,H,0)`. `Streams/*` certifies the global eight-stream data composition for all 16 replicas and 112 ports, for every Fourier character at once (kernel check over packed `Z/4` frame vectors, sound for every operator homomorphism), and proves each port's full frame is `C_all`. `Impl/*` closes the node-level bridge: `nodeProgram` is an explicit program of rational gates and primitives (translation kernels `kernel q v`, address permutations, diagonal `Z/4` phases, scalars) on the 14,336 families and 8 private centres, and `nodeProgram_cAll` proves it applies `C_all` to every family for every representation of the 73-bit operators (so also for the machine's column tensor powers). Each of the 144 local invocations wraps its 704 registers through orthogonal charts (identity or basis-coordinate swaps for data, slice-first basis orders for helpers), adapts data registers by rank-zero lowerings between stream-frame kernel lists and native labels, unwinds helpers by the inverse monomial halves of their own split transitions, and runs a word whose edges are the primitive lowerings of their exact frame transitions (5,586 child calls per word); `call_correct` matches it to the stream events under data facts checked by the kernel for all 144 calls. No cover classes or `X_δ` corrections are needed. `nodeProgram_children` proves the program makes exactly `F = 1,041,408` child calls (odd kernels): the data adapters are rank-zero (their stream-frame odd vectors are orthonormal low port basis vectors spanning exactly the native labels), helper wrappers are monomial, each invocation makes the 5,586 calls of its word, and the idle phases make the remaining 237,024. `Impl/NodeReady` lowers it to `machineProgram`, a program of odd factors, translations, slot XORs, slot phases `i^{c x_i}`, unit scalars `i^c` and rational gates with the same action and the same `1,041,408` child calls: permutations are transvection words, quadratic phases are slot phases with XOR-conjugated cross terms, and every lowering scalar is a fourth root of unity because native realizations are Gaussian-dyadic unitaries (`T16/Dyadic`). Translations need no child calls on the machine: reversing a wire's record order is the translation by `𝟙` together with a spectator relabelling, so `T_w = rev ∘ M⁻¹ ∘ rev ∘ M` for a slot-XOR basis change `M` with `M(𝟙+w) = 𝟙`. Remaining is the machine: cheap translations (`kernel 2 v`; the stream schedule alone needs at least 7,168 per node, against a slack of 5,120 children, so they cannot be child pairs), general permutations and quadratic phases from slot XORs and phase passes, private scratch, dyadic gate coefficients, and retargeting the node from `m = 25³` to `m = 73`.

**PR589 local exponent.** `BitPackedRecurrence.five_packed_root_closed` requires both `1 - bitSaving < lam` and `τ ≤ lam` for the internal-node toll exponent `τ`. The current `BitBorrowedSweep.PackedStageExecution` charges local work at `BudgetBound.tau`. In the PR97 instance this is the stage-1 exponent `1 - 3734039/10^12` (`Stage2Machine/Bound.lean`, `Global/Branching97.lean`), strictly above the integrated stage-2 exponent `1 - 123899714039/10^15`. Thus even supplying all private-worker initialization and endpoints at their advertised costs would leave this direct recurrence too weak to improve stage 2. In `borrowedWorkerCost` the width power already occurs in both the row-swap tariff and the full-width leaf exchange. A better exponent requires a sharper bound on their aggregate contribution or a different realization of those operations; changing a width-independent stage coefficient cannot suffice.

The compiled inherited COPY charts in `M6/BitActiveCopy.lean` make the obstruction quantitative. Each direction of `copySweepPort` charges seven exchanges on the full role volume at caller atom width, before the role-specific sweep conversion. Packing once around the whole child via `activeCopyWorker` reduces the number of passes. Even one such charge is too large for the direct recurrence: `copyExchange_exceeds` proves that, for any fixed rate and any exponent below `BudgetBound.tau`, the charged `coreCost V w + 1` eventually exceeds that rate times `V w^exponent` for every positive volume. The result applies on aligned widths as well. It bounds the advertised charge only. A tighter execution bound, a route operating at a separately chosen atom width, or a recurrence that prices the route on sufficiently smaller volumes would require a different estimate.

The alternative of charging routes as extra recursive children has an exact necessary test. For children of the same volume as a scheduled child, the five-copy schedule has parent capacity `64 * 142080 = 9093120` at exponent one, and `BitDescriptorRecurrence.scheduled_rank_sum` gives used rank mass `9041760`. Only `51360` rank units remain across the entire node. Even `7338` extra rank-seven children exceed capacity; decreasing the exponent increases each normalized child weight. Apply this test to the actual route multiplicities before constructing a recursive route worker. The previously studied Bruhat realization, estimated at 4.5 rank-seven calls per role, already fails it by a wide margin (see [the route audit](../docs/pr589-hole/pr589-hole.tex)). The existing `swapVolumeRate_div_width_le` divides the tariff by a fixed rank power and therefore changes only its coefficient for the 64-atom node.

For the implemented borrowed data route, the obstruction already occurs during entry to one noninitial scatter chart. `BitRouteRun.dataRegister_route` uses `stageRoute_runs` on each of 222 data owners. Its two upper factors each reverse 64 label columns before and after a triangular pass (`LabelRoute.upper_runs`). Each reversal moves all 64 positions, so any list of pair swaps implementing it has at least 32 entries. With the current pair-swap implementation charging one interchange of width `64*w` per pair on one role volume, even seven data owners on a single entry would consume at least `7*4*32*64 = 57344` extra rank units in a recursive-call accounting. This exceeds the whole-node slack of 51360 before COPY helpers, exits or the other invocations. This counts the chosen decomposition, independently of the coarser 252-call tariff. Reducing that tariff to the exact swap-list length cannot rescue direct recursive substitution; a viable replacement must change how the chart is executed or avoid materializing the chart transition.

**Common-coordinate COPY.** The flat borrowed scatter now uses `commonScatter_stage` directly. Decoding the nine-window COPY action with `Copy.decoded_scatter` gives exactly `borrowedScatter` on every live register at every label. This removes the outer chart entries, per-window routes, and chart exits together. `borrowedPieces_nodeCost` now charges the nine sweeps only linear local work plus the scheduled children, and `borrowedNode_parentCost` instantiates the sweep's extra full-width core count with zero. The recursive worker now uses the same common coordinates. `commonCopyWindow_layout` places the source, temporary and two basis passes around its rank-seven child. `borrowedWindows_host` composes all nine fanouts and `borrowedScatterSchedule_host` supplies the resulting program to the invocation with zero chart and full-width leaf charges. The COPY packing cost is addressed below. MOVE workers and idle operations still require tighter costs.

**First-use helper packing.** Even with common-coordinate COPY, the outer sweep still packs helper owners. At the first invocation all prior slots are `none`, so `scheduledSlotChanges` emits all 439 distinct helpers. Project each digit in `helperFieldOrder` to its side of `ChartAxis ⊕ ChartAxis`. The input has side word L^64 R^64; every packed slot has L^8 R^8 L^56 R^56, independently of the within-side order. The number of right-before-left pairs thus rises from zero to 448. An adjacent swap changes it by at most one. Consequently the current `helperLabelPacking` realization needs at least 439 × 448 = 196672 adjacent field exchanges just for entry to the first invocation. Giving each a same-volume rank-one child already exceeds the entire node's 51360 spare rank units. This rules out that substitution even if every later slot transition were free. It does not lower-bound the runtime of a batched exchange. A replacement must handle the group permutation at a different cost or let the invocation consume the helper's inherited layout.

Batching adjacent swaps into larger physical field exchanges still fails the same-volume recursive-child test if the present per-owner stage boundaries are kept. Across the cut after field 64, eight independent right inputs appear on the left after packing. Over the prime field, this off-diagonal submatrix has rank eight, so the physical permutation `P` satisfies rank(P − I) ≥ 8. The inverse has the same displacement rank. A rank-r interchange changes its two arguments by (−z,z) for z in an r-dimensional image, and conjugating the interchange preserves displacement rank. Telescoping a product therefore bounds its displacement rank by the sum of its exchange ranks. Each stage starts by packing 439 distinct owners. By `helperCharts_unvisited` all those owners still have a slot at the end, even if a later invocation changed its position. Restoring any such slot costs at least eight more rank units by the inverse calculation. Even ideal per-owner batching would thus charge at least 9 × 439 × (8 + 8) = 63216 units, against 51360 available. This test assumes same-volume exchanges as the only paid coordinate changes and fixed physical layouts at the stated boundaries. An implicit layout carried into the invocation, or a joint realization eliminating a boundary, requires a different analysis.

**Scalar gates in inherited helper order.** The first scalar block, D, already combines different physical layouts. Its 111 targets are data registers 111–221; all 18085 source occurrences are helpers. Gate zero reads 202 helpers. Every D gate has frame zero, so these reads occur before a frame change could align the operands. The 111 × 439 binary matrix of source incidences has rank 111 (row elimination on the literal `PR589/D.lean` source lists, toggling a bit for each occurrence). Thus a scheme that first forms a fixed set of whole-word helper sums and then uses only scalar combinations of those sums to feed all D targets needs at least 111 independent sums per invocation. Charging even one same-volume rank-one child for each such sum at all 160 invocations and nine stages costs 159840 rank units. This excludes a separately materialized D with that pricing. It leaves open fusion with the surrounding circuit or an implementation that handles cross-layout sums without separately charging such children.

Grouping D's sources by inherited slot position gives a sharper test for implementations that form partial sums separately at each position. At stage zero, gate zero's 202 source occurrences split as 75, 60 and 67 at positions 0, 8 and 16. Restrict the 111-row incidence matrix to each of those three column sets. Their binary ranks are 99, 101 and 100, so recovering all D outputs from separately computed linear summaries needs at least 300 summary words at that stage. Repeating the calculation for stages 0 through 8 gives sums of restricted ranks 300, 256, 434, 433, 437, 434, 300, 433 and 314. Charging one same-volume rank-one child per independent summary across 160 invocations costs at least 534560 rank units against 51360 spare. These figures come from direct binary elimination on the literal D source lists, replaying `idlePositions`, `idleStages`, `numberHelpers` and `slotPos` from `BitHosting.lean`; they are computational diagnostics outside the Lean proof. This test leaves open a fused circuit or a linear-time physical pass for the cross-layout contribution.

The literal scalar word admits a deferral. `PR589/DeferredTargets.lean` checks that none of the 5583 gates reads a target register as a source and all D writes land on targets. Consequently the complete scalar output equals the A/scatter/B/C suffix on the original input plus the initial D correction. This allows the scalar proof to accumulate D at the endpoint. A physical implementation still owes the framed transport of that correction and its cost.

**Idle handoff for the common-layout invocation.** Idle 2 supplies a test before a bank returns to active use. It goes from level 0 to 4, so its required physical exchange has rank 28. All 222 copies have three disjoint eight-axis helper slots and a rank-four remainder. For a fixed replica and owner class, each slot visits that owner once by `hostClass_bijective`. In the unmodified borrowed worker every visit swaps the *same* pair of eight-axis fields and fixes the spectator (`BorrowedStep.helperRead`); its three swaps compose to one. Even granting the rank-four remainder an arbitrary choice of basis, these operations have combined displacement rank at most 12, leaving at least 16 for a physical correction at a fixed-layout handoff. Charging that difference once per role on this idle alone costs 16 × 222 × 32 × 5 = 568320 same-volume rank units. The paired remainder intervals and the per-register read identities do not remove this deficit. A class-based construction must change which physical axes the recursive invocation actually exchanges, or carry a changed layout through subsequent active operations and the final output. Checking a relabeling of the same common-layout worker at each visit cannot establish the fixed-layout handoff.

**Inherited interval order.** Every retained COPY source has dimension seven and frame zero has dimension zero. Consequently `phasePackSchedule 0 7` moves the second seven-atom field across one spectator, using seven adjacent swaps. Entry and return for nine windows in each of 1440 invocations total 181440 swaps. Charging even one rank unit per swap exceeds the node's 51360-unit slack. `scheduledIntervalCall_exec` uses the address equivalence from `scheduledPhaseCoordinates` in the opposite direction: when the child accepts those physical offsets, its transpose already acts on the two separated fields. A direct host call then costs the child budget plus two. The scheduled COPY worker and the nine-window sweep now use this direct call between the two basis passes. Their child position satisfies the explicit inherited-interval equation, and the local COPY bill is linear in the role volume. At a stopping child, `inheritedCopyLeaf_exec` builds the dimension headers and executes the physical transpose at the inherited offsets. Its tape cost is at most `1300*V + 1 + coreCost V child.width` before host embedding. The compact input for `phaseHeaderProgram 0 7` has six marked tapes: three copies of the atom width, one spectator suffix, and the constants one and seven. `loadCopyLeafHeaders_exec` constructs this bank from the two normalized binary source words and blank workspace, preserving both stacks outside the bank, at cost `18*length(bits w) + 6*length(bits W) + 26`. `inheritedCopyLeaf_exec` composes this loader with the leaf on one host, returns the transposed payload on its original tape, and preserves every off-bank stack. The call clears every private tape and leaves the payload in place. If the tape-machine budget is `C`, each private tape holds at most `length(bits w) + length(bits W) + 4 + 2*C` symbols on return, which bounds the cleanup independently of the payload length. The worker record supplies the spectator suffix on tape 27 and a unary predecessor clock on tape 33. `loadCopyLeafRecord_exec` converts that clock to the atom width, uses only blank shear scratch, and erases the temporary binary width after the header copy. This brings the full header preparation charge to `21*w + 20*length(bits w) + 6*length(bits W) + 40` for atom width `w`. `stoppedCopyChild_exec` discharges the scheduled child contract when the worker installs `stoppedCopyProgram`. This fixed program fits the existing row-swap workspace, shares record tape 24 with the leaf, restores all other record fields and returns the workspace blank. `stoppedBorrowedWindows_host` installs these procedures across all nine windows. For any fixed cutoff, the complete stopping sweep costs at most a uniform constant times the role volume and returns the checked fanout effect from a prepared seed. An internal child needs an inherited-order recursive supplier. MOVE still uses the packed layout.

**PR589 stage volume and borrowing.** At atom width `w`, put `M = q^w`. A compact owner word carries `B M^128 W` entries. The prepared stage charges its overhead on `B M^128 W N` entries, where `N = M^4096` counts all matrix labels. In `BitDescriptorRecurrence.stageVolume_eq_roleVolume`, that padded volume equals one parent role's volume when the parent has `142080 B N` rows and width `64 w`. The execution theorem's `singleLabelBank` places independent input only in one label row and fills the others with zero. Charging the other rows as borrowed stock therefore requires a semantic proof for the independent inputs occupying those rows. `BitBorrowedScatter.borrowedScatter_stage` now places all 661 registers in their scatter charts and routes them back after COPY. Every matrix label gets the literal framed scatter on its own arbitrary input. The bound includes both chart passes and the nine transpose calls. `borrowedInvocation_stage` composes this scatter with both scalar phases on the same flat owner tapes. The entire invocation acts separately at each label, with scalar, route and transpose costs included. `BitBorrowedNode.borrowedNode_parentCost` composes the nine borrowed-row sweeps with the idle remainder stages and charges the compiled node against the parent volume and the exact `nodeChildren5` occurrence list. Its price hypotheses refer to the actual phase, COPY and remainder workers. The recursive supplier must still realize those prices, and the complete node transform must be identified with interchange on the independent rows. The active port equations now persist through any consecutive remainder stages on other bank pairs. The sweep supplier accepts an arbitrary block count. The compiled node uses `M^112 * B` blocks and trailing length `K`, putting the 112 exterior digits before the inherited block in both sweep and idle order. `alignedSweep_read` proves equality of the physical read offsets for every active vector, exterior vector, inherited block, label and trailing cell. This removes the two layout transposes from the node bill. The earlier explicit conversion is available at `c1ebec1e`. For helpers, the packing program places the assigned eight-dimensional span in the active coordinates. Across a packed sweep, `borrowedRestored_inactive` identifies the restored role with its full family-span exchange at every label. `prepareBorrowedHeaders_exec` prepares the 127 adjacent-exchange headers from parent register words in linear volume time. On a shared bank, `BitBorrowedWindows.borrowedScatterSchedule_host` executes the entry chart, the nine scheduled COPY windows, and the exit chart. Its bound counts each child budget once and includes the two chart passes and local window work. The theorem assumes the child execution contracts, initialized private words, and chart state capacity at the scheduled dimensions. `alignedPhases_host` compiles both scalar phases at the same spectator width and charges each MOVE to its scheduled child. `borrowedInvocationBanks` places both phase programs and the charted scatter on one initialized owner bank and preserves the scalar stock across scatter. It derives the per-label invocation and the sum of the three prices from their local execution contracts. `scheduledBorrowedInvocation_host` instantiates those contracts with both compiled scalar phases and the nine-window charted scatter. The resulting bound charges the complete contiguous child list once, plus gate, MOVE, COPY and chart overhead. `scheduledInvocationFamily` instantiates the shared-archive sweep with all scheduled MOVE and COPY occurrences at the parent descriptor. Its recurrence bill uses the exact contiguous child range for the stage. The chart state capacity and packing coefficient are fixed before the parent dimensions. The stage still assumes both recursive child execution contracts and a prepared seed. Given the header for one role’s row count, `prepareRoleHeaders_exec` produces the packer's trailing dimensions and bounds header preparation by 152402000 times the scheduled stage volume. `prepareRoleRows_hoare` runs the fixed divider on the six full parent headers and returns the exact six role headers in time linear in the parent row count. `prepareRoleRows_exec` places the divider on 38 host tapes and preserves both stacks on every outside tape. Its six output ports satisfy the descriptor copier’s read condition. `loadRoleHeaders_exec` runs the divider and copies its six outputs into fresh archive source registers, with a charge for every copied bit. `parentRoleArchive_exec` composes the divider, copying, and archive construction on one host, with a single program independent of the parent dimensions. The role descriptor volume is exactly the scheduled stage volume when the parent width is 64 atom widths. It bounds each header word and the reduced row count, so the complete archive setup has a single fixed linear rate. `archivedBorrowedCall_host` executes packing and the invocation using the parent-built archive and returns its header words intact and its leaf scratch empty. `archivedSweep_exec` sequences all 160 calls and final restoration on this same archive, assuming each unwrapped worker realizes its invocation price and preserves the private inputs of other occurrences. It proves the restored stage equations and charges each worker once. `allocatedArchiveSweep_host` allocates a private bank for each seeded invocation and proves from disjointness that every later worker retains its inputs. It produces the restored stage on one archive. `parentPackedStage_exec` composes parent archive setup on 80 source tapes with the packed stage, charging construction once before the stage bill and preserving all private invocation inputs. `archiveChildCall_exec` constructs the worker controls from the archive, preserves the live payload and saved record, and executes the recursive procedure at cost at most 89 times the stage volume plus the child budget. The basis workspace has exactly two marked binary headers (atom width and spectator suffix). Installing the full basis and chart seeds across all occurrences and discharging the node endpoint and recursion remain.

## Completed integration gates for `2^-34`

| Gate | Progress | Evidence |
| --- | --- | --- |
| Exact margins and recurrence slack | ✅ | Layer margin `513/2^43` exceeds public target `512/2^43`; all other stage margins cover it. |
| Actual dimension arithmetic and precision | ✅ | Root64/input9, exponent9/64, lower cap7, upper power8, threshold64; gamma and modulus room proved. |
| Executable dimension and clean table stage | ✅ | Actual forty-variable stage, scratch cleanup, full PmF chain and charged wider prelude. |
| Actual fourth-root compact chunks | ✅ | Literal root2 overwrite, exact29+20K cost, distribution, source/recurrence matching and main assembly checked. |
| Wider distribution and machine costs | ✅ | All116 width/cost dependencies through CompactBdWiresCost checked; small-input bounds and actual allocated width proved. |
| Public theorem and audits | ✅ | All298 affected dependencies, complete 125034-declaration audit and focused 572-contract audit passed. |

The cycle-free dyadic stage core stays below ParamProg; independent arithmetic
witness modules do not introduce import cycles into actual sizing. The selected
state-of-the-art target remains open.

### Gaussian retained entries and entire-lattice tails

The actual rational cross-cell evaluator now joins the structured within-cell
coefficients with a uniform selected entry-error bound. The omitted signed
entire-lattice tails, including omitted aliases, sum to at most `2^(-46p)`
under the explicit band-width condition `16*p ≤ u*w²`. Three guarded source
checks and a combined26-declaration standard-axiom audit pass. This completes
coefficient and tail prerequisites, not the periodic rounded operator:
executable band choice, row-error assembly, sharp inverse bounds and charged
bulk execution remain. The public saving stays `2^-34`.

The stopped scanner now has a checked composed threshold-to-record pipeline:
it computes the floor-log cutoff, emits exactly the mapped stopped pieces and
actual exponent sum, then clears the cutoff with its full cost charged. Source
preservation and both contracts pass the standard-axiom audit. The next caller
bridge must derive the cutoff from actual global dimension and establish
rebased-leaf size, precision and layer-cost bounds; a supplied threshold is
not yet the global stopped-recursion implementation.

The omitted-tail width is now selected by ordinary executable natural division
and integer square root: `sqrt(16*p/u)+1`. Checked strict upper-square and
preceding-square bounds preserve the intended square-root scale, and the
selected full-tail estimate no longer takes a band-condition oracle. The
six-declaration standard-axiom audit passes; machine costs remain open.

### T16 actual binary tableau ranks

The source-faithful canonical binary tableau, including identity at rank zero
and the full C gate at rank nine, now has a proved inverse-Z subspace identity.
Kernel transport and rank-nullity give the actual relative X-block rank, with
no assumption that a selected frame has nondegenerate restricted dot product.
An explicit initial-column extension API connects these formulas to native
trace ranks; the1004 literal invertible extension witnesses remain to import.
Four guarded checks and104-declaration standard-axiom audit pass. Complex
Pauli realization, global phases, dirty routing and tape costs remain open.

The selected stopped-recursion cutoff now reads actual preserved global `D`:
`log_m(D) / 10^24 - 1`, matching the source assembler's selected beta rather
than its default beta. Subtracting one level pays the emitted digit factor.
The complete charged cutoff/scanner/cleanup pipeline proves every output leaf
has `leaf^(10^24) ≤ D` when `10^24 ≤ log_m(D)`. Below that threshold the
cutoff is explicitly zero, with no unsupported leaf bound. Both modules and
standard-axiom audits pass. Actual compact caller replacement, precision,
small-input handling and layer-cost absorption remain open.

### Selected PR589 frame-state bridge

The selected scalar word now has exact occurrence-indexed frame-state replay
and compiler phase/boundary identities, retaining all29250 phase incidences
and527 logical scatter incidences. The240-file frozen checkpoint passes guarded
checks and a1760-declaration standard-axiom audit. These identities apply to
a supplied frame interpretation; actual rational E8 operator interpretation,
compatibility with binary scalar values, distinct-frame COPY execution,
geometric ranks and hosted costs remain open.

The stopped replacement now reaches the actual original-parameter root
constructor through reservation arithmetic, active scanner and cleanup. The
constructor returns its fresh exponent sum; the actual configured width gives
piece precision from the existing geometric fit and activeD≤globalD, with no
new assumed stopped precision bound. Four guarded checks and seven principal
contract audits pass. The back reservation remains unchanged and is outside
the active-digit leaf bound. Top adapter/layer replacement, the separate back
leaf bound and asymptotic cost absorption remain to connect.

### Completed periodic rounded-row error

`PhaseCellRow` defines the actual finite corrected periodic row by wrapping
every retained integer offset into `ZMod s` and accumulating repeated residues.
Its exact target is the existing normalized operator `normN`, identified with
its entire lattice series. Symmetric lattice splitting accounts for both
omitted signed tails, including every alias. `PhaseCellRowBudget` bounds
retained rounding amplification and proves row error at most `2^(-45p)` for
vectors of sup norm at most one, using the selected executable square-root
band and existing gap/precision conditions. No dimension factor occurs.
Both guarded source checks and the22-declaration standard-axiom audit pass.
The remaining M7 work includes actual continuous-linear-map/inverse packaging,
sharp inverse norm, structured solve and boundary composition, bulk/core/halo
execution, prime supply and charged machine costs. Public saving remains
`2^-34`.

The1004 literal source-greedy extension matrices are now imported with checked
inverse/dual equations and retained initial columns. Native inverse-Z and
relative X-block rank theorems cover every original climb/center event in both
orientations without extension hypotheses. All35 new modules and the combined
5185-declaration standard-axiom audit pass; the38-file generated checkpoint is
deterministic. Complex Pauli realization, phases/tableau completeness, monomial
factors, adapters, dirty routing and hosted costs remain open.

The periodic corrected row is now packaged as an actual continuous linear map,
with operator norm error at most `2^(-45p)`. Inverse perturbation consumes this
proved estimate directly: any actual exact inverse bounded by `2^(16p)` yields
a two-sided rounded inverse bounded by `2^(16p+1)`, within `2^(-12p)` of the
exact inverse. The guarded check and14-declaration standard-axiom audit pass.
This closes the approximation-to-operator bridge; constructing the exact sharp
inverse and executing its structured solve remain separate obligations.

The PR589 source's nine physical COPY/ERASE buffer lifecycles now have an
explicit imported program through temporary661, retaining527 intervening
frame-zero ADD incidences and545 total records. Decoded scatter equivalence,
immutable copied sources and cleared temporary are proved for supplied
invertible frames and arbitrary dirty binary streams. All four modules and
101-declaration standard-axiom audit pass; source exporter order and six-file
manifest verified. Concrete rational E8 projection interpretation and actual
COPY/MOVE ranks remain open, so this does not yet certify primitive costs.

The complete stopped top constructor now reuses the unchanged original adapter
with its actual fresh exponent sum, config and working width; all full-frame
execution contracts and exact costs are checked. The source processes back
reservation separately (compact-control-layout.tex13–16,64–75), applying tiny
beta only to the active middle recurrence (79–107). Accordingly the unchanged
back leaf costs at most `512*B*V`, with actual floor-chunk bound
`B ≤ 2*g*d^(1-c)+1`, without a tiny-beta assumption. Five modules and their
principal standard-axiom audits pass. Hosting/layer replacement, the relation
between selected-axis cutoff and ambient dimension, and asymptotic active
cost absorption remain to connect.

### Completed small-gap Gaussian inverse mathematics

Pairing the nearest positive and negative offsets proves that only one can
attain the worst rounding error. Together with the entire-lattice tail, this
gives the actual normalized operator a row gap `1/(4p)` when `p≥2`,
`8p≤2^u`, `alpha²=u`, and `theta≥1/(4p)`. The exact two-sided inverse has
norm at most `4p`. The actual corrected periodic rounded matrix then has a
two-sided inverse of norm at most `8p`, differing from the exact inverse by at
most `32p²/2^(45p)` under the checked similarity/precision conditions.
The older restriction `alpha²*theta≥1` is absent. All three guarded checks and
the eight-declaration standard-axiom audit pass. These are actual operator
inverses; their fast Toeplitz/Schur/core/halo realization, boundary composition,
prime supply, normalization and charged machine costs remain open. The public
fixed-machine saving is still `2^-34`.

The stopped constructor is now hosted in the actual layer record path from
SynV. Fresh records, exponent sum, config and width follow the executed
constructor. Stopped and original lists have identical selected-address lists
after global rebase, preserving coverage and the shared padded-row divisor.
Configured precision discharges actual piece readiness and separate reservation
costs. The selected-axis cutoff satisfies the required ambient-dimension depth
bound, including small selected dimensions. Five modules and seven principal
standard-axiom audits pass. The selected list is explicitly nonempty here;
downstream refresh/prepare, the empty fallback and active recurrence absorption
remain to connect.

### Concrete PR589 rational frame operators

The frame interpretation now uses actual rational E8 root spans with dot/2
form, proving nondegeneracy by positivity. It acts by ShearFrame pullback on
F2-valued streams over rational address pairs; rational geometry is not
identified with binary coordinate geometry. COPY is the inverse projector
shear, with rank equal to the actual root-span dimension. Comparable MOVE
ranks are actual projector-difference ranks. All nine retained COPY ranks are
seven (total63); the first literal MOVE0→2 has rank one. The guarded module
checks and99-declaration standard-axiom audit pass; all511 earlier files remain
unchanged. Complete selected label dimensions/nesting, occurrence MOVE profile,
weighted moments and hosted machine costs remain open.

### Boundary elimination invariants

Literal real Schur elimination on arbitrary active vertex sets now preserves
the positive row-dominance margin and never increases absolute row mass.
Successive elimination has both invariants for any pivot list, with absent or
duplicate vertices skipped, and the one-step right-hand-side update is proved
from the original pivot equation. No symmetry or positive-definiteness is
assumed. Both guarded source checks and the17-declaration standard-axiom audit
pass. Connecting the actual rounded Gaussian matrix, boundary index geometry,
LU/Woodbury realization and tape costs remains open.

### T16 exact complex gate realization

Source-faithful C/P/D gates now have genuine complex operators and exact
phase-bearing Pauli conjugation, including inverses, literal diagonal
polynomial/alpha compatibility and finite-word composition. The global phase
is represented explicitly. Seven guarded module checks and a164-declaration
standard-axiom audit pass without warnings; the eight-file checkpoint leaves
all previous trace/geometry/tableau imports unchanged. Canonical-word/native
tableau identification, monomial residual equality, tableau-plus-zero-state
completeness, adapters, routing and tape costs remain open.

### Actual rounded-matrix boundary margin

The executable rational periodic matrix now accumulates every retained alias
and agrees exactly with the existing rounded operator's matrix-vector action.
Its entries are nonnegative and its diagonal is at least one. The selected
small-gap estimates imply an actual matrix row-dominance margin `1/(8p)`,
preserved by arbitrary successive interior elimination. Both guarded source
checks and the12-declaration standard-axiom audit pass. Boundary sparsity and
ordering, identification with the block Schur complement, fast structured
solve, normalization and tape costs remain open.

Stopped layer preparation/refresh and exact address selection now pass their
actual execution contracts. Positive ambient parameters and the existing
capacity implication justify the nonempty case; empty selection follows the
existing direct synChunk fallback, with no additional runtime selection test.
Three guarded source checks and the principal standard-axiom audit pass.
Packed-child geometry and runtime readiness remain unfinished after a
definitional-equality memory hotspot; those drafts are preserved separately
and excluded from committed sources. Full active recurrence/cost absorption
remains open.

### Complete selected PR589 label dimensions

All636 selected rational root-span label dimensions now have exact spanning
and dual certificates. Generic root-list subset witnesses give genuine
nesting, actual projector-difference MOVE rank and ordered-list conversion.
All44 Lean modules and the1981-declaration standard-axiom audit pass; the
46-file checkpoint reproduces its42 generated modules and preserves all517
earlier supplier files. Concrete nesting/rank certificates for29250 phase
incidences plus661 final-alignment incidences, weighted moments, hosting and
tape realization remain open. This checkpoint supplies complete label
dimensions, not the complete ordered MOVE profile.

### Exact boundary solve through elimination

Successive Schur elimination now carries its right-hand side: every full
solution restricts to a solution of the eliminated system, and eliminated
vertices are recovered from their pivot rows. A positive dominance margin
bounds and determines active solutions. On the actual rounded Gaussian
matrix, the reduced boundary system after any interior elimination has
exactly the restricted full solution, bounded by `8p` times its right-hand
side, with no positive-definiteness assumption. Both guarded checks and the
10-declaration standard-axiom audit pass. This is the exact algebra of the
source's two interior passes and one boundary solve. Boundary sparsity and
ordering, Gohberg–Semencul interior inverses, rounded structured solves and
tape costs remain open.

### Boundary sparsity after interior elimination

Schur fill-in through a pivot needs both of its links, so eliminating vertices
that couple only within their own cell creates only same-cell entries. The
actual rounded matrix is supported in the cyclic band of the selected width.
Interior vertices, whose band stays in the array and in one phase cell, couple
only within that cell; after eliminating any of them, every reduced coupling
is a band entry or joins one phase cell. This is the source's sparsity claim
for the Schur boundary, with wrap entries kept as band entries. Both guarded
checks and the10-declaration standard-axiom audit pass. Boundary count and
bandwidth in boundary order, Gohberg–Semencul interior inverses, rounded
structured solves and tape costs remain open.

### Gohberg–Semencul interior inverse identity

Any two-sided inverse of a symmetric Toeplitz matrix over a field is now
proved symmetric and persymmetric, and satisfies the Trench diagonal
recurrence. With its first column `x` and shifted reversed column `z`
(`z₀=0`), it equals `(L(x)L(x)ᵀ-L(z)L(z)ᵀ)/x₀` entrywise, the source's four
triangular Toeplitz products. Only `x₀≠0` is assumed. The guarded check and
24-declaration standard-axiom audit pass. Instantiating it on phase-cell
interior blocks, the `x₀>1/2` and column-norm bounds, rounded factors and
convolution costs remain open.

A dominant symmetric Toeplitz block with unit diagonal and off-diagonal row
mass `ρ<1` now has an actual two-sided inverse, inverse row sums at most
`1/(1-ρ)` and corner at least `1-ρ/(1-ρ)`; row mass is at most twice the
one-sided coefficient sum. For `ρ≤1/8` the corner is at least `6/7`
(the source needs `x₀>1/2`) and the Gohberg–Semencul factorization holds.
The guarded check and namespace standard-axiom audit pass. The actual
phase-cell kernel bound, rounded factors and convolution costs remain open.

The actual shared within-cell kernel now meets these conditions: executable
off-diagonal samples are at most `20^-δ` once `u≥1`, so every Toeplitz block
has row mass at most `1/8` (the source assumed `u≥4`). Each interior block
of any length has an actual inverse with corner at least `6/7` and the
Gohberg–Semencul factorization, and actual cell entries are exactly its
diagonal similarity. The guarded check and10-declaration standard-axiom audit
pass. Block composition of interior inverses with the boundary solve, rounded
factors and convolution costs remain open.

### Exact four-step interior/boundary solve

The source's two interior passes and one boundary solve are now exact for
any exact interior solver: interior solves are linear under dominance, any
boundary solution of the Schur operator glues to a full solution, and with
a margin on the whole index set it is the unique solution, bounded by
`max|b|/μ`. On the actual rounded Gaussian matrix, for any interior set, the
four steps reproduce the full solution with boundary values at most `8p`
times the right-hand side. Both guarded checks and the10-declaration
standard-axiom audit pass. Together with the Gohberg–Semencul blocks, this
completes the exact algebra of the fast inverse; rounded factors, error
propagation through the four steps and convolution/tape costs remain open.

### Rounded four-step error composition

The exact full solution satisfies the Schur boundary equation, and the Schur
operator is linear with inverse bound `1/μ`. Stage deviations `e₁…e₅` for the
interior pass, residual, boundary solve, recovery right-hand side and second
interior pass compose to boundary error `e₃+(Ke₁+e₂)/μ` and interior error
`e₅+(e₄+K·boundary)/μ`, with coupling row mass `K`. On the actual rounded
Gaussian matrix the off-diagonal row mass is at most one, giving
`e₃+8p(e₁+e₂)` and `e₅+8p(e₄+e₃+8p(e₁+e₂))`, with no factor in the number of
cells or the line length. Both guarded checks and the8-declaration
standard-axiom audit pass. This is the source's independent composition with
simpler constants; local stage bounds for rounded Gohberg–Semencul and
boundary elimination, and tape costs, remain open.

### Rounded Gohberg–Semencul application

Gohberg–Semencul is now an operator identity: `x₀ M v` equals
`L(x)L(x)ᵀv-L(z)L(z)ᵀv`, with truncated lower convolutions and upper
correlations whose row norms are bounded by the coefficient mass. With masses
at most two, `x₀≥1/2`, rounded factors and reciprocal within `η`, and each of
the five computed stages rounded within `η`, the computed application is
within `64Lη V` of the exact inverse for inputs bounded by `V≥1` when
`Lη≤1`. This is the unscaled local stage error `e₁`/`e₅`; the diagonal
similarity scaling, the concrete rounding of the actual factors and the
convolution costs remain open. Both guarded checks and the39-declaration
standard-axiom audit pass.

Every interior row of the actual rounded Gaussian matrix, whose band stays in
the array and in one phase cell, is now proved free of aliasing and exactly
equal to `a_i G(|l-i|)/a_l` for every column, with the shared Toeplitz
kernel `G` and zeros beyond the band. This connects the actual matrix to the
Gohberg–Semencul blocks. The guarded check and3-declaration standard-axiom
audit pass. Per-cell interior solves and similarity-scaled rounding remain.

Exact interior solvers now exist under any dominance margin, and on a
consecutive interval of interior vertices containing every active vertex of
its phase cell, every interior solution of the actual matrix equals the
similarity-scaled Gohberg–Semencul inverse of the shared Toeplitz kernel.
Both guarded checks and standard-axiom audits pass. Rounded similarity
scaling, the boundary elimination error and tape costs remain open.

The complete rounded block solve is now bounded: with weights in `(0,1]`,
rounded reciprocal weights and inputs, the five rounded Gohberg–Semencul
stages and rounded rescaling, a dominant Toeplitz block with `ρ≤1/8` is
solved within `η+64LηV+2(η+Cη)` of the exact scaled inverse, for inputs
bounded by `C` and scaled inputs by `V≥1`. With the actual cell solve this
supplies the interior stage errors `e₁`/`e₅` once actual weight bounds and
the factor rounding are instantiated. The guarded check and namespace
standard-axiom audit pass.

### Exact block-Schur identification

After eliminating all interior vertices in any order, the reduced matrix now
acts on boundary vectors exactly as the Schur operator
`A_BB-A_BI A_II⁻¹ A_IB`, and it inherits the full dominance margin. This
closes the block-Schur identification left open above and gives the boundary
system a concrete dominant matrix for its factorization. The guarded check and
4-declaration standard-axiom audit pass. The rounded boundary factorization
error and tape costs remain open.

### Boundary LU factors and residual bound

Elimination in list order now yields explicit factors `A=LU` on the active
set. Each pivot consumes `μ|A_ik|/A_kk` of every other row's mass, so
multiplier rows sum to at most `1+mass/μ` (at most `1+16p` for the actual
matrix, versus the source's looser `65p²`), and pivot rows keep the margin
and never exceed the original mass. Computed forward and back substitutions
with residuals `εf`, `εb` against the exact factors solve the system within
`(Λεb+εf)/μ`. No Woodbury correction is needed for this bound: cyclic wrap
entries are ordinary fill in the same factors. The guarded check and
5-declaration standard-axiom audit pass. Instantiating residuals for rounded
triangular solves, the boundary ordering and tape costs remain open.

Rounded triangular solves with rounded factors are now bounded: with factor
row-sum errors `εL`, `εU`, forward rows rounded within `η`, back-substitution
residual `δ` and smallness `c=(ΛεU+εL(M+εU))/μ≤1/2`, the computed solution is
within `2((Λδ+η+εLδ)/μ+cX)` of the exact one, with the growth of computed
values bootstrapped from the maximum error. This is the boundary stage error
`e₃` in terms of factor and online rounding. The guarded check and
2-declaration standard-axiom audit pass. Actual rounded Schur factors, the
boundary ordering and tape costs remain open.

Actual similarity weights lie in `[2^-(8p+1),1]`, and the rounded interior
solve of one actual phase-cell interval reproduces the exact interior solution
of the actual rounded Gaussian matrix within `η+64LηV+2(η+Cη)`. This supplies
the actual stage errors `e₁`/`e₅` per cell. Both guarded checks and the
2-declaration standard-axiom audit pass.

Interior vertices of each phase cell are now proved convex in physical order:
every interior vertex lies in a consecutive in-array interval containing all
interior vertices of its cell, discharging the interval hypotheses of the
exact and rounded cell solves for the choice `I` = all interior vertices. The
guarded check and2-declaration standard-axiom audit pass.

The actual boundary stage error `e₃` is now bounded: the boundary Schur matrix
of the actual rounded Gaussian matrix keeps margin `1/(8p)` and row mass at
most two, its multipliers sum to at most `1+16p`, and rounded factors with
rounded triangular solves are within
`2(((1+16p)δ+η+εLδ)8p+c·64p²ρ)` of the exact Schur solution, under the
smallness `c=((1+16p)εU+εL(2+εU))8p≤1/2`. Together with the per-cell interior
bounds, every stage error of the rounded four-step solve is now proved on the
actual matrix in terms of local rounding contracts. Guarded check and
2-declaration standard-axiom audit pass. The concrete computation meeting
those contracts and its tape cost remain open.

### Small-gap factorization for the pipeline interface

The pipeline's source-error theorem needs contraction factors, but in the
small-gap regime the exact inverse of `N` has norm up to `4p`. The
permutation-left factorization is now proved there without `α²θ≥1`:
`P_s F_s = 2^(2⌈α²⌉+2+j) B₀' P_t F_t A` with `B₀'=B₀/2^j` a contraction when
`2p≤2^j`, matching the source's extra normalization. It plugs into the
already generic `sourceApprox_err` with `γ=d(2⌈α²⌉+2+j)`. The guarded check
and standard-axiom audit pass. The new line maps (chirp forward, phase-cell
inverse) on tapes, their costs and the `ε=5/8` sizing remain open.

The pipeline's `B̃₀` interface is now generic in the computed inverse: any J̃
that keeps the unit disk and is within `εJ` of `J(v/2)` yields `hB'`/`hB'1`
with error `6+εJ`, and `B₀(J/2^j)=B₀(J)/2^j`. A phase-cell solve of `N` scaled
by `2^-j` therefore enters the existing source-error theorem unchanged. The
guarded check and3-declaration standard-axiom audit pass.

A small-gap computed inverse within `e` of `L(v/2)/2^j`, where `L` inverts
the rounded operator within `δ₀` of the exact inverse (`‖J‖≤4p`, `4p≤2^j`),
now gives the pipeline `B̃₀` interface for the normalized factorization target
`B₀(J)/2^j` with error `6+2^p(e+δ₀/2)`. With the four-step error bounds this
reduces the new inverse line map to its concrete rounded computation. The
guarded check and2-declaration standard-axiom audit pass.

### Narrower route to `2^-33` (cost estimate, not yet checked)

Corrected estimate. Keep the existing direct-window `Ã` machine and the
existing source/axis sizes, and replace only the Neumann inverse in `B̃₀`.
Choose a small `α² = u = ⌈log₂(8p)⌉`. The current sizes give
`1/(4d) < θ ≤ 1/(2d)` with `d` the dimension, so the small-gap hypotheses hold
with cell parameter `d`: `θ ≥ 1/(4p)`, `dθ ≥ 1/4`, `u d ≤ p`, `8p ≤ 2^u`. The
rounded matrix `H` is circular-banded with half bandwidth
`w = ⌊√(16p/u)⌋+1` and margin `1/(8p)`. Phase cells are not needed for
`ε<1/2`: factor `H` once per axis by rounded elimination (backward stable,
`SchurLUBackward`), store the factors, and solve each line by forward and back
substitution. Fill stays in the band plus a `w`-wide cyclic border, so a line
costs `O(s w)` operations, `O(√(p/u))` per element, the same order as the
`Ã` window `α√p`. Setup is `O(s w²)` per axis, negligible against the `T/t`
lines per axis. Both maps then cost about `p^(1/2) M(p)` per element, giving
Gaussian margin about `1/2-δ-ε`; the layer margin `ε(1-λ')` covers `2^-33`
for `ε≥0.28`, e.g. `ε=5/16` (margin `5/32`). `2^-32` needs `ε≥0.56` and so a
faster forward map. To check: the cyclic fill pattern and substitution cost,
working precision about `p+2log₂s`, the `ε=5/16` sizing lemmas that assume
`ε≤1/7`, and the new `B̃₀` and retuned `Ã` machines and costs.

The boundary solve now also has a backward-error form: computed factors with
unit-diagonal multipliers whose product equals the Schur matrix up to row
mass `εS` give error `2((Λδ+η)/μ+(εS/μ)X)` when `εS/μ≤1/2`. An on-tape
rounded elimination therefore only needs a backward bound on its factors,
avoiding exact rational setup of the Schur complement. The guarded check and
3-declaration standard-axiom audit pass.

Rounded elimination is now proved backward stable for dominant matrices: with
every multiplier and update rounded within `η`, each stage keeps dominance up
to explicit losses, the computed factors reproduce every entry within
`len·η(1+M)`, and multipliers stay bounded. Followed by rounded triangular
solves, the computed boundary solution is within
`2((Λδ+η)/μ+(εS/μ)X)` with `Λ=1+len(2M/μ+η)`, `εS=n·len·η(1+M)`. The boundary
solve is therefore fully specified by fixed-point operations, with no exact
rational setup; with `η=2^-P` the polynomial factors in the line length are
negligible. The guarded check and5-declaration standard-axiom audit pass.

`Mult/SmallGapSizes` checks the route's sizing claim at the current sizes:
with `u=⌈log₂(8p)⌉` and the dimension as cell parameter, every axis satisfies
`8p≤2^u`, `1/(4p)≤θ_i`, `1/4≤dθ_i` and `u d≤p`. The guarded check and
4-declaration standard-axiom audit pass. These hold at `ε=9/64`; the `ε=5/16`
sizing must re-establish them.

`Mult/BandedB0` closes the numeric side of the inverse-only route: real solves
of the rounded matrix (for example by the backward-stable banded elimination)
within `e`, applied to real and imaginary parts and normalized within `η`,
give the pipeline `B̃₀` interface for the small-gap factorization target with
error `6+2^p((2e+η)+δ₀/2)`. The guarded check and3-declaration standard-axiom
audit pass. Remaining for this route: cyclic fill and substitution cost,
`ε=5/16` sizing, the new `B̃₀` machine with per-axis stored factors, the
retuned `Ã` costs and the final assembly.

The cyclic fill pattern of the route is checked: eliminating the actual
rounded matrix in physical order keeps every factor entry within the band or
the `w`-wide cyclic border, so every non-border factor row has at most `3w+1`
entries and a line solve with stored factors touches `O(sw)` entries. Both
guarded checks and the5-declaration standard-axiom audit pass.

The banded solve is now a concrete function: `SchurSubst.bandSolve` performs
rounded elimination and rounded forward/back substitution (quotients by the
pivot rounded once) in elimination order, and `bandSolve_error` bounds its
error end to end for any dominant system. Rounded factors are triangular in
that order and stay inside the exact fill (`fill_support_r`). This is the
numeric specification the new `B̃₀` tape machine must implement. The guarded
check and5-declaration standard-axiom audit pass.

On the actual rounded Gaussian matrix in physical order, the concrete band
solve is within `2700s²p²η` of the exact solution whenever `128ps²η≤1`
(`PhaseCellBandSolve`). With `η=2^-P` and `P≥p+2log₂s+O(log p)` this meets
the `B̃₀` interface error `p²`. The guarded check and3-declaration
standard-axiom audit pass.

The new `B̃₀` line map is now fully concrete (`Mult/ConcreteB0`): `bandJt`
computes the inverse by two rounded band solves of the rounded matrix (real
and imaginary parts of `v/2`), scales by `2^-j` and rounds to the `p`-grid.
Under `128ps²η≤1` and an explicit smallness condition it satisfies the
pipeline `B̃₀` interface for the normalized factorization target, for the
exact inverse of `N`. The guarded check and2-declaration standard-axiom audit
pass. Its tape machine and cost, the per-axis factor setup, the `ε=5/16`
sizing and the final assembly remain.

At the existing sizes the concrete `B̃₀` meets all its precision conditions
with working precision `3p` and `j=⌈log₂(4p)⌉`, with interface error at most
`p²` (`Mult/ConcreteB0Sizes`). The guarded check and4-declaration
standard-axiom audit pass.

The tape library has no record division, so the line machine must multiply
by stored pivot reciprocals and rounds each product separately. The numeric
specification now matches that: `bandSolveM` rounds every product with exact
sums and uses stored rounded reciprocals, with residuals `nη` and
`(n+M+2θM)η+2θMB`, and `bandSolveM_error` bounds it through the
size-dependent backward theorem `backward_lu_k`. Factors and reciprocals are
computed per axis in the table VM, which has exact division. Both guarded
checks and the standard-axiom audits pass.

Machine design simplification: eliminating in folded order `0, s-1, 1, s-2, …`
turns the cyclic band into an ordinary band of half width `2w+1`, so the
rounded factors have no border fill (`PhaseCellFold`) and the machine-faithful
solve keeps its error bound in that order (`bandSolveM_fold`). The line
machine is therefore: fold the line, one uniform banded forward pass and one
backward pass with stored factors and reciprocals (column-oriented, equal to
the row-oriented specification by `colFwd_eq`/`colBwd_eq`), unfold. The target
map is `Mult/ConcreteB0.bandJtF`. Guarded checks and standard-axiom audits
pass.

Tape machine progress for the banded `B̃₀` line (`Fast/BandLine`): the forward
and backward passes are proved on the `RsbR` registers. Each pass is `s`
column steps (pop the final head, one truncated stream product of `B` stored
column entries, `B` pending updates), with the backward step preceded by a
product with the stored pivot reciprocal; the passes leave exactly the
step-indexed lists of `Mult.BandList`, which reproduce `fwdZC`/`bwdZC` and so the
concrete `bandJtF` map. Remaining for the line: fold/unfold and scaling of the
line records, dropping the `B` dummies, the per-axis factor tables from the
table VM, axis/box wrappers, and costs.

Loader redesign: the table VM has a fixed set of scalar variables and no
arrays, so it cannot hold the band for elimination, and records have no
divider. The per-axis factorization will therefore run on record tapes with
pivot reciprocals by rounded Newton iteration (`NLogN/NewtonRecip`:
quadratic convergence under perturbation, `|r_K-1/b|≤60η/β²` after
O(log(pP)) steps). Rounded elimination is now generic in the multiplier rule
(`SchurLUBackward`), and `recipMul` (Newton reciprocal times entry) satisfies
it with error `η(1+60M/β²)`. Matrix entries can come from the existing `E`
weight table code at working precision. Guarded checks and standard-axiom
audits pass.

The numeric spec now matches the factorization machine. Rounded elimination
rounds the product and subtracts exactly (`relim`), as fixed-point records do.
`bandSolveG` takes any multiplier rule and any pivot reciprocal rule
(`bandSolveG_error`), and `bandSolveN_fold` instantiates both with Newton
reciprocals (`recipMul`, `recipNewton`): on the phase-cell matrix in folded
order the error is at most `62000 p³ s² η(1+180/β²)` for a Newton floor
`β ≤ 1/(16p)`. Guarded checks and standard-axiom audits pass.

The tape machine may use unguarded Newton rules: `bandSolveG_congr`
(`SchurCongr`) shows two rules agreeing on entries of size at most `M` and
pivots in `[μ/2, M]` give the same solve, so `bandSolveMach_fold` bounds the
machine rules (`machMul`, raw `newtonR`) by the same `62000 p³ s² η(1+180/β²)`.
`SchurStages` reads the factors of the natural order off the stage matrices
(`lur_range`) and relabels factors by an injection (`lur_map`, for the folded
order). `SchurWindow` is the real-valued sliding-window factorization: a window
of `B+1` rows on `2B+1` columns, one step per pivot, and `factorRows_run` shows
the run emits each stage's eliminated column and pivot row.

`Mult/BandFactor` runs the window factorization on integer numerators
(`newtonZ`, `mulZ`, `factorRowsZ`) and maps it onto the real run
(`factorRowsZ_map`). `FastB0.concrete_resampB₀_specX` gives the pipeline
interface for any line solver within `e`, and `concrete_resampB₀_specN` for the
machine solver `machSolve`. At working precision `4p`, Newton floor
`β = 1/(16p)` and `newtonK p = 2(log₂p+1)+9` iterations, `Big.newton_conditions`
and `Big.concreteB0N_conditions` discharge every precondition with final error
at most `p²`. Remaining for the swap: the backward-pass column table from the
pivot rows (a per-axis transpose), the factorization and transpose machines on
tapes, the line wrapper, and pipeline and cost integration.

`Mult/BandSolveList` closes the list level of the line solve. For a banded
grid matrix `AZ` (zero outside `s × s`), `lineSolveZ` runs the integer window
factorization, the forward pass on the padded multiplier columns, and the
backward pass on the transposed pivot rows (`ucolZ`) with Newton reciprocals;
`lineSolveZ_eq` shows its grid values are the machine-rule `bandSolveG` of the
natural order. `bandSolveG_map` (`SchurStages`) relabels a solve along an
injection, which carries the folded order to natural positions. Open: the
matrix the machine factors is a grid rounding of the phase-cell matrix, so the
error analysis needs a perturbation step from `realMatrix` to its rounding.

Superseding the `specN` route above: the machine factors a grid rounding `Ã`
of the phase-cell matrix. `NLogN/PhaseCellPerturb` shows a row-sum perturbation
`ε ≤ 1/(32p)` keeps margin `1/(16p)` and mass `9/4`, and the machine solve of
`Ã` is within `62000(2p)³s²η' + 64p²ε` of the phase-cell solution
(`bandSolveMach_perturb`). `concrete_resampB₀_specP` gives the pipeline
interface, and `Big.concreteB0P_conditions` discharges it at precision `5p`,
`β = 1/(32p)`, `newtonK p = 2(log₂p+1)+11` and `ε ≤ 2^-3p`, error at most `p²`.

The matrix the machine builds is the wrapped window of Gaussian coefficients
`exp(normExp j k)`, `|k| ≤ w = width p u` (about `4√(p/u)`), each within `δ`
(`NLogN/PhaseCellMachMatrix`, `windowMatrix`). Its rows are within
`(2w+1)δ + 2^-46p + 2^-45p` of the phase-cell rows in absolute sum
(`windowMatrix_close`, through the exact window, `N`, and `‖rounded - exact‖`).
`concrete_resampB₀_specW` gives the pipeline interface for its machine solve,
and `window_eps_le` makes the perturbation at most `2^-3p` for entries at
precision `5p` (the `tableE` routine at precision `5p` gives `δ = 2/2^(5p)`).

`Mult/BandSolveFold` closes the list-level spec in folded positions: the
numerator window matrix `wmZ` of coefficient numerators `aZ`, stored at folded
positions as `foldZ` (banded with half width `2w+1`, `foldZ_band`), run through
`lineSolveZ`, gives at folded position `i` exactly `machSolveT` at vertex
`foldAt i` (`lineSolveFold_eq`). What remains for the swap is mechanical tape
work: a table program emitting the folded rows of `foldZ` at precision `5p`,
the window factorization and transpose machines, the line wrapper around the
existing forward/backward line machine, and pipeline and cost integration.

Tape machines for the per-axis factor data are in `Fast/BandFactor`: Newton
reciprocals (`band_newton_runs`), the window step and loop
(`band_facStep_runs`, `band_facLoop_runs`, state `facState` iterating
`stepRowsZ`), the pivot-row transpose (`Mult/BandTranspose`, `tRun_eq`;
`band_tLoop_runs`), and block reversal (`band_rev_runs`). Next: the per-axis
driver that sets the counters and constants, runs the factorization, reverses
the multipliers into the forward table and the pivot rows into transpose order,
and runs the transpose; then the per-line driver around the existing banded line
passes, and the table program for the folded rows.

All per-axis pieces of the banded `B̃₀` are now proven machines: the folded row
stream of the table VM at precision `P` (`Fast/TableFold`, `tblFoldStream_host`,
rows `foldRowZ` = initial window then factorization inputs), the window
factorization (`band_facLoop_runs`) with its record widths discharged
(`facFits_all`), block reversal (`band_rev_runs`), and the transpose
(`band_tLoop_runs`). The remaining integration, in order:
1. A per-axis driver: table stream onto `src`, split off the initial window,
   factor, reverse the multipliers into the forward table, reverse the pivot rows
   into transpose order, zero window, transpose; counters differ between the
   phases (`m2n`, `mwn` are `2B`, `2Bw` while factoring and `B`, `Bw` in the line
   passes), so the driver copies them from spare registers between phases.
2. A per-line driver around `bandFwdLoopP`/`bandBwdLoopP` (BandLine): fold and
   scale the input, copy the stored tables onto `ef`/`tb`, the two passes, unfold,
   scale and round; its list spec is `lineSolveFold_eq` composed with `bandJtX`.
3. Record-width conditions of the line passes from the solution bounds.
4. Generalize `rsbAxisP`/`RsbAxisCfg`/`RsbAxisData` (currently hard-wired to the
   Neumann line) or add the banded variant, the loader for the band counters and
   constants, the cost bounds, the `ε`/`α` retune and the final theorem.

The banded `B̃₀` now replaces the Neumann inverse in the proved multiplier.
`Fast/BandStage.bandStage_exec` runs the loader and the banded lines along
every axis and computes `tensorZR (bandA n)`; `Fast/BandFits` proves the
record widths from the backward-stability bounds (`NLogN/SchurSizes`);
`Mult/BandSpec` discharges the per-axis numeric facts from `Big n`,
`8p ≤ 2^(α²)` and `α² d ≤ p`. The band line approximates `2^-α² ℬ₀`, so
the source exponent becomes `γ = d (3α² + 2)` (`Mult/SourceErrScaled`), and
`Mult/Pipeline.pipeline_correct` holds with `lineB = bandA`. The tape source
phase runs the band stage with records on `prm` and widths `dsW ≈ 10p`,
`dsWW ≈ 70p`; `Cost/MatchBandB.mt_band_stage_le_linear` bounds the stage by
`O(totResamp + totDirectCRT + T p)`. `MathlibTM2.Theorem` builds and the
statement uses only standard axioms. The public bound is unchanged at
`2^-34`: remaining are the small-`α` retune at `ε = 5/16`, the matching
sizing lemmas and the final theorem.

Next blocker for `2^-33`: the margin `ε(1-λ')` needs `ε ≥ 16/57`, but the
synthetic layers bound their precision shift by `(G+m)·D^6` and use `d^6 ≤ b`
and `d^7 ≤ b` (`Cost/MatchSynOver.mrO_synE_le`,
`CompactCallerWorkingWidth`), which needs `ε < 1/6`. The shift is the piece
exponent `E_{j+1} = G + F E_j` (`Node/Params.expSeq`), so it grows like
`F^j ≤ D^{log_m F} ≈ D^4.28` with `F ≈ 9.2·10^17`, `m = 15625`. At `ε = 1/6`,
`ε(1-λ') = 608/2^43` is still below `2^-33`. Reaching `2^-33` therefore also
needs bounded precision in the synthetic layers, for example rounding the
pieces between levels, so that the working width stays `O(p)` at
`ε ≈ 9/32`. The other `d^k ≤ b` uses (`Fast/ParamMath`, `Mult/Sizes`) are
sizing conveniences.

The Gaussian width is retuned: `α` is now the least integer with
`u² ≤ α⁴`, `u = ⌈log₂ p⌉ + 3`, so `u ≤ α² < 4u ≤ 4d` (`Mult/Sizes`,
computed on tape by `ParamSub.pmAlphaC`). The source factorization uses
`NLogN.smallgap_factorization` (`θ ≥ 1/(4p)`, `8p ≤ 2^(α²)`) through
`BandSpec.band_factorization_sg`, so the old `α²θ ≥ 1` condition is gone.
Both resampling maps now cost about `√(p log p) M(p)` per element, and the
Gaussian stage no longer limits `ε` below `1/2`. `MathlibTM2.Theorem` builds;
the public bound is unchanged until `ε` rises, which waits on the
synthetic-layer precision above.

Rounded synthetic layers (complete, `2^-33`). The layer machine keeps one common scale by
multiplying the wires a factor does not touch by `2^Tc` (`Layer/NodeZ.execM`),
so the exponent compounds, `E_{j+1} = G + F E_j`. Instead the factor shifts
its child's output right by `Tc` (truncating) and leaves the other wires
alone; gates still double. The node exponent is then `G` at every level, and
the truncation errors grow by a fixed factor per level, about
`√N (FΛ)^j` units for an array of `N` entries, which is `logT/2 + O(log d)`
guard bits, so the working width stays `O(p)` for any `ε < 1/2`. Steps:
rounded node and layer semantics with that error bound (`Layer/`); the factor
programs with a truncating shift in place of `shiftTc` (`Node/Factor`,
`Node/CompactFactor`) and their costs; the round error absorbed by
`SynthErrRounds` and the widths `synW2`; then `ε = 9/32` with its sizing and
the final theorem.

This is done. Each level truncates by its own scale (`Layer/LayerR`), the
error bound is sharp through spectator invariance (`Layer/NodeRSharp`), and the
top shrinks before its final division so outputs stay in the unit disk
(`Layer/TopRS`). The computed rounds are within `√2(1+1/16)/2^p` of the exact
rounds (`Mult/SynthErrRoundsQ`), the pipeline is generic in the box
convolution (`Pipeline.pipeline_correctG`, `Mult/PipelineQ`), and the main
chain runs on the rounded box stage up to `Fast/CompactFinalR`. Only `d² ≤ b`
is needed by the rounded costs; direct rounds stay exact with width `O(p)`.
The resampling margin uses `α ≤ 2√d`, so the stage margins hold at
`epsilon=9/32`, `kappa=2^-33`, binding on the layer margin `513/2^42`.
`MathlibTM2.Theorem` now proves `MulInTime (2^33)⁻¹` with the standard axioms.
The exact chain that needed `d^6 ≤ b` was removed (restore from the parent of
`8fb31454`).

**Retune to `epsilon=79/256`: `kappa = 36261/2^48`.** The only size relation
that capped `epsilon` below the resampling limit `5/16` was `d^7 ≤ b²`
(`epsilon ≤ 2/7`), used for the moduli room through `d^5 ≤ 4ℓ²`.
`Sizes.Big.moduli_room` now follows from `d² ≤ 2ℓ` alone, via
`16 d² N ≤ (4d)^(2d+2)` and `(4d)^8 ≤ 2^d` for `d ≥ 128`. The dimension is
`d = iroot 256 (b^79)`. The parameter machine forms `b^79 = ((((b^9)²b)²b)²b)` in
eleven atoms and takes the root with the existing capped-squaring search at
`k = 8`. Its word fit `(b^79+1)² < 2^(4b+32)` holds for `b ≥ 512`, so `pm_s3`
takes `Big n`. `pm_N_le` handles `d ≤ 3` directly. The layer gap is
`1-lambda' = 459/2^40`, just inside `1-Parameters.lam`. Stage margins: layout
`79/1024 · a_b`, layer `36261/2^48` (binding and public), direct rounds
`237/1024`, CRT `(177/256) a_b`, resampling `3/512`. Further retuning is
capped at about `1.12 · 2^-33` (`epsilon < 5/16`, `1-lambda' < 1-sigma`).
The next dyadic step still needs the M7 Gaussian route.

**Retune to `epsilon=7/16`: `kappa = 3213/2^44 ≈ 2^-32.35`.** The resampling
margin `1/2-delta-3epsilon/2` came from the coarse bound `α ≤ 2√d`; the actual
band width is logarithmic, `α² < 4(⌈log₂ p⌉+3)`, so `Cost/Growth.gr_alpha_le_K`
gives `α ≤ 4 b^{ε c/2}` (`c = 2^-32`) from `⌈log₂ p⌉ ≤ K`, and the margin is
`1/2-delta-epsilon(1+2^-33)`. The dimension is `d = iroot 16 (b^7)`; the
parameter machine forms `b^7` in five atoms and takes the root at `k = 4`, with
word fit `(b^7+1)² < 2^(4b+32)` for every `b`. `Big n` now asks `d ≥ 2^40`, and
`Sizes.mul_sq_le_b` (`F d² ≤ b` for `F⁴ ≤ d`) replaces the cube cap in the
moduli room (`6 E d² ≤ b` with `4d ≤ 2^E`), `2d ≤ ℓ`, `16 d α² ≤ b` and the
eventual `C K ≤ ℓ`; `d ≤ 2ℓ` and `d⁹ ≤ 128 ℓ⁷` hold for all `n ≥ 2`. Stage
margins: layout `7/64 · a_b`, layer `3213/2^44` (binding and public), direct
rounds `21/64`, CRT `9/16 · a_b`, resampling `1/32 - 7/2^37`.

**Retune to `epsilon=31/64`, `delta=2^-7`: `kappa = 14229/2^46 ≈ 2^-32.20`.**
`Cost/CompactLogGrowth` now bounds `⌊log₂ m⌋+1 ≤ 512 m^{1/256}`, so one
Schönhage–Strassen product costs `262144 m^{1+2^-7}` and `M(p) = p^{1+2^-7}`.
The dimension is `d = iroot 64 (b^31)`: nine power atoms and the root at `k = 6`,
with word fit `(b^31+1)² < 2^(4b+32)` from `b ≥ 512`. `Big n` asks `d ≥ 2^192`;
`mul_sq_le_b` takes `F^16 ≤ d`, the moduli room uses `(6(x+3))^16 ≤ 2^x` for
`x ≥ 192`, and `d^33 ≤ (2ℓ)^31`, `d ≤ 2ℓ`, `d ≤ 2^(ℓ-1)` hold for all `n ≥ 2`
(the last excludes `d = 3, ℓ = 2` and `d = 5, ℓ = 3` by `2^(b+1) < bT`).
Stage margins: layout `31/256 · a_b`, layer `14229/2^46` (binding), direct
rounds `93/256`, CRT `33/64 · a_b`, resampling `1/128 - 31/2^39`.

Further retuning is capped at `459/2^41 ≈ 2^-32.16`: the resampling margin needs
`epsilon < 1/2 - delta`, and independently the moduli `N = oddProd d` need
`d² log d ≲ b`, i.e. `epsilon < 1/2`. `2^-32` needs `epsilon > 0.557`. Above
`1/2` the construction needs `d ≫ log t` pairwise coprime moduli in windows of
relative width `1/(4d)` below `t = 2^ℓ`; all elementary constructions
(`oddProd`, `1 + iM` with `M = d!`, primorial shifts) need span `e^{Θ(d log d)}`
and fail, so this needs primes in short intervals (the selected construction
cites Baker–Harman–Pintz; PNT with a `(log x)^{-A}` error, `A > 2`, suffices
for `d = (log t)^{5/3}`). Mathlib currently provides Chebyshev bounds and
Bertrand only. With that prime supply, `2^-32` also needs the chirped-correlation
forward map (`notes/fast-gaussian-resampling.tex` at the selected revision,
`O(M(p))` per element, replacing the `α√p` window) and the banded `B̃₀` at
`α² ≈ p^r` with `r < 1-ε`; its margin `(1+r)/2-epsilon-delta` stays positive for
`epsilon < 2/3`, so the phase-cell inverse is not needed for this step.

## Milestone detail

Moved from `PLAN.md` on 2026-10-18, when `PLAN.md` became a one-screen dashboard. These records
describe the state at `25222/2^46`, before the merge of PR 4 (seven-eighths chunks) and PR 5
(prime moduli, balanced prefix, DFT corollary, PR589 bit-side work). Current status is in
`PLAN.md`; the per-milestone designs since then are `IntegerMultBounds/MathlibTM2/Balanced/DESIGN.md`
(M5), `IntegerMultBounds/MathlibTM2/M6/DESIGN.md` (M6), `IntegerMultBounds/MathlibTM2/NearOne/DESIGN.md`
(M7 and near-one dimensions) and `IntegerMultBounds/Primes/DESIGN.md` (prime moduli).

#### Milestone table at `25222/2^46`

| ID | Progress | Original sections | Concrete deliverable | Bound effect / remaining work |
| --- | --- | --- | --- | --- |
| **M1** | ✅ | **§§5, 6, 9** | **Set `epsilon=2^-30`, `c=2^-34`; reprove dependent sizing, executable parameter generation, cost and machine lemmas.** | **Complete, historical.** Public saving `kappa=2^-93`; exact internal margin `296/(10^11 * 2^64)` lies between `2^-93` and `2^-92`. Internal margin improved by `2^67`; public saving improves the former exact bound by more than `2^66`. |
| M2 | ✅ | §§4.3, 8.2, 9.3 | Replace adjacent CRT walks by direct nonadjacent swaps; preserve exact semantics and price setup, controls, movement and cleanup. | **Complete.** The running multiplier uses linear CRT routing and sharp linear resampling costs. Final parameters `epsilon=2^-5`, `c=2^-32`, `lambda'=1-1/10^11` give exact margin `296/(10^11 * 2^37)` and public saving `2^-66`; theorem and focused audit pass. |
| M3 | 🟡 | §5.2–5.3, Appendix A | Compact dirty controls, actual caller integration, stopped recursion and local repair costs. | **Compact integration complete:** actual fourth-root transforms, main input/distribution, full arithmetic chain, output, cleanup and finite-machine dispatch prove public saving `2^-33`, with rounded synthetic layers (one scale per level, truncation errors absorbed by the rounds) at `epsilon=9/32`. **Remaining:** stopped top/layer integration and cost absorption; actual global cutoff, reservation/root construction and configured precision are checked. |
| M4 | ⬜ | §5.4, §9.7 | Linear completed-child precision bound and explicit recursive workspace/stock contracts. | Planned. Remove conservative guard-growth restrictions and prove the reserve coefficients required at selected cutoffs. |
| M5 | ⬜ | §6.2, §4 | Balanced prefix and arbitrary-source coordinate routing in both transform directions. | Planned. Replace layout saving `epsilon c a_b` by direct movement saving `a_b`; restore spectators and frequency order. |
| M6 | 🟡 | §3.1–3.6, §§4–5 interfaces | Prove both selected finite suppliers, their variable-rank moments and the 144-call owner schedule. | The complete selected PR589 scalar word and finite-register dirty endpoint are checked, including source/helper restoration. Exact PR589 frame-state/compiler boundaries, concrete rational frame/COPY interpretation and all636 label dimensions, plus T16 charge profile, owner-row bounds, label traces, finite geometry and source-faithful binary tableau ranks for every native event with all1004 literal extension matrices are checked. Exact selected moment bills (T16 at `7/4178` tied to the checked schedule; PR589 at `10/5769`, schedule histogram checked, physical cost open) and the layer moment interface are checked. The T16 node is lowered to the layer machine and runs in the completed proof; the PR589 bit supplier and a variable-child layer recurrence remain. Target primitive endpoints about `0.00173343` (bit) and `0.00167546` (complex); component bounds alone do not update the final bound. |
| M7 | 🟡 | §8.1–8.3, §9.2/9.7 | Prove faster rounded Gaussian inverse and bulk core/halo tape execution, including prime supply and exact recovery interfaces. | Actual executable coefficients, square-root band, periodic operator error≤`2^(-45p)` and small-gap exact/rounded inverse bounds `4p`/`8p` are checked and audited, including all aliases. Also checked: the actual rational periodic matrix with elimination margin `1/(8p)`; exact, `8p`-conditioned boundary solves with band-or-same-cell sparsity and block-Schur identification; Gohberg–Semencul inverses of actual interior Toeplitz blocks with rounded scaled block-solve errors; and the exact four-step interior/boundary solve with rounded-error composition. Rounded boundary factorization, boundary ordering, tape costs and bulk execution remain; these must remove the Gaussian restriction and support near-one dimensions. |
| M8 | ⬜ | §9.1–9.8 | Prove bootstrap base/stages, link all 47 inequalities to actual stages and close the audited fixed-machine theorem. | Planned. Goal: exact unconditional saving `0.001672660197076918`. |

#### Section bottlenecks at `25222/2^46`

| Manuscript section | Progress | What limits our bound | Improvement needed |
| --- | --- | --- | --- |
| §2 Machine model and streams | 🟡 | Every new algorithm needs actual finite-machine costs and clean returned state. | Reuse Mathlib FinTM2 and existing host primitives; price new schedules. |
| §3 Finite networks | 🟡 | Current bit/complex primitive savings are `2.96e-9` and, with the T16 node on the layer machine, `10^-3` (`log_73 (F/NW) < 999/1000`). | Selected PR589 bit supplier and T16 complex supplier, with checked words, restoration, owner schedules and variable-rank moments. |
| §4 Address interchange | 🟡 | All field moves inherit the bit exponent; the running CRT now uses linear direct routing. | Prove selected arbitrary-source routing contracts. |
| §5 Butterfly layers; Appendix A | 🟡 | **The T16 node takes the layer margin `epsilon (1-lambda')` off the critical path; the layout margin `epsilon c (1-tau)` binds.** Complete compact runtime is proved. | Tighten recursive layer costs using stopped recursion, precision and proved recursive stock. |
| **§6 Synthetic transforms/layout** | 🟡 | **Layout saving `epsilon c (1-tau)` exceeds the public saving by a factor of about `1.77` but remains a nearby restriction.** | M2 retuned epsilon/c; next replace this charge by selected coordinate routing and a balanced prefix. |
| §7 Exact polynomial products | ✅ | Packing widths and extra logarithms must remain within budget. | Reuse the proved fast subroutine and exact algebra; revalidate under new widths. Not currently binding. |
| §8 Resampling | 🟡 | Current Gaussian exponent is `1/2 + 2^-7 + epsilon(1+2^-33)` (band width `α` logarithmic); margin `2^-7 - 31/2^39` at `epsilon=31/64`. | Chirped-correlation forward map (`O(M(p))` per element) and a wider banded inverse for `epsilon > 1/2`. |
| §9 Exact multiplication/cost | 🟡 | Direct CRT charge is `d(1+ell^tau)`; the final bound is the smallest stage margin. | Seven-stage bootstrap, all 47 linked target inequalities and unchanged exact output semantics. |
| §§10–11 Arithmetic/transposition corollaries | ⬜ | Downstream consequences, not multiplication bottlenecks. | Defer until the multiplication bound advances. |

#### The `epsilon < 1/2` barrier before the prime moduli

**The `epsilon < 1/2` barrier.** `2^-32` needs `epsilon > 0.557` with the existing supplier. Beyond `1/2` the `d` pairwise coprime moduli must sit in windows `[(1-2η)t, (1-η)t]` of relative width `η = 1/(4d)`, with `d ≫ log t`. Every elementary construction (`oddProd`, `1 + iM`, primorial shifts) needs `d² log d ≲ b`; the selected construction instead cites Baker–Harman–Pintz primes in short intervals. Mathlib has only Chebyshev bounds and Bertrand. So the next dyadic step needs **both** a short-interval prime supply (at least PNT with a `(log x)^-A` error term, `A > 2`) **and** a faster forward Gaussian map. The forward map is the selected chirped correlation (`notes/fast-gaussian-resampling.tex`), `O(M(p))` per element. The existing banded `B̃₀` with a larger `α² ≈ p^r`, `r < 1-ε`, suffices for the inverse up to `epsilon < 2/3`, so the phase-cell inverse is not on the critical path for `2^-32`.
The actual compact runtime removes the old full-slot control restriction. A
checked route certificate (`CompactGaussianRoute`) shows that with the **existing** supplier the selected Gaussian margin
lets every stage margin cover `2^-32` at `epsilon=5/8`, while no Gaussian
improvement alone reaches `2^-31`; M6 is needed beyond `2^-32`. Stopped recursion and precision/workspace accounting in M3–M5 continue.

#### M3 integration checklist

| Deliverable | Progress | Remaining gate |
| --- | --- | --- |
| Compact slot, basis, factor and recursive layer execution | ✅ | Checked actual programs and local costs. |
| Full runtime top transform and original size/precision bridges | ✅ | No per-piece readiness or execution premise remains. |
| Persistent original guard/dimension, per-round refresh and cleanup | ✅ | Checked from explicit original parameter sources. |
| Individual round stages and expanded main-host placement | ✅ | Checked staging/frame contracts and register embeddings. |
| Complete compact chunk round | ✅ | Checked actual preparation, top execution, restoration and cleanup from original round state. |
| Original-input bootstrap and transform-boundary cleanup | ✅ | Checked the dimension-minus-one correction, parameter precision source, retained globals and charged exit. |
| Counter-driven compact/direct dispatch | ✅ | Checked both actual branches, original butterfly semantics and full main-register frame. |
| Forward/opposite rounds and complete scans | ✅ | Checked original transform stream semantics and full-register restoration except I/O. |
| Bootstrap-to-transform frame | ✅ | Derives setup from real sources, establishes readiness and restores the original file except output after charged exit. |
| Complete forward/opposite transform specifications | ✅ | Existing layouts, actual distributed parameters and charged setup/exit; no layout, execution or readiness oracle remains. |
| Expanded main/source-stage entry and execution | ✅ | Original main invariant supplies entry; concrete source forward/opposite stages run with exact costs. |
| Expanded fifteen-stage arithmetic chain | ✅ | Actual retuned source stages and original primitive stages compose with exact twelve-step normalization overhead; outer input/distribution/output and full cleanup are also integrated. |
| Concrete round and setup cost accounting | ✅ | Checked actual records, setup, recursive calls, controls and cleanup; scalar-budget obligations remain explicit. |
| Uniform caller budgets and round overhead | ✅ | Combined scalar/divisor budgets, actual record validity and full overhead are derived for the old and larger chunks. |
| Larger-chunk recursive readiness and top execution | ✅ | Uniform shape, selected rows, descendant packing and actual parked top execution; full retuned chunk/transform composition remains. |
| Compact layer guard growth | ✅ | Actual original-precision guard fits any positive dimension power with dyadic constants; closed recurrence guard factor fits the proposed layer exponent. |
| Executable fourth-root parameters and distribution | ✅ | Charged table-slot overwrite and distribution wrapper preserve other fields; derived synthetic/layout fields consistently use the new chunk. |
| Complete fourth-root transforms | ✅ | Actual forward/opposite specifications use the new initial wires and existing executable layouts, with no execution/layout/readiness oracles. |
| Retuned reservation and complete top-cost exponent | ✅ | All reserved axes and the actual recursive top program, kernels and controls fit the proposed layer exponent with dyadic coefficients. |
| Retuned distribution-to-transform entry | ✅ | Actual charged distribution preserves the main invariant and supplies the new transform entry state. |
| Retuned aggregate analytic bound | ✅ | Stage envelope and actual machine costs are matched at saving `2^-34`. |
| Replaceable main procedure entry | ✅ | Checked restricted-call transport preserves layer execution when installing the expanded main body. |
| Actual retuned layer costs | ✅ | Complete chunk layer and direct branch costs match the retuned envelope; loop summation remains. |
| Retuned source transforms under replaceable main entry | ✅ | Full source stages execute with exact costs under the expanded recursive procedure table. |
| Main overhead, normalization and cleanup cost bridge | ✅ | Original primitive costs, fixed wrapper steps and expanded-host cleanup fit the sharper bound given the actual source-run match. |
| Actual compact round and loop cost sums | ✅ | Both loop directions fit the retuned convolution envelope given the explicit stash budget. |
| Expanded source and total-time aggregation | ✅ | All three actual source-run costs plus main overhead fit the stronger asymptotic bound, conditional on the two complete transform costs. |
| Complete transform and concrete main-time estimate | ✅ | Actual stash, layout, bootstrap, loops, source runs and main overhead satisfy the `2^-34` envelope with no remaining stage-cost hypotheses. |
| Stronger fixed-machine theorem | ✅ | Public `MathlibTM2.mulInTime` proves `2^-34` for every input pair; complete actual execution and cost hypotheses are discharged. |
| Stopped recursion | 🟡 | The full stopped digit scanner, semantic rebased records and cutoff from a supplied threshold are checked; global threshold generation, caller/precision integration and final layer-cost matching remain. |
