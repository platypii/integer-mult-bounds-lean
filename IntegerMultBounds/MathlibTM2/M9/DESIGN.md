# M9/M10 feasibility audit (first pass, 2026-11-09)

Question: can the productive-job construction of upstream
[PR 4359](https://github.com/CrocSwap/integer-mult-bounds/pull/4359) run on this
machine, and in what order should it be built?

Sources read: the PR body and four notes at `da637c87`
(`FINITE-PRECOMPILATION.md`, `FINITE-TEMPLATE-CLOSURE.md`, `OUTER-TRANSFER-AUDIT.md`,
`DELAYED-COVER-BRIDGE.md`), and this repository's [M6 design](../M6/DESIGN.md),
[PR589 hole note](../../../docs/pr589-hole/pr589-hole.tex) and
[PR97 note](../../../docs/pr97-stage1/pr97-stage1.tex). Upstream numbers are quoted,
not replayed. The upstream JSON receipts, `AUDIT.md`, `EXPLICIT-TEMPLATE-BOUNDS.md`
and the native bindings were not read. The PR is merged upstream as a conditional,
unreviewed written argument.

## Verdict

| Part | Verdict | Reason |
| --- | --- | --- |
| M9 complex supplier | Feasible, not yet useful | No structural obstacle found, but it cannot move `kappa` while the bit supplier binds. |
| M10 bit supplier as specified | No-go on this machine | It needs a class-indexed cover machine that does not exist here. |
| Cover machine (new prerequisite, "M10a") | Open; decides the 0.0023 target | Same missing piece as the PR589 hole. Worth about 3.6 bits before any M9 work. |

Recommended order: audit and, if it survives, build the cover machine with the
PR589 certificates already checked here. Then M9 and M10 on top. M9 first is the
wrong order.

## 1. M9 alone does not move the bound

The compact route needs `tau < lambda`, `sigma < lambda` and `lambda < lambda'`,
and the binding margins are `epsilon (1-lambda')` and `epsilon (1-tau)`.

| Supplier | Saving in the proof |
| --- | --- |
| Bit: PR97 design-B | `1-tau = 1.2388e-4` |
| Complex: T16 | `1-sigma > 1e-3` (`log_73 (F/NW) < 999/1000`); `1.6755e-3` with variable-rank children |

The bit saving is about eight times smaller than the complex one, so `tau` binds
every margin. Raising the complex saving to upstream's `0.002304` changes nothing
until the bit saving passes `1e-3`. The M6 design table shows the same for
"T16 + current bit".

M9 comes before M10 in the plan only because M10 reuses its compiler.

## 2. M10 needs a class-indexed cover

Upstream's BIT unit is not a new word. It is the PR589 local word (661 columns,
111 ports, 666 embedded charts, 636 rational frames) under a p3 controller, then
the finite compiler, then one ambient cover.

- Every array role carries a cover coordinate `g` in `GL_N(Z/q^w)`, with
  `N = 2^6552928412` and `q > 25,600,000 N^5`.
- Matching a parent request to a child endpoint is the route `g -> gS` on a whole
  cover fiber. Port charts are kept as right-route symbols on the same label.
- Each route is priced `O(V w^(1-a_old))` by upstream's cover-routing lemma, with
  `a_old = 384599/10^10`. That lemma moves label digits, never payload digits.
- Final rank-one leaves become weighted children, and bad residue classes pay a
  local-ring fallback.

This machine has a fixed role count and no cover classes. The PR589 hole note
already records the consequence:

- a route acts on the payload's own sub-fields and costs about `V n w^p` per node,
  superlinear in the payload width;
- every upstream supplier with `a_b > 1.24e-4` needs a class-indexed cover or the
  compressed geometry with port routes;
- upstream's cover architecture was open by its own account: data-dependent
  recursive compiler, weighted calls, correlated-helper domain bridge and COPY
  lifetimes.

PR 4359 answers the weight mismatch (one common external weight, lowered only at
the leaves) and the correlated-helper premise (arbitrary-input children). It does
not build the cover machine; it cites it as retained.

The productive-job idea has no purchase on the bit word that does run here. PR97
has no helpers, charts or hosting, so there is nothing to keep.

## 3. The cover machine is the real gate

With a cover machine, PR589 itself runs, without the M9 compiler.

| Configuration at `epsilon = 31/64` | `kappa` | Source |
| --- | --- | --- |
| Today | `2^-14.02` | proved |
| Cover + PR589 (`a_b ≈ 1.697e-3`) + T16 rank-one | about `2^-10.8` | hole note §4.5 |
| Cover + PR589 + T16 variable-rank | about `2^-10.4` | hole note §4.5 |
| Cover + M9 + M10 | about `2^-9.81` | `epsilon × 0.0023` |

The two hole-note rows were computed before full-width chunks; recompute them in
`Cost/CompactInterimParameters` before relying on them.

So the cover machine is worth about 3.6 bits, and the M9/M10 compiler about 0.5 bit
on top. Near-one dimensions (S4–S6, R3–R4) add about one bit to each row. These are
planning margins, not theorems.

What a cover machine must supply here:

1. Streams indexed by a low class in `GL_N(F_q)` and `N^2` high fields of `w-1`
   digits, ordered label first, with a row stock carrying
   `|GL_N(F_q)| q^(N^2 (w-1))`. `RecursiveRowDivisor` assumes a power of a fixed
   role count.
2. The route `g -> g sigma` as a block permutation of low classes plus carry-aware
   high-field updates through a bootstrapped interchange at width `w-1`. Today's
   bit interchange exceeds `a_old`, but an explicit bootstrap-interface theorem is
   still required.
3. Fresh classes for children, and a weight that is independent of the current
   cover row.
4. The weighted rank-one normal form with its bad-class fallback.
5. The stopped recurrence at atom width `e^delta` with `delta` above the target
   saving. The current stop at `e^(1/1000)` caps the ordinary saving at `0.001`.

Likely reusable: `VariableRecurrence.variable_closed`, `StoppedRecurrence`, the
`F L F` wrapper, `GenericBasis` and `ReversedExchange` (cover-free normalization of
one projector), the PR589 local profile, frames, hosting and bill certificates, and
the five-class node semantics.

`N` must stay a variable in every statement. The winning ranks are
`2^276540184361` and `2^6552928412`; nothing at those ranks can be data.

## 4. M9 contract, for when it becomes useful

Upstream's four hypotheses, priced against the layer machine:

| Hypothesis | Here | Open item |
| --- | --- | --- |
| All-column native word with arbitrary-input endpoints | The T16 node already runs on dirty streams with rank-one kernels as layer factors. The p3 controller (seven native calls, 2,242 productive fields, one owned centre) is not ported. | Port the p3 word and its helper endpoints. |
| Disjoint splitting and complete spectators | `Layer/Spectators` exists; not inspected. | Check it covers `r < N` remainder axes. |
| Whole-job adapters | Slot XORs, slot phases and translations exist. | Block permutations of `f`-axis groups are sub-field moves. Price them through the bit interchange inside `internal < lambda`, or show the compiler needs only role relabeling. |
| Finite-program closure | `Layer/Recurrence.recurrence_closed` takes a uniform branching bound `F/NW < m^sigma`. | State it for abstract `(N, W, P)` and prove the compiler's leaf count structurally. |

Further obligations:

- Theorem 1G's integer lockstep flow, the denominator clearing and the leaf
  recurrence `L(n) = Σ w_s L(n-s) + Σ x_e L(e)`, for arbitrary finite data. Sussman's
  `wht-power-saving-lean` has Lean results on the flow; upstream says they do not
  verify this compiler. Not inspected.
- One owned centre per live mixed-unit instance (`O = U`), not the eight private
  centres of T16.
- The linear precision guard `C0 d` with `C0 = 32 N (P+E)^2`, and stock
  `q0 = ceil(log2 W) · D(d)`. This is M4, instantiated for the compiled template.

## 5. Next steps

Step 1 is done: the [cover machine audit](../Cover/DESIGN.md) is a go on paper, with
its own build order.

1. Audit the cover machine on paper against upstream's
   `notes/three-stage-cover-bit.tex` and the `selected-bit-stream-routes`,
   `-fast-primitives`, `-recursive-caller` and `-recursive-closure` packages. Price
   label-first packets, the route, fresh classes and the fallback on the actual
   tape primitives. Output: go or no-go for item 3.
2. On a go, build it for plain PR589 first. The certificates exist and the payoff
   is the largest single step available.
3. Then M9 and M10 together, with M4 for their templates.
4. On a no-go, the remaining routes are the hole note's: a bit word with a
   port-independent line, or a different cover-free bit supplier. The ceiling then
   stays near `2^-13` with near-one dimensions.
