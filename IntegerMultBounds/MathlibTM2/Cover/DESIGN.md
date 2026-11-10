# Cover machine: paper audit (2026-11-09)

Question from the [M9/M10 audit](../M9/DESIGN.md): can a class-indexed cover run on this
machine, so that PR589 (and later the M10 word) has cheap routes?

Sources read at upstream `da637c87`: `notes/three-stage-cover-{bit,rows,assembly}.tex` and the
`PROOF.md` of `research/selected-bit-stream-routes`, `-fast-primitives`, `-recursive-caller` and
`-recursive-closure`. Here: [M8 design](../M8/DESIGN.md) and the
[PR589 hole note](../../../docs/pr589-hole/pr589-hole.tex). Upstream's Python checkers, JSON
receipts and `selected-bit-local-ring-sweeps` were not read or run. Upstream presents all of it as
written argument without a fixed-tape compiler or formal proof.

## Verdict

Go on paper. No step of the cover machine is priced as a product of the payload width and the
atom width, which is what closed the fixed-role route in the hole note. Three components are new
and intrinsic, and they carry most of the work: weights, coefficients computed from labels, and
the bad-class fallback.

| Piece | Status here |
| --- | --- |
| Stopped recursion, atoms `(Z/q^w)^f`, variable-rank reversed children, `F L F` wrapper | Exists (M8 stage 2) |
| Recurrence with linear and leaf tolls, extra fallback children | Exists: `StoppedRecurrence.stopped_closed` takes any child list |
| Leaf interchange at width `w` with prefix, gap and suffix | Exists: `BinaryInterchangeBudget.uniform_bound` |
| Label covariance, weighted contract, weighted leaf | Proved in [`Weighted.lean`](Weighted.lean) |
| Good normal form over the atom ring | Proved in [`GoodForm.lean`](GoodForm.lean) |
| Label routes | New, from existing primitives (section 3) |
| Row stock per level, label layout, good/bad split, directory | New (section 4) |
| Coefficients and weights computed from labels on tape | New, largest item (section 5) |
| Unit-pivot fallback on bad classes | New (section 6) |
| PR589 as a cover network, moment certificate, retune | New (section 7) |

## 1. What the cover is

Every role stream gets a label `g`, an invertible `m × m` matrix over the atom ring
`R_w = Z/q^w`. The stream at label `g` is stored in the frames `g U g⁻¹`.

- The full reversed interchange is the same at every label, so one sweep over all labels
  completes every role (`revExchangeOf_one_conj`).
- A route `σ` changes the label to `g σ` and the local projector to `σ⁻¹ M σ` and keeps the frame
  (`label_route`). A gate between two wires with different routes is a permutation of one wire's
  labels, a pointwise XOR, and the inverse permutation. No payload address digit moves.
- Helpers that share a family sit at different labels, so the cover also replaces the five host
  classes of hole A.

The price is that every frame, adapter and pivot now depends on the label, which is an address
field. That forces the three new components.

## 2. Why the cost closes

Per node of `n` atoms and volume `V`:

| Work | Cost | Reason |
| --- | --- | --- |
| Atom adapters | `O(V n)` | One ordered pass per atom; as in M8 stage 2. |
| Routes | `O(V w^(1-a_leaf))` | They move label atoms of width `w`, through the leaf interchange. Independent of `n`. |
| Splits, XORs, parking | `O(V)` | Unchanged. |

So `T(n, w) ≤ Σ c_r T(r⌊n/m⌋, w) + C n + C w^(1-a_leaf)`, the shape `stopped_closed` already
proves, with the fallback children as extra entries of weight `ε`. With `μ_1 < 1` and
`μ_(1-c) < 1`, and `w = ⌈e^c⌉`, the ordinary saving is `c(1-c) + c·a_leaf`.

For PR589 upstream certifies `c = 17/10000` (`μ_1 < 199/200`, `μ_(1-c) < 9999/10000`). With this
repository's leaf (`a_leaf = 1.2388e-4`) that is `a_b ≈ 1.6973e-3`. The atom exponent rises from
`1/1000` to `c`, which the wrapper needs anyway.

## 3. Label routes

Upstream writes `g = g0 + qG`, keeps the low class `g0 ∈ GL_m(F_q)` as one index and the `m²`
high fields as a box, and updates the high fields with carries read from the low class. The low
classes are permuted through one tape per class.

A simpler layout works here. Take the label box to be all of `M_m(R_w)`: `m²` label atoms of `w`
digits. Right multiplication by `σ` is then the same linear map on each of the `m` label rows,
with no carries and no class tapes:

- factor it as lower-triangular passes and transpositions (`Swap.LowerTriangular.factorization`);
- the passes are ordered-affine steps on label atoms, `O(V)` each;
- each transposition exchanges two label atoms with spectators between them: one leaf
  interchange at width `w`.

Singular labels hold padding. Routes preserve them, since `σ` is invertible. The stock is borrowed
and padded once at the outer wrapper, and the padding pass tests each label's low digits. The
density of invertible classes is above `1 - 2/q` per level, so the padded volume grows by at most
`e^(O(1/q))` over `O(log e)` levels. That exponent loss is below `10^-23` at `q > 2^80`; it must
be carried in the cost statement.

Upstream counts at most 3,520 leaf calls per data route and 1,664 per hosted route with its
carry scheme. The count for the box layout has not been made.

A fixed finite label group would make labels ordinary roles and remove sections 5 and 6. I did not
find one. With a shared basis on the common complement, two routes whose lines meet at 60° have
a principal cosine of `3/4` or `1/4`, so their product has infinite order. Other basis choices
were not settled.

## 4. Stock, layout and classes

- **Row divisor.** Each level consumes `W · A^(m²)` rows (`A = q^w`): the role index and the label
  box. The depth is `D(n) = 1 + D(r_max ⌊n/m⌋)`, at most `2 log₂ e` for PR589 (`r_max = 42`).
  `RecursiveRowDivisor` builds `roleCount^k`; it needs a second factor and a depth that follows the
  largest child.
- **Borrowing.** The stock is `k = O(m² w log e)` digits taken from the head chunk, as in
  upstream's wrapper. `k < e/2` holds for large `e` because `w = e^c`.
- **Frozen labels.** A child treats the labels of its ancestors as spectator prefixes and takes
  its own label from unused stock. Its weights may read ancestor labels and nothing else.
- **Good and bad classes.** The branch depends only on the low digits of the label. Split each
  role stream into a good and a bad stream by that predicate, run one child per stream, and merge.
  The split streams are not boxes, so each carries a directory: the list of label values of its
  prefixes. Upstream's `Δ = 1 + C H (h+1) f` symbols bounds it well below the payload.

## 5. Coefficients from labels

At label `g` the projector of a move is `g P g⁻¹`. Its northeast elimination has unit
lower-triangular adapters and pivots that are rational functions of the label. Three consequences:

- **Weights.** A pivot cannot be applied as a scaling: scaling an atom by a unit that depends on
  the prefix has no bounded streaming form. The pivots are passed to the child as weights. The
  child contract is `F_A (h, d) = (A C d, C A⁻¹ h)` (`weighted`, `weighted_eq`), and one move is
  conjugated adapters around one weighted child with weights `α δ` (`weighted_good_child`). Weights are
  paid at the stopped leaves, four leaf interchanges and three shears per atom pair (`leaf_word`).
- **Adapters.** A weighted adapter coefficient is `α_i L_ik α_k⁻¹`; it stays lower triangular
  (`lower_diag_conj`). The streaming pass is the existing ordered shift with an offset computed
  per prefix block.
- **Evaluator.** The machine must compute, from the label atoms of a prefix: `g⁻¹`, the projector,
  its elimination, and the product of one pivot per ancestor. That is modular arithmetic on
  `w`-digit numbers and elimination of a fixed-size matrix. The cost is polynomial in `w` and the
  depth per prefix block, and a block has at least `q^w` cells. In the fallback an expression reads
  two parent weights, so the cost is `2^depth` times a polynomial; `2^depth ≤ 8e²` and
  `e ≤ w^(1/c)` keep it polynomial in `w`.

The evaluator is the largest new machine component. `Machine/Binary{Add,Sub,Multiply,Divide}`
supply the arithmetic. The existing atom passes take fixed rational coefficients
(`Coordinates.CoeffSupported`); they need a variant whose offset comes from a tape.

## 6. Fallback

On a bad class some leading minor is not a unit, and reduction modulo `q` proves nothing over
`R_w`. Upstream eliminates the full `2m × 2m` residual with unit pivots. Pivot choices depend only
on the low class.

- An upper addition is a lower addition between two exchanges; an exchange of two sub-fields of
  one bank is a reversed child between two reversals of the later field; a reversal is one
  reversed child on the two halves of a field.
- That gives fewer than `32 m²` children of at most `⌊n/m⌋` atoms (`fallback_children`).
- The bad fraction per request is at most `2 m³/q`, from the degree of the minors and the density
  of `GL_m(F_q)`. No union over requests is needed, since the moment averages each request.

New here: children at arbitrary sub-field positions inside one bank, and a
nonvanishing-polynomial count over `F_q`. `GenericBasis` proves the nonvanishing over `ℚ` by the
combinatorial Nullstellensatz; the counting form (Schwartz–Zippel) is a different statement.

Bad classes cannot be turned into padding. A gate pairs label `g` with `g σ`, so the padded set
would have to be closed under every route.

## 7. Build order

Each step ends in checked Lean. Steps 1–3 are algebra and independent of the machine.

| Step | Content | Size |
| --- | --- | --- |
| 1 | Covariance, weighted contract, pivots as child weights, leaf word, fallback count | done, [`Weighted.lean`](Weighted.lean) |
| 2 | Good normal form over a commutative ring: if `P` factors through `r` coordinates and its leading minors of sizes `1..r` are units, then `P C = L Δ Π_r R` with unit lower `L`, `R` (`good_form`), and the move is one weighted child (`good_move`) | done, [`GoodForm.lean`](GoodForm.lean) |
| 3a | Unit-pivot elimination over a local ring: `n (n-1)` row additions and `n` exchanges make an invertible matrix diagonal with unit entries (`fallback_form`) | done, [`Fallback.lean`](Fallback.lean) |
| 3b | Row operations as children (`add_conj`, `ordinary_of_reversed`); one itinerary per residue class (`itinerary_form`, `exists_itinerary`, `valid_congr`); the bad-class count (`bad_count`) | done, [`Fallback.lean`](Fallback.lean), [`Itinerary.lean`](Itinerary.lean), [`BadClass.lean`](BadClass.lean) |
| 4 | Machine: label box and padded stock, routes on label atoms, split by class, directory | 8–15k |
| 5 | Machine: coefficient evaluator and offset-from-tape atom passes | 15–30k |
| 6 | Machine: weighted children and leaves, fallback schedule, node induction | 10–20k |
| 7 | PR589 as a cover network from the role-level node of `M6/Bit*`; histogram and moment certificate at `1 - c`; wrapper at atom exponent `c`; seam and retune | 5–10k |

The sizes are rough. The stage-2 machine that steps 4–6 extend (`M8/RevMachine`,
`M8/Stage2Machine`) is about 26k lines.

The algebra of steps 1–3 is checked. Left for the machine steps, where the layout fixes them:

- `Z/q^w` as a local ring with the unit-reflecting map to `F_q`, to instantiate `valid_congr`;
- the rank factorization `P = A B` of a conjugated rational idempotent, for `good_form`;
- the final diagonal of the fallback as `n - 1` unit pairs and a sign, and the reversal of a
  field as one reversed child on its two halves;
- the program on head and tail fields assembled from `Elim`, with its child count against
  `fallback_children`.

`bad_count` is stated against the whole label box, which is what the box layout needs: at most
`r (r+1) (m+1) / (2q)` of the labels are bad for one move.

Decision point: the remaining cost is machine work of known kind. If steps 4–6 are judged too large, the fallbacks are those of the hole note: a bit
word with a port-independent line, or another cover-free supplier.

## 8. Open questions

1. Leaf-call count per route in the box layout, and the resulting constant.
2. Whether the low digits of the label must lead the address order for the class split, or a
   split pass can test them in place.
3. The exact moment root for the PR589 histogram, in place of upstream's `c = 17/10000`.
4. Recompute `kappa` for cover + PR589 with full-width chunks (`Cost/CompactInterimParameters`).
   The hole note's `2^-10.8` and `2^-10.4` predate them.
5. The M10 word of PR 4359 has cover rank `2^6552928412`. Every statement in steps 2–6 must keep
   the rank a variable.
