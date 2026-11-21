module

public import IntegerMultBounds.MathlibTM2.M6.BitNodeInterchange
public import IntegerMultBounds.MathlibTM2.M6.BitRecurrence

/-!
# The five-class node: children, moment and the closed recurrence

**Headline** (`five_class_node`): the five-class node is a finite program of 29 pieces on
`5W = 142080` roles; on arbitrary dirty streams it is the parent interchange `D_1` on every role
(`runNode_interchange`), and each class run changes a helper's host role only by the exchange on
the helper's slot, the helper restored in its final frame (`invoke_host`); its child list
realizes `fiveHistogram`, five times `bitHistogram`, so at weight `1/(5W)` the occurrence moment is
S2's and at most one at `1 - 10/5769`.

* `Piece.children`: every class run of a stage makes the word's paid frame changes, `localPaid`
  (S1), and every remainder piece makes one child per role of its pair whose remaining interval is
  nonempty, of its rank (`rank_remainder`).
* `five_variable_closed`: `VariableRecurrence.variable_closed_of_rank` for this child list at
  weight `1/142080`. The execution premises (child sizes, per-node cost) are the physical machine's
  and stay hypotheses.

**Scope: an upstream-conditional certificate.** This certifies upstream's PR589 accounting under
its idealization: each frame change is an exact partial swap priced as one child of its rank, and
the stage routes and helper charts are exact coordinate changes priced at nothing.
`five_variable_closed` takes the per-node cost as the hypothesis `hcost`, which only a machine
realizing the idealization discharges. No such machine is known. On the H-before-D tape each
port-dependent route costs interchanges, about `+0.49` on the moment against a slack of `0.0056`;
upstream's fixed-width routes act on cover-class labels, under obligations open upstream
(`M6/DESIGN.md`, "Realizability of the PR589 accounting"). These theorems give no physical
exponent.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M6.BitNode

open IntegerMultBounds.Networks.Certificates.PR589
open IntegerMultBounds.Networks.Certificates.PR589.Nine
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Layer.SelectedMoments
open IntegerMultBounds.MathlibTM2.M6.BitOccurrences
open IntegerMultBounds.MathlibTM2.M6.BitSchedule
open IntegerMultBounds.MathlibTM2.M6.BitHosting

/-- The positive remainder ranks of idle `i` on the 222 copies of one replica and class. -/
def remainderRanks (i : ℕ) : List ℕ :=
  ((List.range 222).map fun c => (idleRanks 4).getD i 0 - 8 * copyCount i c).filter (0 < ·)

/-- The child calls of a piece. -/
noncomputable def Piece.children : Piece → List ℕ
  | .stage _ => (stageRuns.map fun _ => Geometry.Moves.localPaid).flatten
  | .remainder i => (stageRuns.map fun _ => remainderRanks i).flatten
  | _ => []

/-- The child list of the five-class node. -/
noncomputable def nodeChildren5 : List ℕ := nodeProgram.flatMap Piece.children

/-- Five times the selected bit histogram. -/
def fiveHistogram : List (ℕ × ℕ) := bitHistogram.map fun e => (e.1, 5 * e.2)

theorem remainderRanks_eq : (∀ i < 9, remainderRanks i =
    (copyCounts i).map fun k => (idleRanks 4).getD i 0 - 8 * k) ∧ remainderRanks 9 = [] := by
  decide +kernel

theorem stageRuns_length : stageRuns.length = 160 := by
  decide +kernel

theorem sum_runs (X : List ℕ) (price : ℕ → ℕ) :
    (((stageRuns.map fun _ => X).flatten).map price).sum = 160 * (X.map price).sum := by
  rw [List.map_const', stageRuns_length, sum_replicate_flatten]

theorem remainders_sum (price : ℕ → ℕ) :
    (remainders.map price).sum = ((List.range 10).map fun i => ((remainderRanks i).map price).sum).sum := by
  rw [← (remainders_perm.map price).sum_eq, sum_flatMap,
    show List.range 10 = List.range 9 ++ [9] from List.range_succ, List.map_append,
    List.sum_append, List.map_singleton, List.sum_singleton, remainderRanks_eq.2, List.map_nil,
    List.sum_nil, add_zero]
  refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
  rw [remainderRanks_eq.1 i (List.mem_range.mp hi)]

theorem nodeChildren5_price (price : ℕ → ℕ) :
    (nodeChildren5.map price).sum = 5 * (nineRanks.map price).sum := by
  rw [nineRanks, List.map_append, List.sum_append, sum_replicate_flatten, sum_replicate_flatten,
    remainders_sum]
  simp only [nodeChildren5, nodeProgram, List.flatMap_cons, List.flatMap_nil, Piece.children,
    List.map_append, List.sum_append, sum_runs, List.append_nil, List.map_nil, List.sum_nil]
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, List.nil_append]
  ring

/-- Price COPY, phase moves and idle remainders separately. The nine COPY
windows of each invocation already occur in the node's child sum. -/
theorem nodeChildren5_split_price (price : ℕ → ℕ) :
    (nodeChildren5.map price).sum = 12960 * price 7 +
      1440 * (((Geometry.Moves.phaseValues.filter (· ≠ 0)).map price).sum) +
      160 * (remainders.map price).sum := by
  rw [nodeChildren5_price,nineRanks,List.map_append,List.sum_append,
    sum_replicate_flatten,sum_replicate_flatten,Geometry.Moves.localPaid,
    Geometry.Moves.phase_ranks,Geometry.Moves.copyRanks_eq,List.map_append,List.sum_append,
    List.map_replicate,List.sum_replicate]
  simp only [smul_eq_mul]
  ring

/-- The node's child list realizes five times the selected bit histogram. -/
theorem nodeChildren5_realizes : Realizes nodeChildren5 fiveHistogram := by
  apply realizes_of_cost
  intro price
  have h := (nineRanks_realizes.map price).sum_eq
  rw [sum_map_expand] at h
  simp only [smul_eq_mul] at h
  rw [nodeChildren5_price, h]
  simp only [fiveHistogram, List.map_map, Function.comp_def]
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro e _
  ring

theorem histMoment_five (m σ : ℝ) : histMoment fiveHistogram m σ = 5 * histMoment bitHistogram m σ := by
  simp only [histMoment, fiveHistogram, List.map_map, Function.comp_def]
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro e _
  push_cast
  ring

/-- At weight `1/(5W)` the node's occurrence moment is S2's, at most one at `1 - 10/5769`. -/
theorem five_moment_le_one :
    ∑ i : Fin nodeChildren5.length,
      (1 / (142080 : ℝ)) * ((nodeChildren5[i.1] : ℝ) / 64) ^ (1 - bitSaving) ≤ 1 := by
  rw [occurrence_moment_eq nodeChildren5_realizes, histMoment_five]
  have h := bit_bill_le
  have hs : 0 ≤ surcharge bitHistogram 64 (1 - bitSaving) := by
    unfold surcharge
    positivity
  rw [add_div] at h
  have : 5 * histMoment bitHistogram 64 (1 - bitSaving) / 142080 =
      histMoment bitHistogram 64 (1 - bitSaving) / 28416 := by ring
  rw [this]
  have hd : 0 ≤ surcharge bitHistogram 64 (1 - bitSaving) / 28416 := by positivity
  linarith

theorem nodeChildren5_bounds (i : Fin nodeChildren5.length) : 0 < nodeChildren5[i.1] ∧ nodeChildren5[i.1] ≤ 42 := by
  have hmem : nodeChildren5[i.1] ∈ nodeChildren5 := List.getElem_mem i.2
  have hperm := nodeChildren5_realizes.mem_iff.1 hmem
  simp only [expand, fiveHistogram, bitHistogram, List.map_cons, List.map_nil, List.flatMap_cons,
    List.flatMap_nil, List.mem_append, List.mem_replicate, List.not_mem_nil, or_false] at hperm
  omega

theorem nodeChildren5_le (i : Fin nodeChildren5.length) : nodeChildren5[i.1] ≤ 42 := (nodeChildren5_bounds i).2

/-- **The five-class bit recurrence.** A recursion whose internal nodes make one child call per
occurrence of the five-class node's child list, of size at most `rank/64` of the parent and weight
`1/142080`, with per-node overhead `C₁ ((K e)^τ + 1)` and leaf cost `C₀ e`, costs at most
`C (K^τ e^λ) + C₀ e^(1-a) u^a` at every `λ > 1 - a`, `a = 10/5769`. Under upstream's idealization
the five-class node meets `hcost`; a tape machine meeting it is the open point of the module
docstring. -/
theorem five_variable_closed {Node : Type*}
    (size : Node → ℕ) (child : Node → Fin nodeChildren5.length → Node)
    (cost : Node → ℝ) (u : ℕ) {τ lam K C₀ C₁ : ℝ}
    (hτ : 0 ≤ τ) (hτl : τ ≤ lam) (hlam : 1 - bitSaving < lam) (hK : 1 ≤ K)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hu : 1 ≤ u)
    (hleaf : ∀ x, size x ≤ u → cost x ≤ C₀ * size x)
    (hsize : ∀ x, u < size x → ∀ i,
      (size (child x i) : ℝ) ≤ ((nodeChildren5[i.1] : ℝ) / 64) * (size x : ℝ))
    (hcost : ∀ x, u < size x →
      cost x ≤ C₁ * ((K * size x) ^ τ + 1) + ∑ i, (1 / (142080 : ℝ)) * cost (child x i)) :
    ∀ x, cost x ≤
      2 * C₁ / (1 - ((42 : ℝ) / 64) ^ (lam - (1 - bitSaving))) * K ^ τ * (size x : ℝ) ^ lam +
      C₀ * (size x : ℝ) ^ (1 - bitSaving) * (u : ℝ) ^ (1 - (1 - bitSaving)) := by
  have ha : bitSaving = 10 / 5769 := rfl
  exact VariableRecurrence.variable_closed_of_rank size (fun _ => nodeChildren5.length) child
    (fun _ i => nodeChildren5[i.1]) (fun _ _ => 1 / (142080 : ℝ)) cost u (m := 64) (R := 42)
    (by norm_num) (by norm_num) (by norm_num) hτ hτl (by rw [ha]; norm_num)
    (by rw [ha]; norm_num) hlam hK hC₀ hC₁ hu (fun _ _ => by norm_num)
    (fun _ _ i => by exact_mod_cast nodeChildren5_le i) hleaf hsize hcost
    (fun _ _ => five_moment_le_one)

/-- **The five-class node under upstream's idealization**, as one result. Frame changes are ideal
partial swaps priced as one child of their rank, and routes and charts are free. The result is
conditional on that idealization and gives no physical exponent; see the module docstring.
1. The five-class node is a finite program of 29 pieces on `5W = 142080` roles; each stage piece
   runs the invocation once per replica and class, 160 runs.
2. On arbitrary dirty streams it is the parent interchange `D_1` on every role, and in every class
   run a helper's host role changes only by the exchange on the helper's slot.
3. Its child list realizes five times `bitHistogram`.
4. At weight `1/(5W)` the occurrence moment is at most one at `1 - 10/5769`, so
   `five_variable_closed` applies at every `λ > 1 - 10/5769`. -/
theorem five_class_node :
    Fintype.card Role = 142080 ∧ nodeProgram.length = 29 ∧ stageRuns.length = 160 ∧
    (∀ (X : State) (ρ : Role), runNode X ρ = along (exchange 1) (X ρ)) ∧
    (∀ (n : Fin 9) (r : Fin 32) (d : Fin 5) (X : State), ∀ h < 439,
      invoke n r d X (hostRole n r d h) = along (exchange (helperSpan n h)) (X (hostRole n r d h))) ∧
    Realizes nodeChildren5 fiveHistogram ∧
    ∑ i : Fin nodeChildren5.length,
      (1 / (142080 : ℝ)) * ((nodeChildren5[i.1] : ℝ) / 64) ^ (1 - bitSaving) ≤ 1 :=
  ⟨card_role, rfl, stageRuns_length, runNode_interchange,
    fun n r d X h hh => invoke_host n r d X h hh, nodeChildren5_realizes, five_moment_le_one⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
