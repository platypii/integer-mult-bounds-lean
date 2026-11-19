module

public import IntegerMultBounds.MathlibTM2.M8.Rev97Machine
public import IntegerMultBounds.MathlibTM2.M8.Stage2LinkB
public import IntegerMultBounds.MathlibTM2.M8.Global.NodeRanksB
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Contract

/-!
# The block children of the stage-2 PR97 node

A control's block children are its edge programs with interchanges, one child of rank `r` for a
program of `r` interchanges (`childRanks`). For the stage-2 list of a framed list they are the
ranks of its frame changes (`Rev.programs_revPhysOf`), so their moments are the moments of its
moves (`sum_childRanks`). `ranks97`, the children of `control97` (the control of `rev97` and
`rev97m`), therefore have the two moment gaps of the stage-2 histogram (`moment₁_ranks97`,
`momentτ_ranks97`).

Every child is smaller than the node: the actual gauged design-B exchanges have rank below
529 (`Global.DesignB.rank_lt`). The data paths telescope, local side moves have rank at most 23,
and every side exterior has rank at most 528. The complete node histogram supplies both moment
gaps at the design-B saving.

`rev97_closed` and `rev97_contract`: with the leaf bound below `529` and the node recurrence
over `ranks97` on `W` roles, the reversed family costs at most
`C/(1-q₁) n + C/(1-q_τ) n^τ* L`, at `τ* = 1 - 12402/10⁸`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Global

/-- The ranks of a control's block children: the interchange counts of its edge programs that
have interchanges. -/
def childRanks {ι : Type} {m : ℕ} (s : List (Step ι (FieldProgram m))) : List ℕ :=
  ((Step.programs s).map AffineFieldProgram.interchanges).filter (0 < ·)

namespace Rev

variable {ι : Type} {d : ℕ}

/-- The interchange counts of the stage-2 list are the ranks of the frame changes. -/
theorem programs_revPhysOf {G G' : Mat d} (h : G * G' = 1) (h' : G' * G = 1) :
    ∀ L : List (FStep ι d), (Step.programs (revPhysOf G G' L)).map AffineFieldProgram.interchanges =
      (edgeMats L).map Matrix.rank
  | [] => rfl
  | s :: rest => by
    have ih := programs_revPhysOf h h' rest
    cases s <;>
      simpa [revPhysOf, Step.programs, edgeMats, revStep, revProgram_interchanges,
        rank_conj h h'] using ih

end Rev

namespace Rev97Ranks

variable {ι : Type} {d : ℕ}

theorem edgeMoment_eq_sum {M : Type} [AddCommMonoid M] (φ : ℕ → M) :
    ∀ L : List (FStep ι d), edgeMoment φ L = ((Rev.edgeMats L).map fun U => φ U.rank).sum
  | [] => rfl
  | s :: rest => by
    cases s <;> simp [edgeMoment, Rev.edgeMats, edgeMoment_eq_sum φ rest]

theorem sum_map_filter_pos {M : Type} [AddCommMonoid M] (φ : ℕ → M) (hz : φ 0 = 0) :
    ∀ l : List ℕ, ((l.filter (0 < ·)).map φ).sum = (l.map φ).sum
  | [] => rfl
  | r :: l => by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp [hz, sum_map_filter_pos φ hz l]
    · simp [hr, sum_map_filter_pos φ hz l]

/-- The moments of the block children of a stage-2 list are the moments of its moves. -/
theorem sum_childRanks {M : Type} [AddCommMonoid M] (φ : ℕ → M) (hz : φ 0 = 0) {G G' : Mat d}
    (h : G * G' = 1) (h' : G' * G = 1) (L : List (FStep ι d)) :
    ((childRanks (Rev.revPhysOf G G' L)).map φ).sum = edgeMoment φ L := by
  rw [childRanks, sum_map_filter_pos φ hz, Rev.programs_revPhysOf h h', edgeMoment_eq_sum,
    List.map_map]
  rfl

theorem mem_childRanks {G G' : Mat d} (h : G * G' = 1) (h' : G' * G = 1) {L : List (FStep ι d)}
    {r : ℕ} (hr : r ∈ childRanks (Rev.revPhysOf G G' L)) : 0 < r ∧ ∃ U ∈ Rev.edgeMats L, U.rank = r := by
  rw [childRanks, List.mem_filter, Rev.programs_revPhysOf h h', List.mem_map] at hr
  obtain ⟨⟨U, hU, rfl⟩, hpos⟩ := hr
  exact ⟨by simpa using hpos, U, hU, rfl⟩

-- Plain-node full-rank exclusion and local-top helpers: restore from bd16f751.
/-- Every exchange of the selected gauged node is smaller than its width. -/
theorem rank_lt {U : Mat 529} (hU : U ∈ Rev.edgeMats Global.DesignB.framedNode) : U.rank < 529 :=
  Global.DesignB.rank_lt hU

end Rev97Ranks

open Rev97Ranks Stage2Moments
open Global.Branching97 (roleCount)

/-! ### The children of the stage-2 node -/

/-- The ranks of the block children of the stage-2 PR97 node. -/
def ranks97 : List ℕ := childRanks control97

theorem rev97_control : rev97.control = control97 := rfl

theorem rev97m_control : rev97m.control = control97 := rfl

theorem ranks97_pos {r : ℕ} (hr : r ∈ ranks97) : 1 ≤ r :=
  (mem_childRanks basis97_inv basis97_inv' hr).1

theorem ranks97_lt {r : ℕ} (hr : r ∈ ranks97) : r < 529 := by
  obtain ⟨-, U, hU, rfl⟩ := mem_childRanks basis97_inv basis97_inv' hr
  exact rank_lt hU

theorem sum_ranks97 (φ : ℕ → ℝ) (hz : φ 0 = 0) : (ranks97.map φ).sum = edgeMoment φ Global.DesignB.framedNode :=
  sum_childRanks φ hz basis97_inv basis97_inv' Global.DesignB.framedNode

/-- The linear moment gap of the children. -/
theorem moment₁_ranks97 :
    (ranks97.map fun r : ℕ => (1 / ((roleCount : ℕ) : ℝ)) * ((r : ℝ) / ((529 : ℕ) : ℝ))).sum ≤ q₁ := by
  have hf : (ranks97.map fun r : ℕ => (1 / ((roleCount : ℕ) : ℝ)) * ((r : ℝ) / ((529 : ℕ) : ℝ))) =
      ranks97.map fun r : ℕ => ((r : ℝ) / 529) ^ (1 : ℝ) / roleCount :=
    List.map_congr_left fun r _ => by rw [Real.rpow_one]; push_cast; ring
  rw [hf, sum_ranks97 _ (by simp)]
  exact linear_premiseB

/-- The `τ*`-moment gap of the children, at `τ* = 1 - 12402/10⁸`. -/
theorem momentτ_ranks97 :
    (ranks97.map fun r : ℕ =>
      (1 / ((roleCount : ℕ) : ℝ)) * ((r : ℝ) / ((529 : ℕ) : ℝ)) ^ (1 - (savingB : ℝ))).sum ≤ qτB := by
  have hτ : (1 - (savingB : ℝ)) ≠ 0 := by norm_num [savingB]
  have hf : (ranks97.map fun r : ℕ =>
      (1 / ((roleCount : ℕ) : ℝ)) * ((r : ℝ) / ((529 : ℕ) : ℝ)) ^ (1 - (savingB : ℝ))) =
      ranks97.map fun r : ℕ => ((r : ℝ) / 529) ^ (1 - (savingB : ℝ)) / roleCount :=
    List.map_congr_left fun r _ => by push_cast; ring
  rw [hf, sum_ranks97 _ (by rw [Nat.cast_zero, zero_div, Real.zero_rpow hτ, zero_div])]
  exact tau_premiseB.le

/-! ### The stopped bound of the reversed family -/

/-- **The stage-2 PR97 family closes.** A cost that obeys the leaf bound below `529` atoms and
the node recurrence over the children `ranks97` on `W` roles is at most
`C/(1-q₁) n + C/(1-q_τ) n^τ* L`. -/
theorem rev97_closed (T : ℕ → ℝ) {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hleaf : ∀ n, 1 ≤ n → n < 529 → T n ≤ C * L)
    (hnode : ∀ n, 529 ≤ n →
      T n ≤ (ranks97.map fun r : ℕ => T (r * (n / 529)) / roleCount).sum + C * n + C * L) :
    ∀ n, 1 ≤ n →
      T n ≤ C / (1 - q₁) * n + C / (1 - qτB) * ((n : ℝ) ^ (1 - (savingB : ℝ)) * L) :=
  RevMachine.family_closed 529 roleCount (by norm_num) (by norm_num [roleCount]) ranks97
    (fun _ => ranks97_pos) (fun _ => ranks97_lt) T (by norm_num [savingB]) hC hL
    (by exact_mod_cast q₁_lt_one) (by exact_mod_cast qτB_nonneg) (by exact_mod_cast qτB_lt_one)
    hleaf hnode moment₁_ranks97 momentτ_ranks97

/-- **The contract of the stage-2 PR97 family.** A contract monotone in its budget that holds
below `529` atoms at `C L` and passes from the block children `ranks97` to the node holds for
every atom count at `C/(1-q₁) n + C/(1-q_τ) n^τ* L`. -/
theorem rev97_contract (P : ℕ → ℝ → Prop) (mono : ∀ n B B', P n B → B ≤ B' → P n B')
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (leaf : ∀ n, 1 ≤ n → n < 529 → P n (C * L))
    (node : ∀ n, 529 ≤ n → ∀ T : ℕ → ℝ, (∀ r ∈ ranks97, P (r * (n / 529)) (T (r * (n / 529)))) →
      P n ((ranks97.map fun r : ℕ => T (r * (n / 529)) / roleCount).sum + C * n + C * L)) :
    ∀ n, 1 ≤ n →
      P n (C / (1 - q₁) * n + C / (1 - qτB) * ((n : ℝ) ^ (1 - (savingB : ℝ)) * L)) :=
  RevMachine.family_contract P mono 529 roleCount (by norm_num) (by norm_num [roleCount]) ranks97
    (fun _ => ranks97_pos) (fun _ => ranks97_lt) (by norm_num [savingB]) hC hL
    (by exact_mod_cast q₁_lt_one) (by exact_mod_cast qτB_nonneg) (by exact_mod_cast qτB_lt_one)
    moment₁_ranks97 momentτ_ranks97 leaf node

end

end IntegerMultBounds.MathlibTM2.M8
