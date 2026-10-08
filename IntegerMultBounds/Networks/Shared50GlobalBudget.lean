import IntegerMultBounds.Networks.NetworkBudget
import IntegerMultBounds.Networks.Shared50Certificate
import IntegerMultBounds.Shared50Parameters

/-! Terminal labels and dimensions for the optimized padded two-bank world.
`GlobalCircuit.World` has three auxiliary banks and would have 601952597120000
roles here. The smaller 406321422080000 budget instead uses two auxiliary banks,
as in stage-reuse-note.tex and paired-construction.tex: stages 1 and 3 share a
bank while stage 2 remains separate. The certified local roles embed into each
padded side bank. Constructing that reused global schedule, its frame joins and
its loss estimate remains separate; all trace premises below are explicit. -/

namespace IntegerMultBounds.Networks.Shared50GlobalBudget

noncomputable section

open Module

attribute [local irreducible] SharedPointExecution.code SharedPointReplay.circuit

abbrev Base := Fin 50 → ℚ
abbrev Triple := NeighborCounts.Triple 50
abbrev Address := GlobalCircuit.Address Triple
abbrev Side := Fin 509194
abbrev Control := Fin 50
abbrev Invocation := Fin 2 × Triple × Triple
abbrev Scratch := Invocation × (Side ⊕ Control)
abbrev World := Address ⊕ Address ⊕ Scratch
abbrev Ambient := StageLabels.Ambient ℚ Base

def form : LinearMap.BilinForm ℚ Base := Labels.rational 50

def vector (T : Triple) : Base := Labels.indicator T.val

def cubeForm : LinearMap.BilinForm ℚ Ambient :=
  TensorSubspace.form form (TensorSubspace.form form form)

/-- Padding preserves every actual locally allocated role as a distinct slot. -/
def sideRoleEmbedding : Fin SharedPointExecution.code.state.next ↪ Side :=
  Fin.castLEEmb Shared50Certificate.role_bound

theorem form_nondegenerate : form.Nondegenerate :=
  Labels.rational_nondegenerate (by decide : 50 ≠ 9)

theorem vector_self (T : Triple) : form (vector T) (vector T) = 2 :=
  Labels.rational_self T.val T.property

theorem vector_self_ne_zero (T : Triple) : form (vector T) (vector T) ≠ 0 := by
  rw [vector_self]
  norm_num

theorem base_finrank : finrank ℚ Base = 50 := by simp [Base]

theorem ambient_finrank : finrank ℚ Ambient = 125000 := by
  rw [NetworkBudget.ambient_finrank (K := ℚ) (F := Base), base_finrank]
  exact Shared50Parameters.arity_count

theorem triple_card : Fintype.card Triple = 19600 := by
  rw [NeighborCounts.triple_card]
  exact Shared50Parameters.dimension_count

theorem address_card : Fintype.card Address = 7529536000000 := by
  simp only [Address, GlobalCircuit.Address, Fintype.card_prod, triple_card]

theorem invocation_card : Fintype.card Invocation = 768320000 := by
  simp only [Invocation, Fintype.card_prod, Fintype.card_fin, triple_card]

theorem scratch_card : Fintype.card Scratch = 391262350080000 := by
  simp only [Scratch, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, triple_card]

theorem world_card : Fintype.card World = 406321422080000 := by
  simp only [World, Fintype.card_sum, address_card, scratch_card]

theorem world_card_eq_W : Fintype.card World = Shared50Parameters.W := by
  rw [world_card, Shared50Parameters.wire_count]

/-- The existing unreused type really has a different cardinality. -/
theorem unreused_world_card : Fintype.card (GlobalCircuit.World Triple Side Control) =
    601952597120000 := by
  simp only [GlobalCircuit.World, GlobalCircuit.Address, GlobalCircuit.Invocation,
    Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, triple_card]

/-- Exactly the X bank starts on its tensor lines. -/
def source : World → Submodule ℚ Ambient :=
  Sum.elim (GlobalLabels.terminal (K := ℚ) vector) (Sum.elim (fun _ => ⊥) (fun _ => ⊥))

/-- Y ends in the orthogonal terminal complement; every other sink is full. -/
def sink : World → Submodule ℚ Ambient :=
  Sum.elim (fun _ => ⊤)
    (Sum.elim (fun b => cubeForm.orthogonal (GlobalLabels.terminal (K := ℚ) vector b)) (fun _ => ⊤))

def sourceTotal : ℕ := RankTrace.total (fun U : Submodule ℚ Ambient => finrank ℚ U) source

def sinkTotal : ℕ := RankTrace.total (fun U : Submodule ℚ Ambient => finrank ℚ U) sink

theorem terminal_finrank (b : Address) : finrank ℚ (GlobalLabels.terminal (K := ℚ) vector b) = 1 :=
  NetworkBudget.terminal_finrank form vector vector_self_ne_zero b

theorem complement_finrank (b : Address) :
    finrank ℚ (cubeForm.orthogonal (GlobalLabels.terminal (K := ℚ) vector b)) = 124999 := by
  have hh := NetworkBudget.complement_finrank form form_nondegenerate vector vector_self_ne_zero b
  rwa [base_finrank] at hh

private theorem source_total_aux {B S : Type*} [Fintype B] [Fintype S]
    (t : B → Base) (ht : ∀ b, form (t b) (t b) ≠ 0) :
    RankTrace.total (fun U : Submodule ℚ Ambient => finrank ℚ U)
      (Sum.elim (GlobalLabels.terminal (K := ℚ) t) (Sum.elim (fun _ => ⊥) (fun _ => ⊥)) :
        GlobalCircuit.Address B ⊕ GlobalCircuit.Address B ⊕ S → Submodule ℚ Ambient) =
      Fintype.card B ^ 3 := by
  have hp (i : GlobalCircuit.Address B ⊕ GlobalCircuit.Address B ⊕ S) :
      finrank ℚ ((Sum.elim (GlobalLabels.terminal (K := ℚ) t)
        (Sum.elim (fun _ => ⊥) (fun _ => ⊥))) i) =
      Sum.elim (fun _ => 1) (Sum.elim (fun _ => 0) (fun _ => 0)) i := by
    rcases i with x | y | z
    · exact NetworkBudget.terminal_finrank form t ht x
    · exact _root_.finrank_bot ℚ _
    · exact _root_.finrank_bot ℚ _
  unfold RankTrace.total
  simp_rw [hp]
  simp [GlobalCircuit.Address, pow_succ]
  ring

private theorem sink_total_aux {B S : Type*} [Fintype B] [Fintype S]
    (t : B → Base) (ht : ∀ b, form (t b) (t b) ≠ 0) :
    RankTrace.total (fun U : Submodule ℚ Ambient => finrank ℚ U)
      (Sum.elim (fun _ => ⊤)
        (Sum.elim (fun b => cubeForm.orthogonal (GlobalLabels.terminal (K := ℚ) t b)) (fun _ => ⊤)) :
        GlobalCircuit.Address B ⊕ GlobalCircuit.Address B ⊕ S → Submodule ℚ Ambient) +
      Fintype.card B ^ 3 = (2 * Fintype.card B ^ 3 + Fintype.card S) * 125000 := by
  have hp (i : GlobalCircuit.Address B ⊕ GlobalCircuit.Address B ⊕ S) :
      finrank ℚ ((Sum.elim (fun _ => ⊤)
        (Sum.elim (fun b => cubeForm.orthogonal (GlobalLabels.terminal (K := ℚ) t b)) (fun _ => ⊤))) i) =
      Sum.elim (fun _ => 125000) (Sum.elim (fun _ => 124999) (fun _ => 125000)) i := by
    rcases i with x | y | z
    · change finrank ℚ (⊤ : Submodule ℚ Ambient) = _
      rw [_root_.finrank_top, ambient_finrank]
      rfl
    · have hh := NetworkBudget.complement_finrank form form_nondegenerate t ht y
      rwa [base_finrank] at hh
    · change finrank ℚ (⊤ : Submodule ℚ Ambient) = _
      rw [_root_.finrank_top, ambient_finrank]
      rfl
  unfold RankTrace.total
  simp_rw [hp]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, GlobalCircuit.Address, Fintype.card_prod]
  ring

/-- The actual selected source subspaces have this total dimension. -/
theorem source_total : sourceTotal = 7529536000000 := by
  have hh := source_total_aux (S := Scratch) vector vector_self_ne_zero
  rw [triple_card] at hh
  exact hh

theorem source_total_eq_N : sourceTotal = Shared50Parameters.N := by
  rw [source_total, Shared50Parameters.source_count]

private theorem sink_arithmetic (total b scratch : ℕ)
    (hh : total + b ^ 3 = (2 * b ^ 3 + scratch) * 125000)
    (hb : b = 19600) (hs : scratch = 391262350080000) :
    total + 7529536000000 = 406321422080000 * 125000 := by
  subst b
  subst scratch
  norm_num at hh ⊢
  exact hh

/-- Sink accounting includes the full padded banks and every genuine terminal
complement. It does not assume that a global schedule realizes those labels. -/
theorem sink_total : sinkTotal + 7529536000000 = 406321422080000 * 125000 := by
  have hh := sink_arithmetic _ _ _ (sink_total_aux (S := Scratch) vector vector_self_ne_zero)
    triple_card scratch_card
  have hs : sinkTotal = RankTrace.total (fun U : Submodule ℚ Ambient => finrank ℚ U)
      (Sum.elim (fun _ => ⊤)
        (Sum.elim (fun b => cubeForm.orthogonal (GlobalLabels.terminal (K := ℚ) vector b)) (fun _ => ⊤)) :
        GlobalCircuit.Address Triple ⊕ GlobalCircuit.Address Triple ⊕ Scratch → Submodule ℚ Ambient) := rfl
  exact (congrArg (fun total => total + 7529536000000) hs).trans hh

theorem sink_total_eq_Wm : sinkTotal + Shared50Parameters.N =
    Shared50Parameters.W * Shared50Parameters.m := by
  rw [Shared50Parameters.source_count, Shared50Parameters.wire_count]
  exact sink_total

/-- Endpoint dimensions translate a genuine ordinary projection-rank balance
into the two-source-dimension arithmetic needed by the rational correction. -/
theorem balance_dimensions (ordinaryRank loss : ℕ)
    (hb : ordinaryRank + sourceTotal = sinkTotal + 2 * loss) :
    ordinaryRank + Shared50Parameters.N + Shared50Parameters.N =
      Shared50Parameters.W * Shared50Parameters.m + 2 * loss := by
  have hs := sink_total_eq_Wm
  rw [source_total_eq_N] at hb
  omega

/-- Conditional arithmetic only: the reused trace and its loss bound must still
be proved. The rational negative-source correction is the extra source total. -/
theorem corrected_rank_budget (ordinaryRank loss : ℕ)
    (hb : ordinaryRank + sourceTotal = sinkTotal + 2 * loss)
    (hl : loss ≤ Shared50Parameters.L) : ordinaryRank + sourceTotal ≤ Shared50Parameters.s := by
  have hh := NetworkBudget.shear_budget (balance_dimensions ordinaryRank loss hb) hl
  rw [source_total_eq_N, Shared50Parameters.rank_formula]
  exact hh

theorem branching_of_balance (ordinaryRank loss : ℕ)
    (hb : ordinaryRank + sourceTotal = sinkTotal + 2 * loss)
    (hl : loss ≤ Shared50Parameters.L) :
    ((ordinaryRank + sourceTotal : ℕ) : ℝ) / Shared50Parameters.W <
      (Shared50Parameters.m : ℝ) ^ Parameters.tau :=
  Shared50Parameters.branching_of_rank_le _ (corrected_rank_budget ordinaryRank loss hb hl)

/-- A concrete signed-rank trace can use the bound once its source correction,
ordinary balance and loss estimate have all been established. -/
theorem branching_of_trace_bounds (ordinaryRank signedRank loss : ℕ)
    (hb : ordinaryRank + sourceTotal = sinkTotal + 2 * loss)
    (hl : loss ≤ Shared50Parameters.L) (hc : signedRank ≤ ordinaryRank + sourceTotal) :
    (signedRank : ℝ) / Shared50Parameters.W < (Shared50Parameters.m : ℝ) ^ Parameters.tau :=
  Shared50Parameters.branching_of_rank_le _ (hc.trans (corrected_rank_budget ordinaryRank loss hb hl))

end
end IntegerMultBounds.Networks.Shared50GlobalBudget
