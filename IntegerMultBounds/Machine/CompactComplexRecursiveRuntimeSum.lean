import IntegerMultBounds.Networks.ComplexRecursiveCallSchema
import IntegerMultBounds.Machine.CompactComplexRecursiveGeometry
import IntegerMultBounds.Swap.Recurrence
import Mathlib.Data.Nat.Cast.Order.Field

/-! Structural runtime sums for the actual complex25 call schema. The recurrence
charges each literal child occurrence once, at the role-volume quotient. Its
analytic bound separates stopped-leaf cost from local interchange cost. This
is a budget theorem: constructing an execution satisfying the local contracts
and the recursive child contracts remains a distinct obligation. -/
namespace IntegerMultBounds.Machine.CompactComplexRecursiveRuntimeSum
noncomputable section
open Networks
open CompactComplexRecursiveGeometry (arity)

/-- The number of permanent complex roles, fixed by the actual finite motif. -/
def roles : ℕ := 58645352620000

/-- The actual recursive multiplicity; repeated sites are charged separately. -/
abbrev children : ℕ := ComplexRank25.rankSum

attribute [local irreducible] ComplexRecursiveCallSchema.calls ComplexRank25.rankSum

/-- A leaf allowance and an explicit per-depth local coefficient determine the
natural budget. Neither the desired total nor an execution oracle occurs here. -/
def budget (leaf : ℕ) (localCost : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, V => leaf * V
  | depth+1, V => localCost depth * V + children * budget leaf localCost depth (V/roles)

private theorem constant_sum {α : Type*} (xs : List α) (n : ℕ) :
    (xs.map (fun _ => n)).sum = xs.length*n := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih]; ring

/-- The coefficient recurrence is exactly the sum over original call occurrences,
not the number of distinct labels or a supplied branching bound. -/
theorem budget_succ_calls (leaf : ℕ) (localCost : ℕ → ℕ) (depth V : ℕ) :
    budget leaf localCost (depth+1) V = localCost depth*V +
      (ComplexRecursiveCallSchema.calls.map
        (fun _ => budget leaf localCost depth (V/roles))).sum := by
  rw [constant_sum,ComplexRecursiveCallSchema.calls_rankSum]
  rfl

/-- Normalized real recurrence, with natural quotient rounding removed upwards. -/
def normalized (leaf : ℕ) (localCost : ℕ → ℕ) : ℕ → ℝ
  | 0 => leaf
  | depth+1 => (children : ℝ)/roles*normalized leaf localCost depth+localCost depth

theorem normalized_nonneg (leaf : ℕ) (localCost : ℕ → ℕ) (depth : ℕ) :
    0 ≤ normalized leaf localCost depth := by
  induction depth with
  | zero => exact Nat.cast_nonneg _
  | succ depth ih =>
    exact add_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ih)
      (Nat.cast_nonneg _)

/-- Every child quotient, including nondivisible and zero volumes, decreases the
real upper bound. -/
theorem budget_le_normalized (leaf : ℕ) (localCost : ℕ → ℕ) (depth V : ℕ) :
    (budget leaf localCost depth V : ℝ) ≤ normalized leaf localCost depth*V := by
  induction depth generalizing V with
  | zero => simp only [budget,normalized,Nat.cast_mul]; exact le_rfl
  | succ depth ih =>
    have hdiv : ((V/roles : ℕ) : ℝ) ≤ (V : ℝ)/roles := Nat.cast_div_le
    calc
      (budget leaf localCost (depth+1) V : ℝ) =
          (localCost depth : ℝ)*V+children*(budget leaf localCost depth (V/roles) : ℝ) := by
        simp only [budget,Nat.cast_add,Nat.cast_mul]
      _ ≤ (localCost depth : ℝ)*V+
          children*(normalized leaf localCost depth*((V/roles : ℕ) : ℝ)) := by
        gcongr
        exact ih _
      _ ≤ (localCost depth : ℝ)*V+
          children*(normalized leaf localCost depth*((V : ℝ)/roles)) := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hdiv (normalized_nonneg leaf localCost depth))
          (Nat.cast_nonneg _))
      _ = normalized leaf localCost (depth+1)*V := by rw [normalized]; ring

/-- Fixed certified branching saving, derived from the actual rank sum. -/
theorem branching_bound : (children : ℝ)/roles < (arity : ℝ)^Parameters.sigma := by
  exact ComplexRank25.branching_bound

theorem exponents : 0 < Parameters.tau ∧ Parameters.tau ≤ Parameters.sigma ∧
    Parameters.sigma < 1 := by
  norm_num [Parameters.tau,Parameters.sigma]

/-- Absorb local geometric costs using the strict branching slack. Unlike a
constant forcing recurrence, this handles actual width-dependent local costs. -/
theorem geometric_forcing {F : ℕ → ℝ} {a x B C : ℝ}
    (ha : 0≤a) (hax : a<x) (hB : 0≤B) (hC : 0≤C)
    (hbase : F 0≤B) (hstep : ∀ d, F (d+1)≤a*F d+C*x^(d+1)) :
    ∀ d, F d≤(B+C*x/(x-a))*x^d := by
  have hx : 0<x := lt_of_le_of_lt ha hax
  have hgap : 0<x-a := sub_pos.mpr hax
  have hcoef : a*(B+C*x/(x-a))+C*x≤(B+C*x/(x-a))*x := by
    have hcancel : C*x/(x-a)*(x-a)=C*x := div_mul_cancel₀ _ hgap.ne'
    have hBa : a*B≤x*B := mul_le_mul_of_nonneg_right hax.le hB
    nlinarith
  intro d
  induction d with
  | zero => simpa only [pow_zero,mul_one] using
      hbase.trans (le_add_of_nonneg_right (div_nonneg (mul_nonneg hC hx.le) hgap.le))
  | succ d ih =>
    calc
      F (d+1) ≤ a*F d+C*x^(d+1) := hstep d
      _ ≤ a*((B+C*x/(x-a))*x^d)+C*x^(d+1) := by gcongr
      _ = (a*(B+C*x/(x-a))+C*x)*x^d := by rw [pow_succ]; ring
      _ ≤ ((B+C*x/(x-a))*x)*x^d :=
        mul_le_mul_of_nonneg_right hcoef (pow_nonneg hx.le _)
      _ = (B+C*x/(x-a))*x^(d+1) := by rw [pow_succ]; ring

/-- Fixed analytic constant for local costs, independent of recursion depth,
leaf width and payload volume. -/
def localConstant : ℝ := (arity : ℝ)^Parameters.sigma /
    ((arity : ℝ)^Parameters.sigma-(children : ℝ)/roles)

theorem localConstant_positive : 0<localConstant := by
  exact div_pos (Real.rpow_pos_of_pos (by norm_num [arity]) _)
    (sub_pos.mpr branching_bound)

/-- Local costs paid at the interchange exponent can be summed over every
recursive level. The leaf coefficient is retained separately. -/
theorem normalized_bound (leaf : ℕ) (localCost : ℕ → ℕ) (leafExponent : ℕ)
    {C : ℝ} (hC : 0≤C)
    (hlocal : ∀ d, (localCost d : ℝ) ≤
      C*((arity^(leafExponent+d+1) : ℕ) : ℝ)^Parameters.tau) (depth : ℕ) :
    normalized leaf localCost depth ≤
      ((leaf : ℝ)+C*((arity^leafExponent : ℕ) : ℝ)^Parameters.tau*localConstant)*
        ((arity^depth : ℕ) : ℝ)^Parameters.sigma := by
  have hwidth (d : ℕ) :
      ((arity^(leafExponent+d+1) : ℕ) : ℝ)^Parameters.tau ≤
      ((arity^leafExponent : ℕ) : ℝ)^Parameters.tau*
        ((arity : ℝ)^Parameters.sigma)^(d+1) := by
    rw [show leafExponent+d+1=leafExponent+(d+1) by omega,pow_add,Nat.cast_mul,
      Real.mul_rpow (by positivity) (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [← Swap.Recurrence.rpow_pow_eq]
    apply pow_le_pow_left₀ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num [arity]) exponents.2.1
  have h := geometric_forcing
    (F:=normalized leaf localCost) (a:=(children : ℝ)/roles)
    (x:=(arity : ℝ)^Parameters.sigma) (B:=(leaf : ℝ))
    (C:=C*((arity^leafExponent : ℕ) : ℝ)^Parameters.tau)
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) branching_bound
    (Nat.cast_nonneg _) (mul_nonneg hC (by positivity)) le_rfl
    (fun d => by
      have hd := (hlocal d).trans (mul_le_mul_of_nonneg_left (hwidth d) hC)
      simpa only [normalized,mul_assoc] using add_le_add_right hd
        ((children : ℝ)/roles*normalized leaf localCost d)) depth
  rw [Swap.Recurrence.rpow_pow_eq] at h
  simpa only [localConstant,mul_div_assoc] using h

/-- Original-volume recursive bound, with distinct stopped-leaf and local cost
terms. The local premise is per-node arithmetic; it is not a desired total. -/
theorem budget_bound (leaf : ℕ) (localCost : ℕ → ℕ) (leafExponent depth V : ℕ)
    {C : ℝ} (hC : 0≤C)
    (hlocal : ∀ d, (localCost d : ℝ) ≤
      C*((arity^(leafExponent+d+1) : ℕ) : ℝ)^Parameters.tau) :
    (budget leaf localCost depth V : ℝ) ≤
      ((leaf : ℝ)+C*((arity^leafExponent : ℕ) : ℝ)^Parameters.tau*localConstant)*
        (V : ℝ)*((arity^depth : ℕ) : ℝ)^Parameters.sigma := by
  calc
    (budget leaf localCost depth V : ℝ) ≤ normalized leaf localCost depth*V :=
      budget_le_normalized leaf localCost depth V
    _ ≤ (((leaf : ℝ)+C*((arity^leafExponent : ℕ) : ℝ)^Parameters.tau*localConstant)*
        ((arity^depth : ℕ) : ℝ)^Parameters.sigma)*V :=
      mul_le_mul_of_nonneg_right
        (normalized_bound leaf localCost leafExponent hC hlocal depth) (Nat.cast_nonneg _)
    _ = _ := by ring

/-- A complete stopped-call coefficient linear in the actual remaining child
width gives the separate leaf and internal terms of the original cost sum. -/
theorem stopped_budget_bound (leaf : ℕ) (localCost : ℕ → ℕ)
    (leafExponent depth V : ℕ) {B C : ℝ} (hC : 0≤C)
    (hleaf : (leaf : ℝ) ≤ B*(arity^leafExponent : ℕ))
    (hlocal : ∀ d, (localCost d : ℝ) ≤
      C*((arity^(leafExponent+d+1) : ℕ) : ℝ)^Parameters.tau) :
    (budget leaf localCost depth V : ℝ) ≤
      (B*(arity^leafExponent : ℕ)+
        C*((arity^leafExponent : ℕ) : ℝ)^Parameters.tau*localConstant)*
        (V : ℝ)*((arity^depth : ℕ) : ℝ)^Parameters.sigma := by
  apply (budget_bound leaf localCost leafExponent depth V hC hlocal).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  exact add_le_add hleaf le_rfl


/-- Express the sum in the original uncontracted width. The coefficient displays
exactly the leaf factor `leafWidth^(1-sigma)` and the local factor
`leafWidth^(tau-sigma)` without requiring a stopped-threshold hypothesis. -/
theorem original_width_bound (leaf : ℕ) (localCost : ℕ → ℕ)
    (leafExponent depth V : ℕ) {B C : ℝ} (hC : 0≤C)
    (hleaf : (leaf : ℝ) ≤ B*(arity^leafExponent : ℕ))
    (hlocal : ∀ d, (localCost d : ℝ) ≤
      C*((arity^(leafExponent+d+1) : ℕ) : ℝ)^Parameters.tau) :
    (budget leaf localCost depth V : ℝ) ≤
      ((B*(arity^leafExponent : ℕ)+
        C*((arity^leafExponent : ℕ) : ℝ)^Parameters.tau*localConstant)/
        ((arity^leafExponent : ℕ) : ℝ)^Parameters.sigma)*
        (V : ℝ)*((arity^(leafExponent+depth) : ℕ) : ℝ)^Parameters.sigma := by
  have hp : 0<((arity^leafExponent : ℕ) : ℝ)^Parameters.sigma := by
    apply Real.rpow_pos_of_pos
    exact_mod_cast (pow_pos (by decide : 0<arity) leafExponent)
  have hw : ((arity^(leafExponent+depth) : ℕ) : ℝ)^Parameters.sigma =
      ((arity^leafExponent : ℕ) : ℝ)^Parameters.sigma*
        ((arity^depth : ℕ) : ℝ)^Parameters.sigma := by
    rw [pow_add,Nat.cast_mul,Real.mul_rpow (by positivity) (by positivity)]
  have h := stopped_budget_bound leaf localCost leafExponent depth V hC hleaf hlocal
  rw [hw]
  convert h using 1; field_simp

/-- Independently bounded actual child runtimes sum to exactly the recurrence
coefficient. This exposes the local induction obligation without postulating
an already bounded complete recursive execution. -/
theorem child_sum_le (cost : ComplexRecursiveCallSchema.Call → ℕ)
    (leaf : ℕ) (localCost : ℕ → ℕ) (depth V : ℕ)
    (hchild : ∀ call ∈ ComplexRecursiveCallSchema.calls,
      cost call ≤ budget leaf localCost depth (V/roles)) :
    (ComplexRecursiveCallSchema.calls.map cost).sum ≤
      children*budget leaf localCost depth (V/roles) := by
  have hs : ∀ (xs : List ComplexRecursiveCallSchema.Call),
      (∀ call ∈ xs, cost call ≤ budget leaf localCost depth (V/roles)) →
      (xs.map cost).sum ≤ xs.length*budget leaf localCost depth (V/roles) := by
    intro xs
    induction xs with
    | nil => simp
    | cons call xs ih =>
      intro hx
      have hc := hx call (List.mem_cons_self ..)
      have ht := ih (fun c hm => hx c (List.mem_cons_of_mem _ hm))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      calc
        cost call+(xs.map cost).sum ≤
            budget leaf localCost depth (V/roles)+xs.length*budget leaf localCost depth (V/roles) :=
          Nat.add_le_add hc ht
        _ = _ := by ring
  simpa only [ComplexRecursiveCallSchema.calls_rankSum] using
    hs ComplexRecursiveCallSchema.calls hchild

end
end IntegerMultBounds.Machine.CompactComplexRecursiveRuntimeSum
