module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpLineInitialize

/-! # Exact write footprint of retained line preparation

Finite support checks concern only the short register lists. Data, dimensions
and all input coefficients remain arbitrary in the frame theorem.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Node

def readinessTargets : List (Fin 640) :=
  [processor .wn, processor .pn, processor .nn, output.cr .wn, output.cr .pn,
    output.cr .nn, output.nr .wn, output.nr .pn, output.nr .nn]

def tableTargets : List (Fin 640) := [processor .ys, batch .srcY, output.cr .ys, output.nr .ys]

def prepareWrites : List (Fin 640) := readinessTargets ++ tableTargets ++ List.ofFn output.dim

/-- Preparation changes only the nine readiness counters, four tables and nine output controls. -/
theorem preparedStack_off (p q l Γ w t s α m M : ℕ) (S : Stacks 640 A)
    (k : Fin 640) (hk : k ∉ prepareWrites) :
    (preparedStack p q l Γ w t s α m M S).R k = S.R k := by
  have hh : k ∉ readinessTargets ∧ k ∉ tableTargets ∧ k ∉ List.ofFn output.dim := by
    simpa only [prepareWrites, List.mem_append, not_or, and_assoc] using hk
  have hr : k ≠ processor .wn ∧ k ≠ processor .pn ∧ k ≠ processor .nn ∧
      k ≠ output.cr .wn ∧ k ≠ output.cr .pn ∧ k ≠ output.cr .nn ∧
      k ≠ output.nr .wn ∧ k ≠ output.nr .pn ∧ k ≠ output.nr .nn := by
    simpa only [readinessTargets, List.mem_cons, List.not_mem_nil, or_false, not_or] using hh.1
  have ht : k ≠ processor .ys ∧ k ≠ batch .srcY ∧ k ≠ output.cr .ys ∧ k ≠ output.nr .ys := by
    simpa only [tableTargets, List.mem_cons, List.not_mem_nil, or_false, not_or] using hh.2.1
  rcases hr with ⟨hpw, hpp, hpn, hcw, hcp, hcn, hnw, hnp, hnn⟩
  change countersR p q l Γ w t (tablesR w q s t α m M Γ (readinessR q w S.R)) k = S.R k
  unfold countersR
  rw [chirpOutputDimensions_off output.dim p q l Γ w t _ k (fun i he =>
    hh.2.2 (List.mem_ofFn.mpr ⟨i, he.symm⟩))]
  rw [tables_off w q s t α m M Γ _ k ht.1 ht.2.1 ht.2.2.1 ht.2.2.2]
  exact readiness_off q w S.R k
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> assumption)
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> assumption)
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> assumption)

/-- Every binary bank survives the complete preparation stage unchanged. -/
theorem preparedStack_bank (p q l Γ w t s α m M : ℕ) (S : Stacks 640 A) (i : Fin 193) :
    (preparedStack p q l Γ w t s α m M S).R (bankTape i) = S.R (bankTape i) := by
  change countersR p q l Γ w t (tablesR w q s t α m M Γ (readinessR q w S.R)) (bankTape i) = _
  unfold countersR
  rw [chirpOutputDimensions_off output.dim p q l Γ w t _ (bankTape i) (by
    intro j h
    have hb := bank_range i
    have hd := output_dimension_range j
    have hv := congrArg Fin.val h
    omega)]
  exact arithmetic_bank w q s t α m M Γ S.R i

private theorem not_written_of_check (xs : List (Fin 640))
    (h : xs.all (fun k => !prepareWrites.contains k) = true) : ∀ k ∈ xs, k ∉ prepareWrites := by
  intro k hk hw
  have hc := List.all_eq_true.mp h k hk
  simp [hw] at hc

theorem workspace_not_written : ∀ k ∈ correlationEmpty, k ∉ prepareWrites :=
  not_written_of_check _ (by decide +kernel)

theorem dimensions_not_written (i : Fin 7) : correlationDimensions i ∉ prepareWrites := by
  fin_cases i <;> decide +kernel

theorem processor_data_not_written : ∀ r ∈ [CR.xs, .xsv, .ysv, .acc, .out], processor r ∉ prepareWrites := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem operand_not_written : batch .srcX ∉ prepareWrites := by decide +kernel

theorem wordCounter_not_written : wordCounter ∉ prepareWrites := by decide +kernel

/-- The whole written support lies below the raw input, scalar inputs and producer scratch. -/
theorem written_small : ∀ k ∈ prepareWrites, k.val < 500 := by
  have h : prepareWrites.all (fun k => decide (k.val < 500)) = true := by decide +kernel
  intro k hk
  exact of_decide_eq_true (List.all_eq_true.mp h k hk)

theorem high_not_written (k : Fin 640) (hk : 500 ≤ k.val) : k ∉ prepareWrites := by
  intro h
  have := written_small k h
  omega

theorem raw_not_written (r : ChirpRawReg) : raw r ∉ prepareWrites := by
  by_cases hr : r = .dst
  · subst r
    simpa only [raw_link] using processor_data_not_written .xs (by simp)
  · apply high_not_written
    simp only [raw, ite_eq_right hr]
    omega


theorem host_not_written (i : Fin 91) : host i ∉ prepareWrites :=
  not_written_of_check (List.ofFn host) (by decide +kernel) _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

theorem workspace_high : ∀ k ∈ correlationEmpty, 369 ≤ k.val := by
  have h : correlationEmpty.all (fun k => decide (369 ≤ k.val)) = true := by decide +kernel
  intro k hk
  exact of_decide_eq_true (List.all_eq_true.mp h k hk)

theorem dimensions_high (i : Fin 7) : 369 ≤ (correlationDimensions i).val := by
  fin_cases i <;> decide +kernel

theorem host_high (i : Fin 91) : 369 ≤ (host i).val := by
  simp only [host, Function.comp_apply, productTape]
  omega

theorem producer_high (i : Fin 11) : 500 ≤ (producer i).val := by simp [producer]; omega

theorem raw_outside_banks (r : ChirpRawReg) : (raw r).val < 176 ∨ 369 ≤ (raw r).val := by
  by_cases hr : r = .dst
  · subst r
    rw [raw_link]
    exact Or.inl (processor_range .xs).2
  · apply Or.inr
    simp only [raw, ite_eq_right hr]
    omega

/-- Compose the bank-setup and preparation frames without rechecking data-dependent execution. -/
theorem initialized_off (p q l Γ w t s α m M : ℕ) (S SB : Stacks 640 A)
    (hframe : ∀ k, k.val < 176 ∨ 369 ≤ k.val → SB.R k = S.R k)
    (k : Fin 640) (hk : k.val < 176 ∨ 369 ≤ k.val) (hw : k ∉ prepareWrites) :
    (preparedStack p q l Γ w t s α m M SB).R k = S.R k :=
  (preparedStack_off p q l Γ w t s α m M SB k hw).trans (hframe k hk)

/-- Left stacks of the shared product are retained through both initialization phases. -/
theorem preparedStack_left (p q l Γ w t s α m M : ℕ) (S : Stacks 640 A) :
    (preparedStack p q l Γ w t s α m M S).L = S.L := rfl

/-- Private product right/left stacks remain clean throughout complete initialization. -/
theorem initialized_product_clean (p q l Γ w t s α m M : ℕ) (S SB : Stacks 640 A)
    (hL : SB.L = S.L) (hframe : ∀ k, k.val < 176 ∨ 369 ≤ k.val → SB.R k = S.R k)
    (hclean : RpClean host S) :
    RpClean host (preparedStack p q l Γ w t s α m M SB) := by
  constructor
  · intro i
    simpa only [preparedStack_left, hL] using hclean.1 i
  · intro i hi
    exact (initialized_off p q l Γ w t s α m M S SB hframe _ (Or.inr (host_high i))
      (host_not_written i)).trans (hclean.2 i hi)


end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
