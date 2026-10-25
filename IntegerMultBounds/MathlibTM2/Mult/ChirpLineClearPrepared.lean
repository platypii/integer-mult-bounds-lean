module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpInitializedLine

/-! # Release retained readiness, coefficient tables and output controls

Clear the exact preparation footprint after its last line. The output tape is
outside that footprint. Every erased symbol is charged by the host execution.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 640 Q A U}

def clearPrepared : Pr P 640 Q A U := clearWords prepareWrites

def clearPreparedR (R : Regs 640 A) : Regs 640 A := fun k => if k ∈ prepareWrites then [] else R k

theorem prepareWrites_nodup : prepareWrites.Nodup := by decide +kernel

theorem output_not_written : output.nr .out ∉ prepareWrites := by decide +kernel

def clearPreparedCost (R : Regs 640 A) : ℕ :=
  2 * (prepareWrites.map fun k => (R k).length).sum + 45

/-- Cleanup charges exactly twice the retained symbol volume plus 45 control steps. -/
theorem clearPrepared_exec (v : HS 640 Q A U) (S : Stacks 640 A) :
    ∃ v', v'.user = v.user ∧
      Exec body clearPrepared (mk v S) (clearPreparedCost S.R)
        (mk v' { S with R := clearPreparedR S.R }) := by
  have he := clearWords_exec (body := body) prepareWrites prepareWrites_nodup v S
  have hlen : prepareWrites.length = 22 := by decide +kernel
  unfold clearPrepared clearPreparedCost clearPreparedR
  simpa only [hlen, Nat.add_assoc, show 2 * 22 + 1 = 45 from rfl] using he

/-- Fresh arithmetic and control banks imply freshness of the whole release support. -/
theorem prepareWrites_fresh (S : Stacks 640 A)
    (hproc : ∀ r, S.R (processor r) = [])
    (hcr : ∀ r, S.R (output.cr r) = []) (hnr : ∀ r, S.R (output.nr r) = [])
    (hK : S.R (batch .srcY) = []) (hbank : ∀ i, S.R (output.bank i) = []) :
    ∀ k ∈ prepareWrites, S.R k = [] := by
  intro k hk
  simp only [prepareWrites, List.mem_append] at hk
  rcases hk with (hr | ht) | hd
  · simp only [readinessTargets, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hproc _ | exact hcr _ | exact hnr _
  · simp only [tableTargets, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    all_goals first | exact hproc _ | exact hK | exact hcr _ | exact hnr _
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
    exact hbank (Fin.castLE (by decide) i)

/-- Raw bank initialization is disjoint from every subsequently released preparation tape. -/
theorem prepareWrites_outside : ∀ k ∈ prepareWrites, k.val < 176 ∨ 369 ≤ k.val := by
  have h : prepareWrites.all (fun k => decide (k.val < 176 ∨ 369 ≤ k.val)) = true := by decide +kernel
  intro k hk
  exact of_decide_eq_true (List.all_eq_true.mp h k hk)

/-- The raw-initialization frame preserves release-support freshness. -/
theorem prepareWrites_fresh_after_banks (S SB : Stacks 640 A)
    (hframe : ∀ k, k.val < 176 ∨ 369 ≤ k.val → SB.R k = S.R k)
    (hfresh : ∀ k ∈ prepareWrites, S.R k = []) : ∀ k ∈ prepareWrites, SB.R k = [] :=
  fun k hk => (hframe k (prepareWrites_outside k hk)).trans (hfresh k hk)

/-- The original fresh preparation support is restored while the actual forward output is kept. -/
theorem clearPrepared_lineResult (p q l Γ w t s α m M : ℕ) (SB : Stacks 640 A)
    (u : ZMod s → GaussianInt) (hblank : ∀ k ∈ prepareWrites, SB.R k = []) :
    clearPreparedR (lineResult p q l Γ w t s α m M SB u).R =
      Function.update SB.R (output.nr .out)
        (cstream A (p + l + Γ + 5) (chirpForwardOutput s t α p q l Γ m u)) := by
  funext k
  by_cases hw : k ∈ prepareWrites
  · have ho : k ≠ output.nr .out := by intro h; subst k; exact output_not_written hw
    simp only [clearPreparedR, ite_eq_left hw, Function.update_of_ne ho]
    exact (hblank k hw).symm
  · simp only [clearPreparedR, ite_eq_right hw]
    by_cases ho : k = output.nr .out
    · subst k
      simp only [lineResult, Function.update_self]
    · change Function.update (preparedStack p q l Γ w t s α m M SB).R (output.nr .out) _ k = _
      rw [Function.update_of_ne ho, Function.update_of_ne ho]
      exact preparedStack_off p q l Γ w t s α m M SB k hw

/-- Cleanup retains the returned tape, so its already proved approximation bound is unchanged. -/
theorem clearPrepared_output (R : Regs 640 A) : clearPreparedR R (output.nr .out) = R (output.nr .out) :=
  ite_eq_right output_not_written

theorem clearPrepared_readOutput (p wo t : ℕ) (S : Stacks 640 A) :
    readOutput p wo t { S with R := clearPreparedR S.R } = readOutput p wo t S := by
  funext k
  dsimp only [readOutput]
  rw [clearPrepared_output]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
