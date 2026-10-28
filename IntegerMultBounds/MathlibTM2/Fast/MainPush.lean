module

public import IntegerMultBounds.MathlibTM2.Fast.MainProg
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Stack sizes along an execution, the cleanup and the reset

`mnSize s` is the total number of symbols on the stacks of a store. One run of an action pushes
at most `mnActPush a` symbols (`mn_act_size`), so an execution of `m` steps whose actions and
procedure bodies push at most `c` symbols each ends with at most `mnSize s + c m` symbols
(`mn_exec_size`): every executed action costs one step. `mnPushC body` bounds the push count of
every procedure body (`mn_progPush_le_pushC`). On host stores the registers hold at most
`mnSize` symbols (`mn_sumR_le_size`).

`mn_clear_exec`: the cleanup `mnClear` empties every register in
`2 ∑ |R i| + 2 mnT + 1` steps. `mn_reset_exec`: `mnReset` sets the local state to `mnV₀` in one
step.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast


/-! ### The cleanup and the reset -/

section ClearGen

variable {T Q A : ℕ} {U P : Type}

/-- Emptying the registers of a nodup list `l`, in `∑ (2 |R i| + 2) + 1` steps. -/
theorem mn_clearList_exec (body : P → Pr P T Q A U) :
    ∀ (l : List (Fin T)), l.Nodup → ∀ (v : HS T Q A U) (S : Stacks T A),
      ∃ v', Exec body (Prog.seqList (l.map emptyR)) (mk v S)
        ((l.map fun i => 2 * (S.R i).length + 2).sum + 1)
        (mk v' { S with R := fun k => if k ∈ l then [] else S.R k })
  | [], _, v, S => by
      refine ⟨v, Exec.cast (Exec.act (body := body) .done (mk v S)) (by simp) ?_⟩
      rfl
  | i :: l, hnd, v, S => by
      rw [List.nodup_cons] at hnd
      obtain ⟨v₁, -, he₁⟩ := emptyR_exec body i v S
      obtain ⟨v₂, he₂⟩ := mn_clearList_exec body l hnd.2 v₁
        { S with R := Function.update S.R i [] }
      refine ⟨v₂, Exec.cast (Exec.seq he₁ he₂) ?_ ?_⟩
      · have e : (l.map fun j => 2 * (Function.update S.R i [] j).length + 2) =
            l.map fun j => 2 * (S.R j).length + 2 := by
          refine List.map_congr_left fun j hj => ?_
          rw [Function.update_of_ne (fun h => hnd.1 (by rw [← h]; exact hj))]
        simp only [List.map_cons, List.sum_cons]
        rw [e]
        ring
      · congr 2
        funext k
        by_cases hk : k = i
        · subst hk; simp
        · simp [hk]

/-- Emptying every register, in `2 ∑ |R i| + 2 T + 1` steps. -/
theorem mn_clearAll_exec (body : P → Pr P T Q A U) (v : HS T Q A U) (S : Stacks T A) :
    ∃ v', Exec body (Prog.seqList ((List.finRange T).map emptyR)) (mk v S)
      (2 * ∑ i, (S.R i).length + 2 * T + 1) (mk v' { S with R := fun _ => [] }) := by
  obtain ⟨v', he⟩ := mn_clearList_exec body (List.finRange T) (List.nodup_finRange T) v S
  have e1 : ((List.finRange T).map fun i => 2 * (S.R i).length + 2).sum =
      2 * ∑ i, (S.R i).length + 2 * T := by
    rw [← Fin.sum_univ_def, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm T 2]
  have e2 : (fun k => if k ∈ List.finRange T then [] else S.R k) =
      fun _ => ([] : List (Fin (A + 4))) := by
    funext k
    exact ite_eq_left (List.mem_finRange k)
  rw [e1, e2] at he
  exact ⟨v', he⟩

end ClearGen

section Clear

variable {A : ℕ}

attribute [local irreducible] mnT mnQ

/-- **The cleanup** empties every register in `2 ∑ |R i| + 2 mnT + 1` steps. -/
theorem mn_clear_exec (body : MnProc → MnPr A) (v : HS mnT mnQ A Unit) (S : Stacks mnT A) :
    ∃ v', Exec body mnClear (mk v S) (2 * ∑ i, (S.R i).length + 2 * mnT + 1)
      (mk v' { S with R := fun _ => [] }) := by
  unfold mnClear
  exact mn_clearAll_exec body v S

/-- **The reset** sets the local state to `mnV₀` in one step. -/
theorem mn_reset_exec (body : MnProc → MnPr A) (v : HS mnT mnQ A Unit) (S : Stacks mnT A) :
    Exec body mnReset (mk v S) 1 (mk mnV₀ S) :=
  Exec.act (body := body) _ (mk v S)

end Clear

end IntegerMultBounds.MathlibTM2.Fast.Main
