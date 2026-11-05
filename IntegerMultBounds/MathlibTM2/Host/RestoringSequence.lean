module

public import IntegerMultBounds.MathlibTM2.StackResources

/-! Sequential restored phases add time and share their peak workspace.
An invariant over the remaining schedule carries the semantic obligations. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U ι : Type}

/-- Replacing a restored output by an equal-length word preserves boundary stock. -/
theorem mn_replace_right_size_of_length (v w : HS T Q A U) (S : Stacks T A)
    (output : Fin T) (ys : List (Fin (A+4))) (hlen : ys.length = (S.R output).length) :
    mnSize (mk w {S with R := Function.update S.R output ys}) = mnSize (mk v S) := by
  have hh := mn_size_update (mk v S) w (.rt output) ys
  have hbalance : mnSize (mk w {S with R := Function.update S.R output ys})+(S.R output).length =
      mnSize (mk v S)+ys.length := by
    simpa only [mk,update_rt,get_rt] using hh
  omega

/-- A stage may consume an input prefix while replacing an equal-length output.
This is the boundary-stock premise needed by restoringSequence_exec_within. -/
theorem mn_replace_input_output_size_le (v w : HS T Q A U) (S : Stacks T A)
    (input output : Fin T) (hne : input ≠ output)
    (xs ys : List (Fin (A+4))) (hinput : xs.length ≤ (S.R input).length)
    (houtput : ys.length = (S.R output).length) :
    mnSize (mk w {S with R := (Function.update (Function.update S.R input xs) output ys)}) ≤
      mnSize (mk v S) := by
  let M : Stacks T A := {S with R := Function.update S.R input xs}
  have hbalance := mn_size_update (mk v S) w (.rt input) xs
  have hle : mnSize (mk w M) ≤ mnSize (mk v S) := by
    have hh : mnSize (mk w M)+(S.R input).length = mnSize (mk v S)+xs.length := by
      simpa only [M,mk,update_rt,get_rt] using hbalance
    omega
  have hout := mn_replace_right_size_of_length w w M output ys
    (by simpa [M,Function.update_of_ne hne.symm] using houtput)
  exact hout.le.trans hle

def restoringSequence (program : ι → Pr P T Q A U) : List ι → Pr P T Q A U
  | [] => .act .done
  | x::xs => .seq (program x) (restoringSequence program xs)

def restoringSequenceWorkspace (workspace : ι → ℕ) : List ι → ℕ
  | [] => 0
  | x::xs => max (workspace x) (restoringSequenceWorkspace workspace xs)

theorem restoringSequenceWorkspace_le (workspace : ι → ℕ) (xs : List ι) (bound : ℕ)
    (hbound : ∀ x ∈ xs, workspace x ≤ bound) : restoringSequenceWorkspace workspace xs ≤ bound := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    exact max_le (hbound x (by simp)) (ih (fun y hy => hbound y (by simp [hy])))

theorem restoringSequence_exec_within (body : P → Pr P T Q A U)
    (program : ι → Pr P T Q A U) (Inv : List ι → Stacks T A → Prop)
    (cost : ι → ℝ) (workspace : ι → ℕ) (depth : ℕ)
    (hstep : ∀ x xs (v : HS T Q A U) S, Inv (x::xs) S →
      ∃ v' F, ∃ n : ℕ, v'.user = v.user ∧ (n : ℝ) ≤ cost x ∧ Inv xs F ∧
        mnSize (mk v' F) ≤ mnSize (mk v S) ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+workspace x)
          depth (program x) (mk v S) n (mk v' F))
    (xs : List ι) (v : HS T Q A U) (S : Stacks T A) (hInv : Inv xs S) :
    ∃ v' F, ∃ n : ℕ, v'.user = v.user ∧ (n : ℝ) ≤ (xs.map cost).sum+1 ∧ Inv [] F ∧
      mnSize (mk v' F) ≤ mnSize (mk v S) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+restoringSequenceWorkspace workspace xs)
        depth (restoringSequence program xs) (mk v S) n (mk v' F) := by
  induction xs generalizing v S with
  | nil =>
    refine ⟨v,S,1,rfl,by simp,hInv,le_rfl,?_⟩
    simpa only [restoringSequence,restoringSequenceWorkspace,Action.run,Nat.add_zero] using
      ExecWithin.act (body := body) (.done : Act T Q A U) (mk v S) (by omega) (by simp only [Action.run]; omega)
  | cons x xs ih =>
    obtain ⟨v₁,M,n₁,hu₁,hn₁,hM,hs₁,he₁⟩ := hstep x xs v S hInv
    obtain ⟨v₂,F,n₂,hu₂,hn₂,hF,hs₂,he₂⟩ := ih v₁ M hM
    refine ⟨v₂,F,n₁+n₂,hu₂.trans hu₁,?_,hF,hs₂.trans hs₁,?_⟩
    · simp only [Nat.cast_add,List.map_cons,List.sum_cons]
      linarith only [hn₁,hn₂]
    · have hleft := Nat.le_max_left (workspace x) (restoringSequenceWorkspace workspace xs)
      have hright := Nat.le_max_right (workspace x) (restoringSequenceWorkspace workspace xs)
      exact .seq (he₁.mono (by intro d z hz; change mnSize z+d ≤ mnSize (mk v S)+depth+max _ _; omega))
        (he₂.mono (by intro d z hz; change mnSize z+d ≤ mnSize (mk v S)+depth+max _ _; omega))

/-- Uniform natural-number bills specialize the structural executor without
reproving its induction or accumulating workspace across restored phases. -/
theorem restoringSequence_exec_uniform (body : P → Pr P T Q A U)
    (program : ι → Pr P T Q A U) (Inv : List ι → Stacks T A → Prop)
    (cost workspace depth : ℕ)
    (hstep : ∀ x xs (v : HS T Q A U) S, Inv (x::xs) S →
      ∃ v' F, ∃ n : ℕ, v'.user = v.user ∧ n ≤ cost ∧ Inv xs F ∧
        mnSize (mk v' F) ≤ mnSize (mk v S) ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+workspace)
          depth (program x) (mk v S) n (mk v' F))
    (xs : List ι) (v : HS T Q A U) (S : Stacks T A) (hInv : Inv xs S) :
    ∃ v' F, ∃ n : ℕ, v'.user = v.user ∧ n ≤ xs.length*cost+1 ∧ Inv [] F ∧
      mnSize (mk v' F) ≤ mnSize (mk v S) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+workspace)
        depth (restoringSequence program xs) (mk v S) n (mk v' F) := by
  have hreal : ∀ x rest (u : HS T Q A U) M, Inv (x::rest) M →
      ∃ u' F, ∃ n : ℕ, u'.user = u.user ∧ (n : ℝ) ≤ (cost : ℝ) ∧ Inv rest F ∧
        mnSize (mk u' F) ≤ mnSize (mk u M) ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk u M)+depth+workspace)
          depth (program x) (mk u M) n (mk u' F) := by
    intro x rest u M hI
    obtain ⟨u',F,n,hu,hn,hF,hs,he⟩ := hstep x rest u M hI
    exact ⟨u',F,n,hu,(show (n : ℝ) ≤ (cost : ℝ) by exact_mod_cast hn),hF,hs,he⟩
  obtain ⟨v',F,n,hu,hn,hF,hs,he⟩ := restoringSequence_exec_within body program Inv
    (fun _ => (cost : ℝ)) (fun _ => workspace) depth hreal xs v S hInv
  have hsum : (xs.map (fun _ => (cost : ℝ))).sum = xs.length*cost := by
    simp [List.map_const',List.sum_replicate,nsmul_eq_mul]
  rw [hsum] at hn
  have hworkspace := restoringSequenceWorkspace_le (fun _ : ι => workspace) xs workspace
    (fun _ _ => le_rfl)
  refine ⟨v',F,n,hu,by exact_mod_cast hn,hF,hs,?_⟩
  exact he.mono (by intro d z hz; omega)

end IntegerMultBounds.MathlibTM2.Host
