module

public import IntegerMultBounds.MathlibTM2.StackResources
public import IntegerMultBounds.MathlibTM2.Host.StackLoops
public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! Return both stacks of each reverse shear work tape to the empty state. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.MathlibTM2.Stack Host
variable {T Q A : ℕ} {P U : Type}

open IntegerMultBounds.MathlibTM2.Fast.Main

private theorem action_stack_length {K σ : Type} {Γ : K → Type} [DecidableEq K]
    (a : Action Γ σ) (s : Store Γ σ) (j : K) :
    ((a.run s).stk j).length ≤ (s.stk j).length + mnActPush a := by
  induction a generalizing s with
  | done => simp [Action.run,mnActPush]
  | push k f a ih =>
    have bound := ih ⟨s.var,Function.update s.stk k (f s.var :: s.stk k)⟩
    apply bound.trans
    by_cases eq : j = k
    · subst j; simp [mnActPush]; omega
    · simp [mnActPush,Function.update_of_ne eq]
  | pop k f a ih =>
    have bound := ih ⟨f s.var (s.stk k).head?,Function.update s.stk k (s.stk k).tail⟩
    apply bound.trans
    by_cases eq : j = k
    · subst j; simp [mnActPush]
    · simp [mnActPush,Function.update_of_ne eq]
  | peek k f a ih => exact ih _
  | load f a ih => exact ih _
  | branch f a b iha ihb =>
    simp only [Action.run,mnActPush]
    split
    · exact (iha s).trans (Nat.add_le_add_left (le_max_left ..) _)
    · exact (ihb s).trans (Nat.add_le_add_left (le_max_right ..) _)

theorem exec_stack_length {K σ : Type} {Γ : K → Type} [DecidableEq K]
    {body : P → Prog P Γ σ} {p : Prog P Γ σ} {s t : Store Γ σ} {n c : ℕ}
    (run : Exec body p s n t) (hp : mnProgPush p ≤ c) (hb : ∀ f, mnProgPush (body f) ≤ c) (j : K) :
    (t.stk j).length ≤ (s.stk j).length + c*n := by
  induction run with
  | act a s => exact (action_stack_length a s j).trans (by simpa [mnProgPush] using Nat.add_le_add_left hp (s.stk j).length)
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨h₁,h₂⟩ := max_le_iff.mp hp
    have := ih₁ h₁
    have := ih₂ h₂
    rw [Nat.mul_add]; omega
  | cond_true _ _ ih => have := ih (max_le_iff.mp hp).1; nlinarith
  | cond_false _ _ ih => have := ih (max_le_iff.mp hp).2; nlinarith
  | loop_false _ => simp
  | loop_true _ _ _ ih₁ ih₂ => have := ih₁ hp; have := ih₂ hp; nlinarith
  | @call f _ _ _ _ ih => have := ih (hb f); nlinarith

/-- Only the initial contents of the tapes being cleared enter the cleanup bound. -/
theorem cleanup_cost_le (is : List (Fin T)) {body : P → Pr P T Q A U} {prog : Pr P T Q A U}
    {s t : HS T Q A U} {S F : Stacks T A} {n c : ℕ}
    (run : Exec body prog (mk s S) n (mk t F)) (hp : mnProgPush prog ≤ c)
    (hb : ∀ f, mnProgPush (body f) ≤ c) :
    (is.map fun i => 4*(F.L i).length+2*(F.R i).length+4).sum+1 ≤
      (is.map fun i => 4*(S.L i).length+2*(S.R i).length+4).sum+1 + is.length*(6*(c*n)) := by
  induction is with
  | nil => simp
  | cons i is ih =>
    have left : (F.L i).length ≤ (S.L i).length+c*n := exec_stack_length run hp hb (.lt i)
    have right : (F.R i).length ≤ (S.R i).length+c*n := exec_stack_length run hp hb (.rt i)
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    rw [Nat.succ_mul is.length]
    omega

def clearWorkTapes : List (Fin T) → Pr P T Q A U
  | [] => .act .done
  | i :: is => .seq (.seq (unload i) (bclear i)) (clearWorkTapes is)

theorem clearWorkTapes_exec (body : P → Pr P T Q A U) (is : List (Fin T)) (distinct : is.Nodup)
    (v : HS T Q A U) (S : Stacks T A) :
    ∃ z, z.user = v.user ∧ Exec body (clearWorkTapes is) (mk v S)
      ((is.map fun i => 4*(S.L i).length+2*(S.R i).length+4).sum+1)
      (mk z {S with L := fun i => if i ∈ is then [] else S.L i,
                    R := fun i => if i ∈ is then [] else S.R i}) := by
  induction is generalizing v S with
  | nil => exact ⟨v,rfl,by simpa [clearWorkTapes] using Exec.act (body := body) .done (mk v S)⟩
  | cons i is ih =>
    obtain ⟨u,hu,drain⟩ := unload_exec body i v S
    obtain ⟨y,hy,_,clear⟩ := bclear_exec body i u _
    let D : Stacks T A := {S with L := Function.update S.L i [], R := Function.update S.R i []}
    have step : Exec body (.seq (unload i) (bclear i)) (mk v S)
        (4*(S.L i).length+2*(S.R i).length+4) (mk y D) := by
      apply (Exec.seq drain clear).cast
      · simp; omega
      · simp [D]
    obtain ⟨z,hz,run⟩ := ih distinct.tail y D
    have cost : (is.map fun j => 4*(D.L j).length+2*(D.R j).length+4) =
        is.map fun j => 4*(S.L j).length+2*(S.R j).length+4 := by
      apply List.map_congr_left
      intro j hj
      have ne : j ≠ i := fun e => distinct.notMem (e ▸ hj)
      simp [D,Function.update_of_ne ne]
    refine ⟨z,hz.trans (hy.trans hu),(Exec.seq step run).cast ?_ ?_⟩
    · rw [cost]; simp; omega
    · congr 2 <;> funext j <;> by_cases h : j = i <;> simp [D,h]

/-- Clear a closed program's initially empty private tapes. Its step bound controls
the cleanup even when the shared tapes carry arbitrarily long queues. -/
theorem clearPrivate_exec {K : ℕ} (bank : Fin K ↪ Fin T) (prog : Pr Empty T Q A U)
    (v z : HS T Q A U) (S F : Stacks T A) (n budget : ℕ)
    (run : Exec Empty.elim prog (mk v S) n (mk z F)) (time : n ≤ budget)
    (empty : ∀ i, S.L (bank i) = [] ∧ S.R (bank i) = []) :
    let tapes := (List.finRange K).map bank
    ∃ u D l, u.user = z.user ∧ l ≤ budget + (K*4+1+K*(6*(mnProgPush prog*budget))) ∧
      Exec Empty.elim (.seq prog (clearWorkTapes tapes)) (mk v S) l (mk u D) ∧
      (∀ i, D.L (bank i) = [] ∧ D.R (bank i) = []) ∧
      ∀ h, (∀ i, bank i ≠ h) → D.L h = F.L h ∧ D.R h = F.R h := by
  intro tapes
  obtain ⟨u,hu,clear⟩ := clearWorkTapes_exec Empty.elim tapes ((List.nodup_finRange _).map bank.injective) z F
  have charge := cleanup_cost_le tapes run le_rfl (fun e => nomatch e)
  have init : (tapes.map fun h => 4*(S.L h).length+2*(S.R h).length+4) = tapes.map (fun _ => 4) := by
    apply List.map_congr_left
    intro h mem
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp mem
    simp [(empty i).1,(empty i).2]
  simp only [init,List.map_const',List.sum_replicate_nat,show tapes.length = K by simp [tapes]] at charge
  refine ⟨u,_,_,hu,Nat.add_le_add time (charge.trans (by gcongr)),Exec.seq run clear,?_,?_⟩
  · intro i
    simp [tapes,List.mem_map]
  · intro h off
    have absent : h ∉ tapes := fun mem => by obtain ⟨i,_,eq⟩ := List.mem_map.mp mem; exact off i eq
    simp [absent]

def shearWork : List (Fin 35) :=
  (List.finRange 35).filter fun i => decide (i ≤ 26 ∧ i ≠ 2 ∧ i ≠ 24 ∧ i ≠ 25 ∨ 29 ≤ i ∧ i ≤ 31)

theorem shearWork_nodup (r : Fin 35 ↪ Fin T) : (shearWork.map r).Nodup :=
  ((List.nodup_finRange _).filter _).map r.injective

/-- Charge only the material on work tapes. Every other tape keeps its exact stack pair. -/
theorem clearShear_exec (body : P → Pr P T Q A U) (r : Fin 35 ↪ Fin T)
    (v : HS T Q A U) (S : Stacks T A) :
    let tapes := shearWork.map r
    ∃ z F, z.user = v.user ∧ Exec body (clearWorkTapes tapes) (mk v S)
      ((tapes.map fun i => 4*(S.L i).length+2*(S.R i).length+4).sum+1) (mk z F) ∧
      (∀ i : Fin 35, (i ≤ 26 ∧ i ≠ 2 ∧ i ≠ 24 ∧ i ≠ 25) ∨ (29 ≤ i ∧ i ≤ 31) →
        F.L (r i) = [] ∧ F.R (r i) = []) ∧
      ∀ j, j ∉ tapes → F.L j = S.L j ∧ F.R j = S.R j := by
  intro tapes
  obtain ⟨z,hz,run⟩ := clearWorkTapes_exec body tapes (shearWork_nodup r) v S
  refine ⟨z,_,hz,run,?_,?_⟩
  · intro i hi
    have mem : r i ∈ tapes := List.mem_map.mpr ⟨i,by simpa [shearWork] using hi,rfl⟩
    simp [mem]
  · intro j hj
    simp [hj]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
