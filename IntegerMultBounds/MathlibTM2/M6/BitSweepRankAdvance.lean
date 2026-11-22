module

public import IntegerMultBounds.MathlibTM2.Cover.LabelDirectoryCounter
public import IntegerMultBounds.MathlibTM2.Host.IndexCode

/-! Transfer a binary source rank to the selector stream and advance its destination. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host Node RadixDigits RadixCounterData
variable {T Q q : ℕ} {P U : Type}

noncomputable def advanceSweepRank (hq : 2 ≤ q) (r : Fin 7 ↪ Fin T) : Pr P T Q q U :=
  .seq (moveR (r 1) (r 2) id)
    (.seq (.act (.push (.rt (r 2)) (fun _ => separator) .done))
      (.seq (Cover.LabelDirectoryCounter.tick hq (fun _ => r 0) ![r 3,r 4] (r 5) (r 5) (r 6))
        (bclear (r 3))))

theorem advanceSweepRank_exec (body : P → Pr P T Q q U) (hq : 2 ≤ q) (r : Fin 7 ↪ Fin T)
    (ds : List (Fin q)) (pos : 0 < ds.length) (H rank : ℕ) (v : HS T Q q U) (S : Stacks T q)
    (counter : S.R (r 0) = ds.map digitSymbol) (result : S.R (r 1) = binSyms H rank)
    (width : (S.R (r 5)).length = ds.length)
    (free : ∀ i : Fin 7, i = 3 ∨ i = 4 ∨ i = 6 → S.R (r i) = []) :
    ∃ z n, z.user = v.user ∧ n ≤ 2*H+9*ds.length+15 ∧
      Exec body (advanceSweepRank hq r) (mk v S) n (mk z {S with
        R := Function.update (Function.update (Function.update S.R (r 1) []) (r 2)
          (separator :: (binSyms H rank).reverse ++ S.R (r 2))) (r 0) ((increment hq ds).map digitSymbol)}) := by
  let B := {S with R := movedR S.R (r 1) (r 2) id (S.R (r 1))}
  obtain ⟨u,hu,move⟩ := moveR_exec body (r 1) (r 2) (by simp) id v S
  let C := {S with
    R := Function.update (Function.update S.R (r 1) []) (r 2)
      (separator :: (binSyms H rank).reverse ++ S.R (r 2))}
  have push : Exec body (.act (.push (.rt (r 2)) (fun _ => separator) .done)) (mk u B) 1 (mk u C) := by
    apply (Exec.act _ _).cast rfl
    simp [Action.run,update_rt,B,C,movedR,result]
  have layout : AutoLayout (fun _ : Fin 1 => r 0) ![r 3,r 4] (r 5) (r 5) (r 6) := by
    constructor
    · exact fun _ _ _ => Subsingleton.elim _ _
    · intro i j h; fin_cases i <;> fin_cases j <;> simp_all
    · intro i j; fin_cases j <;> simp
    · intro i; simp
    · intro i; simp
    · intro j; fin_cases j <;> simp
    · intro j; fin_cases j <;> simp
    · simp
    · intro i; simp
  obtain ⟨y,k,hy,hk,tick⟩ := Cover.LabelDirectoryCounter.tick_exec (body := body) hq layout ds pos u C
    (by simpa [C] using width) (by simpa [C] using free 6 (by decide))
    (by simpa [C] using free 4 (by decide)) (by simpa [C] using counter)
  let F := {C with
    R := Function.update (Function.update C.R (r 3) (ds.map digitSymbol).reverse)
      (r 0) ((increment hq ds).map digitSymbol)}
  have old : C.R (r 3) = [] := by simpa [C] using free 3 (by decide)
  change Exec _ _ _ _ (mk y {C with R := Function.update (Function.update C.R (r 3)
    ((ds.map digitSymbol).reverse ++ C.R (r 3))) (r 0) ((increment hq ds).map digitSymbol)}) at tick
  rw [old,List.append_nil] at tick
  obtain ⟨z,hz,_,clear⟩ := bclear_exec body (r 3) y F
  have size : (F.R (r 3)).length = ds.length := by simp [F]
  refine ⟨z,2*(S.R (r 1)).length+2+(1+(k+(2*(F.R (r 3)).length+2))),hz.trans (hy.trans hu),by rw [size,result,length_binSyms]; omega,
    Exec.seq move (Exec.seq push (Exec.seq tick ?_))⟩
  change Exec _ _ _ _ (mk z {C with R := Function.update C.R (r 0) ((increment hq ds).map digitSymbol)})
  simpa only [F,Function.update_comm (show r 0 ≠ r 3 by simp),Function.update_idem,← old,
    Function.update_eq_self] using clear

/-- A matrix refresh and evaluation may change the matrix register.
The selector step retains that change and returns the rank register blank. -/
theorem sweepSelectorStep_exec (body : P → Pr P T Q q U) (hq : 2 ≤ q) (r : Fin 7 ↪ Fin T)
    (matrix : Fin T) (apart : ∀ i, r i ≠ matrix) (nextMatrix : List (Fin (q+4)))
    (evaluate : Pr P T Q q U) (ds : List (Fin q)) (pos : 0 < ds.length) (H rank : ℕ)
    (v u : HS T Q q U) (S : Stacks T q) (cost : ℕ) (user : u.user = v.user)
    (counter : S.R (r 0) = ds.map digitSymbol) (width : (S.R (r 5)).length = ds.length)
    (free : ∀ i : Fin 7, i = 1 ∨ i = 3 ∨ i = 4 ∨ i = 6 → S.R (r i) = [])
    (run : Exec body evaluate (mk v S) cost (mk u {S with
      R := Function.update (Function.update S.R matrix nextMatrix) (r 1) (binSyms H rank)})) :
    ∃ z n, z.user = v.user ∧ n ≤ cost+(2*H+9*ds.length+15) ∧
      Exec body (.seq evaluate (advanceSweepRank hq r)) (mk v S) n (mk z {S with
        R := Function.update (Function.update (Function.update S.R matrix nextMatrix) (r 2)
          (separator :: (binSyms H rank).reverse ++ S.R (r 2))) (r 0) ((increment hq ds).map digitSymbol)}) := by
  let B := {S with R := Function.update (Function.update S.R matrix nextMatrix) (r 1) (binSyms H rank)}
  have keep (i : Fin 7) (hi : i ≠ 1) : B.R (r i) = S.R (r i) := by simp [B,hi,apart]
  obtain ⟨z,k,hz,hk,advance⟩ := advanceSweepRank_exec body hq r ds pos H rank u B
    ((keep 0 (by decide)).trans counter) (Function.update_self ..) (by rwa [keep 5 (by decide)])
    (fun i h => (keep i (by omega)).trans (free i (by tauto)))
  have empty : Function.update S.R matrix nextMatrix (r 1) = [] := by simpa [apart] using free 1 (by decide)
  refine ⟨z,cost+k,hz.trans user,Nat.add_le_add_left hk _,Exec.seq run ?_⟩
  simpa only [B,Function.update_of_ne (show r 2 ≠ r 1 by simp),Function.update_of_ne (apart 2),Function.update_idem,← empty,Function.update_eq_self] using advance

end IntegerMultBounds.MathlibTM2.M6.BitNode
