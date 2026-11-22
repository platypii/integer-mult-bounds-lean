module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix
public import IntegerMultBounds.MathlibTM2.Cover.LabelTraversal

/-! Apply a length-preserving block writer in place to contiguous inherited blocks. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host Node Mult.PhaseCellToeplitz

def sweepBlockScan {P U : Type} {T Q A : ℕ} (r : Fin 5 ↪ Fin T) (writer : Pr P T Q A U) : Pr P T Q A U :=
  let step := writer.seq ((discardPrefix (r 1) (r 0) (r 3) (r 4)).seq
    ((moveR (r 1) (r 2) id).seq (.act (peekR (r 0)))))
  .seq (.act (peekR (r 0))) (.seq (.loop (·.flag) step) (moveR (r 2) (r 0) id))

theorem sweepBlockScan_exec {P U ι : Type} {T Q A : ℕ} (body : P → Pr P T Q A U)
    (r : Fin 5 ↪ Fin T) (writer : Pr P T Q A U) (blocks : List ι)
    (input output : ι → List (Fin (A+4))) (L cost : ℕ) (positive : 0 < L)
    (sizes : ∀ i, (input i).length = L ∧ (output i).length = L)
    (v : HS T Q A U) (S : Stacks T A) (source : S.R (r 0) = blocks.flatMap input)
    (blank : ∀ i : Fin 5, i ≠ 0 → S.R (r i) = [])
    (write : ∀ i tail (u : HS T Q A U) (B : Stacks T A), B.R (r 0) = input i ++ tail →
      (∀ j, j ≠ r 0 → j ≠ r 2 → B.R j = S.R j) →
      ∃ y t, y.user = u.user ∧ t ≤ cost ∧ Exec body writer (mk u B) t
        (mk y {B with R := Function.update B.R (r 1) (output i)})) :
    ∃ z t, z.user = v.user ∧ t ≤ blocks.length*(cost+10*L+12)+4 ∧
      Exec body (sweepBlockScan r writer) (mk v S) t
        (mk z {S with R := Function.update S.R (r 0) (blocks.flatMap output)}) := by
  let state (xs acc : List (Fin (A+4))) := {S with R := Function.update (Function.update S.R (r 0) xs) (r 2) acc}
  let step : Pr P T Q A U := writer.seq ((discardPrefix (r 1) (r 0) (r 3) (r 4)).seq
    ((moveR (r 1) (r 2) id).seq (.act (peekR (r 0)))))
  have loop (bs : List ι) (acc) (u : HS T Q A U) (flag : u.flag = (bs.flatMap input).head?.isSome) :
      ∃ y t, y.user = u.user ∧ t ≤ bs.length*(cost+8*L+12)+1 ∧
        Exec body (.loop (·.flag) step) (mk u (state (bs.flatMap input) acc)) t
          (mk y (state [] ((bs.flatMap output).reverse ++ acc))) := by
    induction bs generalizing acc u with
    | nil => exact ⟨u,1,rfl,by simp,by simpa using (Exec.loop_false (body := body) (p := step) (by simpa using flag) : Exec body (.loop (·.flag) step) (mk u (state [] acc)) 1 _)⟩
    | cons i bs ih =>
      let tail := bs.flatMap input
      let B := state (input i ++ tail) acc
      obtain ⟨a,k,ha,hk,emit⟩ := write i tail u B (by simp [B,state]) (fun j h₀ h₂ => by simp [B,state,h₀,h₂])
      let F := {B with R := Function.update B.R (r 1) (output i)}
      obtain ⟨b,hb,discard⟩ := discardPrefix_exec (body := body) (count := r 1) (src := r 0) (trash := r 3) (tmp := r 4)
        (by simp [List.nodup_cons]) (input i) tail a F (by simp [F,B,state]) (by simp [F,(sizes i).1,(sizes i).2])
        (by simp [F,B,state,blank 3 (by decide)]) (by simp [F,B,state,blank 4 (by decide)])
      let G := {F with R := Function.update F.R (r 0) tail}
      obtain ⟨c,hc,move⟩ := moveR_exec body (r 1) (r 2) (by simp) id b G
      let rest := state tail ((output i).reverse ++ acc)
      have endMove : {G with R := movedR G.R (r 1) (r 2) id (G.R (r 1))} = rest := by
        congr 1
        funext j
        by_cases h₀ : j = r 0
        · subst j; simp [rest,G,F,B,state,movedR]
        by_cases h₁ : j = r 1
        · subst j; simp [rest,G,F,B,state,movedR,blank 1 (by decide)]
        by_cases h₂ : j = r 2
        · subst j; simp [rest,G,F,B,state,movedR]
        simp [rest,G,F,B,state,movedR,h₀,h₁,h₂]
      rw [endMove,show (G.R (r 1)).length = L by simp [G,F,(sizes i).2]] at move
      have peek := Exec.act (body := body) (peekR (r 0)) (mk c rest)
      rw [peekR_run,show rest.R (r 0) = tail by simp [rest,state]] at peek
      obtain ⟨y,t,hy,ht,more⟩ := ih ((output i).reverse ++ acc) {c with flag := tail.head?.isSome} rfl
      have on : u.flag = true := by
        rw [flag,List.flatMap_cons]
        cases h : input i with
        | nil => have hsize := (sizes i).1; rw [h] at hsize; simp at hsize; omega
        | cons => rfl
      refine ⟨y,k+(6*(input i).length+6+(2*L+2+1))+t+1,hy.trans (hc.trans (hb.trans ha)),?_,?_⟩
      · exact (show k+(6*(input i).length+6+(2*L+2+1))+t+1 ≤ (i::bs).length*(cost+8*L+12)+1 by
          rw [(sizes i).1,List.length_cons,Nat.add_mul]; omega)
      · rw [List.flatMap_cons,List.flatMap_cons,List.reverse_append,List.append_assoc]
        exact
          (Exec.loop_true on (Exec.seq emit (Exec.seq discard (Exec.seq move peek))) more)
  have peek := Exec.act (body := body) (peekR (r 0)) (mk v S)
  rw [peekR_run,source] at peek
  obtain ⟨y,k,hy,hk,process⟩ := loop blocks [] {v with flag := (blocks.flatMap input).head?.isSome} rfl
  have start : state (blocks.flatMap input) [] = S := by simp [state,← source,← blank 2 (by decide)]
  rw [start,List.append_nil] at process
  let E := state [] (blocks.flatMap output).reverse
  obtain ⟨z,hz,move⟩ := moveR_exec body (r 2) (r 0) (by simp) id y E
  have lengthOf (bs : List ι) : (bs.flatMap output).length = bs.length*L := by
    induction bs with
    | nil => simp
    | cons i bs ih => simp [List.flatMap_cons,Nat.add_mul,(sizes i).2,ih,Nat.add_comm]
  have final : {E with R := movedR E.R (r 2) (r 0) id (E.R (r 2))} =
      {S with R := Function.update S.R (r 0) (blocks.flatMap output)} := by
    congr 1
    funext j
    by_cases h₀ : j = r 0
    · subst j; simp [E,state,movedR]
    by_cases h₂ : j = r 2
    · subst j; simp [E,state,movedR,blank 2 (by decide)]
    simp [E,state,movedR,h₀,h₂]
  rw [final,show (E.R (r 2)).length = blocks.length*L by simp [E,state,lengthOf]] at move
  exact ⟨z,_,hz.trans hy,by nlinarith only [hk],Exec.seq peek (Exec.seq process move)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
