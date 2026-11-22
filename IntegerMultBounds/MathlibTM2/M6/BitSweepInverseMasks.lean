module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderTranspose
public import IntegerMultBounds.MathlibTM2.M6.BitSweepPlacedGather

/-! Transpose the forward selectors to obtain the inverse gather stream. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host Node

private theorem inverseMaskRows {α : Type} {n : ℕ} (f : Fin n → α) :
    (List.ofFn fun i => [f i]).flatten = List.ofFn f := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.ofFn_succ, ih]

/-- Forward selectors have descending destination rows. Transposition puts the
inverse selectors in reverse tape order, suitable for a stack transfer. -/
private theorem transposePermutationMasks_exec {P U : Type} {A Q n : ℕ}
    (body : P → Pr P 8 Q A U) (p : Equiv.Perm (Fin n)) (positive : 0 < n)
    (S : Stacks 8 A) (u : HS 8 Q A U) (unit row : List (Fin (A+4)))
    (one : unit.length = 1) (width : row.length = n) :
    let stream := fun q : Equiv.Perm (Fin n) => (permutationMasks q).flatten.map (bitSymbol (a := A))
    ∃ v steps, v.user = u.user ∧ steps ≤ n*(compactPassCost n 1 n+2)+2 ∧
      Exec body (.seq (.act (peekR 6)) transposeLoop)
        (mk u (transposeStacks S [] (stream p) [] unit row)) steps
        (mk v (transposeStacks S (stream p.symm).reverse []
          (List.replicate n unit.reverse).flatten unit row)) := by
  intro stream
  let cell := fun (j i : Fin n) => bitSymbol (a := A) (decide (p i = j))
  let rows := (List.ofFn fun j i => [cell j i]).reverse
  obtain ⟨v,clock,steps,hclock,user,run,bill⟩ := compactTranspose_exec body S unit row u
    (K := 1) (B := n) (by decide) positive one (by simpa using width) rows (by
      intro r hr i
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hr)
      rfl)
  have len : rows.length = n := by simp [rows]
  refine ⟨v,steps,user,by simpa only [len] using bill,?_⟩
  rw [hclock,len] at run
  have input : rows.flatMap (fun r => (List.ofFn r).flatten) = stream p := by
    simp [rows,stream,permutationMasks_forward,List.flatMap_def,List.map_reverse,
      List.map_flatten,List.map_ofFn,Function.comp_def,cell,inverseMaskRows]
  have output : (List.ofFn (fun i => rows.flatMap (fun r => r i))).flatten =
      (stream p.symm).reverse := by
    simp only [rows,stream,permutationMasks_forward,List.flatMap_def,List.map_reverse,
      List.map_flatten,List.map_ofFn,Function.comp_def,cell]
    rw [List.reverse_flatten]
    simp only [List.map_reverse,List.reverse_reverse,List.map_ofFn,Function.comp_def,Equiv.symm_apply_eq]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    rw [← inverseMaskRows (fun j => bitSymbol (a := A) (decide (j = p i))),List.reverse_flatten]
    simp [List.map_ofFn,Function.comp_def,eq_comm]
  simpa only [input,output] using run

/-- Replace the forward mask tape by its inverse in place and restore the
transpose workspace. For a permutation of n records the cost is cubic in n. -/
theorem invertPermutationMasks_exec {P U : Type} {A Q n : ℕ}
    (body : P → Pr P 8 Q A U) (p : Equiv.Perm (Fin n)) (positive : 0 < n)
    (S : Stacks 8 A) (u : HS 8 Q A U) (unit row : List (Fin (A+4)))
    (one : unit.length = 1) (width : row.length = n) :
    let stream := fun q : Equiv.Perm (Fin n) => (permutationMasks q).flatten.map (bitSymbol (a := A))
    ∃ v steps, v.user = u.user ∧ steps ≤ 60*n^3+6 ∧
      Exec body (.seq (.seq (.act (peekR 6)) transposeLoop) (.seq (moveR 0 6 id) (uclear 3)))
        (mk u (transposeStacks S [] (stream p) [] unit row)) steps
        (mk v (transposeStacks S [] (stream p.symm) [] unit row)) := by
  intro stream
  obtain ⟨v,t,user,paid,transpose⟩ := transposePermutationMasks_exec body p positive S u unit row one width
  let clock := (List.replicate n unit.reverse).flatten
  let F := transposeStacks S (stream p.symm).reverse [] clock unit row
  obtain ⟨y,hy,move⟩ := moveR_exec body 0 6 (by decide) id v F
  let G := {F with R := movedR F.R 0 6 id (F.R 0)}
  obtain ⟨z,hz,clear⟩ := uclear_exec (body := body) 3 y G
  refine ⟨z,_,hz.trans (hy.trans user),?_,(Exec.seq transpose (Exec.seq move clear)).cast rfl ?_⟩
  · have size : (stream p.symm).length = n*n := by
      simp [stream,permutationMasks_forward,List.length_flatten,List.map_reverse,List.map_ofFn,Function.comp_def,List.ofFn_const]
    have tick : clock.length = n := by simp [clock,List.length_flatten,one]
    change t + (2 * (stream p.symm).reverse.length + 2 + (2*clock.length+2)) ≤ _
    rw [List.length_reverse,size,tick]
    unfold compactPassCost at paid
    nlinarith [Nat.mul_le_mul_left n positive, Nat.mul_le_mul_left (n*n) (show 1 ≤ n by omega),
      Nat.mul_le_mul_left n (show 1 ≤ n by omega)]
  · apply congrArg (mk z)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    fin_cases i <;> simp [G,F,movedR,transposeStacks]

/-- Gather the return permutation using the same selector tape as the forward
gather. Only the selector and destination tapes change. -/
theorem sweepInverseGather_exec {T Q A n W : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    (bank : Fin 8 ↪ Fin T) (g : Fin 10 ↪ Fin T) (shared : bank 6 = g 0)
    (p : Equiv.Perm (Fin n)) (positive : 0 < n) (rows : Fin n → List (Fin (A+4)))
    (sizes : ∀ i, (rows i).length = W) (tail unit row : List (Fin (A+4)))
    (one : unit.length = 1) (width : row.length = n) (v : HS T Q A U) (S : Stacks T A)
    (prepared : embStk bank S = transposeStacks (embStk bank S) []
      ((permutationMasks p).flatten.map bitSymbol) [] unit row)
    (input : S.R (g 2) = (List.ofFn rows).flatten ++ tail) (count : (S.R (g 4)).length = n)
    (record : (S.R (g 3)).length = W) (fresh : ∀ i : Fin 10, 5 ≤ i.val → S.R (g i) = []) :
    ∃ z steps, z.user = v.user ∧ steps ≤ 60*n^3+n*(n*(16*W+18)+26)+8 ∧
      Exec body (.seq (embProg bank Empty.elim
        (.seq (.seq (.act (peekR 6)) transposeLoop) (.seq (moveR 0 6 id) (uclear 3))))
        (embProg g Empty.elim sweepGatherProgram)) (mk v S) steps
        (mk z {S with
          R := Function.update (Function.update S.R (g 0) []) (g 1)
            ((List.ofFn (fun i => rows (p i))).flatten ++ S.R (g 1))}) := by
  let stream := (permutationMasks p.symm).flatten.map (bitSymbol (a := A))
  obtain ⟨u,k,hu,hk,inv⟩ := invertPermutationMasks_exec (P := Empty) Empty.elim p positive
    (embStk bank S) (embDn bank v) unit row one width
  have finish : transposeStacks (embStk bank S) [] stream [] unit row =
      {(embStk bank S) with R := Function.update (embStk bank S).R 6 stream} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    have orig := congrArg (fun D : Stacks 8 A => D.R i) prepared
    fin_cases i <;> first | rfl | simpa [transposeStacks] using orig.symm
  rw [← prepared,finish] at inv
  obtain ⟨u',_,user,placed⟩ := exec_emb_ovr (ι := (Empty.elim : Empty → P)) bank.injective
    (body' := body) (fun e => nomatch e) inv v rfl S rfl
  rw [embOvr_stream bank bank.injective,shared] at placed
  let F := {S with R := Function.update S.R (g 0) stream}
  have keep (i : Fin 10) (hi : i ≠ 0) : F.R (g i) = S.R (g i) :=
    Function.update_of_ne (g.injective.ne hi) _ _
  obtain ⟨z,l,hz,hl,gather⟩ := sweepPlacedGather_exec body g p.symm rows positive sizes tail u' F
    ((keep 2 (by decide)).trans input) (by rwa [keep 4 (by decide)]) (by rwa [keep 3 (by decide)])
    (fun i hi => (keep i (by omega)).trans (fresh i hi)) (Function.update_self ..)
  refine ⟨z,k+l,hz.trans (user.trans hu),by omega,Exec.seq placed ?_⟩
  simpa only [F,Function.update_of_ne (show g 1 ≠ g 0 by simp),Function.update_idem,Equiv.symm_symm] using gather

end IntegerMultBounds.MathlibTM2.M6.BitNode
