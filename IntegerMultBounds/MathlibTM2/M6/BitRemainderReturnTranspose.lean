module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderRowSplit

/-! Restore staging order by peeling the active rows in reverse. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host CompactRows

def returnTransposeLoop {P U : Type} {Q A : ℕ} : Pr P 8 Q A U :=
  .loop (·.flag) (extractActiveRow.seq (.act (peekR 3)))

private def widthClock {α : Type} (record : List α) (n : ℕ) := (List.replicate n record.reverse).flatten

private theorem returnLoop_exec {P U : Type} {Q A B K : ℕ} (body : P → Pr P 8 Q A U)
    (S : Stacks 8 A) (record rowWidth : List (Fin (A+4))) (hk : record.length = K)
    (hK : 0 < K) (hB : 0 < B) (limit : ℕ) (rows : List (Fin B → List (Fin (A+4))))
    (bound : rows.length ≤ limit) (width : ∀ r ∈ rows, ∀ b, (r b).length = K)
    (rest : List (Fin (A+4))) (u : HS 8 Q A U)
    (flag : u.flag = (widthClock record rows.length).head?.isSome) :
    ∃ z steps, z.user = u.user ∧ Exec body returnTransposeLoop
      (mk u (transposeStacks S (columns rows) rest (widthClock record rows.length) record rowWidth)) steps
      (mk z (transposeStacks S [] (unread rows++rest) [] record rowWidth)) ∧
      steps ≤ rows.length*(compactPassCost B K limit+2)+1 := by
  induction rows using List.reverseRecOn generalizing rest u with
  | nil =>
    have emp : columns ([] : List (Fin B → List (Fin (A+4)))) = [] := by simp [columns]
    rw [emp]
    exact ⟨u,1,rfl,Exec.loop_false flag,by simp⟩
  | append_singleton rows r ih =>
    have wr := width r (by simp)
    have prev : ∀ z ∈ rows, ∀ b, (z b).length = K := fun z h => width z (by simp [h])
    let pairs := rowPairs rows r
    let pre := widthClock record rows.length
    have len : pre.length = rows.length*K := by simp [pre,widthClock,hk]
    have widths : ∀ p ∈ pairs, p.1.length = pre.length ∧ p.2.length = record.length := by
      intro p hm
      obtain ⟨b,rfl⟩ := List.mem_ofFn.mp hm
      exact ⟨(recordLengths _ prev b).trans len.symm,(wr b).trans hk.symm⟩
    obtain ⟨v,n,user,split,cost⟩ := extractActiveRow_exec body pairs S u rest pre record rowWidth (hk ▸ hK) widths
    simp only [pairs,rowPairs_output,rowPairs_prefix,rowPairs_incoming] at split cost
    have clock : widthClock record (rows++[r]).length = record.reverse++pre := by
      simp [widthClock,pre,List.replicate_succ]
    have on : u.flag = true := by
      rw [clock] at flag
      cases eq : record.reverse with
      | nil => have h := congrArg List.length eq; simp [hk] at h; omega
      | cons a as => simpa [eq] using flag
    let next := {v with flag := pre.head?.isSome}
    let F := transposeStacks S (columns rows) ((List.ofFn r).flatten++rest) pre record rowWidth
    have peek : Exec body (.act (peekR 3)) (mk v F) 1 (mk next F) := Exec.act _ _
    have le : rows.length ≤ limit := by simpa using (Nat.le_of_succ_le (by simpa using bound : rows.length+1 ≤ limit))
    obtain ⟨z,m,same,tail,paid⟩ := ih le prev _ next rfl
    have total := blockLength (fun b => rows.flatMap (fun z => z b)) (recordLengths rows prev)
    have rowLen := blockLength r wr
    have one : K ≤ B*K := Nat.le_mul_of_pos_left _ hB
    have nBound : n ≤ compactPassCost B K limit := by
      simp only [columns, rowPairs,List.length_ofFn,total,rowLen,len,hk] at cost
      rw [cost]
      unfold compactPassCost
      have preLe : rows.length*K ≤ limit*K := Nat.mul_le_mul_right _ le
      have terms := Nat.mul_le_mul_left B (Nat.add_le_add_right (Nat.mul_le_mul_left 4 (Nat.add_le_add_right preLe K)) 10)
      have cells := Nat.mul_le_mul_left B preLe
      rw [show B*((limit+1)*K) = B*(limit*K)+B*K by ring] 
      omega
    rw [clock]
    refine ⟨z,_,same.trans user,(Exec.loop_true on (Exec.seq split peek) tail).cast rfl ?_,?_⟩
    · simp [unread,List.append_assoc]
    · simp only [List.length_append,List.length_singleton,Nat.add_mul,Nat.one_mul]
      omega

/-- Transpose all blocks of records. The step bound counts the actual passes
and is independent of how the block index splits into parents and labels. -/
theorem returnRecordBlocks_exec {P U : Type} {q alphabet : ℕ}
    (body : P → Pr P 8 q alphabet U) (A B K : ℕ) (hb : 0 < B) (hk : 0 < K) :
    ∀ (x : Fin (B*(A*K)) → Fin (alphabet+4)) (S : Stacks 8 alphabet)
      (u : HS 8 q alphabet U) (record rowWidth : List (Fin (alphabet+4))), record.length = K →
      ∃ v steps, v.user = u.user ∧ Exec body (.seq (.act (peekR 3)) returnTransposeLoop)
        (mk u (transposeStacks S (List.ofFn x) [] (List.replicate A record.reverse).flatten record rowWidth))
        steps (mk v (transposeStacks S [] (List.ofFn (compactTranspose x)) [] record rowWidth)) ∧
        steps ≤ A*(compactPassCost B K A+2)+2 := by
  intro x S u record rowWidth hw
  let r := fun (a : Fin A) (b : Fin B) => List.ofFn (fun j : Fin K => x (finProdFinEquiv (b,finProdFinEquiv (a,j))))
  let rows := List.ofFn r
  let start := transposeStacks S (columns rows) [] (widthClock record rows.length) record rowWidth
  let next := {u with flag := (widthClock record rows.length).head?.isSome}
  have peek : Exec body (.act (peekR 3)) (mk u start) 1 (mk next start) := Exec.act _ _
  obtain ⟨v,t,same,run,bill⟩ := returnLoop_exec body S record rowWidth hw hk hb A rows
    (by simp [rows]) (by intro row mem b; obtain ⟨a,rfl⟩ := List.mem_ofFn.mp mem; exact List.length_ofFn)
    [] next rfl
  have full := Exec.seq peek run
  simp only [rows,List.length_ofFn] at bill
  refine ⟨v,1+t,same,?_,by omega⟩
  rw [serialized x,serialized (compactTranspose x)]
  simpa only [start,rows,r,columns,unread,widthClock,List.length_ofFn,List.append_nil,
    List.flatMap_def,List.map_ofFn,Function.comp_def,compactTranspose,Equiv.symm_apply_apply] using full

/-- Restore the compact staging word on the eight-register host within the padded volume. -/
theorem remainderCompactReturn_exec {P U : Type} {q alphabet : ℕ}
    (body : P → Pr P 8 q alphabet U) (w B K : ℕ) (hb : 0 < B) (hk : 0 < K) :
    let A := (IntegerMultBounds.Networks.Shared50ModularControl.prime^w)^16
    let N := IntegerMultBounds.Networks.Shared50ModularControl.prime^(64*(w*64))
    ∀ (x : Fin (B*(A*K)) → Fin (alphabet+4)) (S : Stacks 8 alphabet)
      (u : HS 8 q alphabet U) (record rowWidth : List (Fin (alphabet+4))), record.length = K →
      ∃ v steps, v.user = u.user ∧ Exec body (.seq (.act (peekR 3)) returnTransposeLoop)
        (mk u (transposeStacks S (List.ofFn x) [] (List.replicate A record.reverse).flatten record rowWidth))
        steps (mk v (transposeStacks S [] (List.ofFn (compactTranspose x)) [] record rowWidth)) ∧
        steps ≤ 52*(A*(B*N*K))+2 := by
  intro A N x S u record rowWidth hw
  obtain ⟨v,k,user,run,paid⟩ := returnRecordBlocks_exec body A B K hb hk x S u record rowWidth hw
  exact ⟨v,k,user,run,paid.trans (compactTranspose_volume_bound w B K hb hk)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
