module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderRowMerge

/-! The compact transpose grows every inherited block by one record per pass. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host

namespace CompactRows

def columns {B : ℕ} {α : Type} (past : List (Fin B → List α)) :=
  (List.ofFn (fun b => past.flatMap (fun row => row b))).flatten

def rowPairs {B : ℕ} {α : Type} (past : List (Fin B → List α)) (row : Fin B → List α) :=
  List.ofFn (fun b => (past.flatMap (fun old => old b),row b))

theorem rowPairs_prefix {B : ℕ} {α : Type} (past : List (Fin B → List α)) (row : Fin B → List α) :
    (rowPairs past row).flatMap Prod.fst = columns past := by
  simp [rowPairs,columns,List.flatMap_def,List.map_ofFn,Function.comp_def]
theorem rowPairs_incoming {B : ℕ} {α : Type} (past : List (Fin B → List α)) (row : Fin B → List α) :
    (rowPairs past row).flatMap Prod.snd = (List.ofFn row).flatten := by
  simp [rowPairs,List.flatMap_def,List.map_ofFn,Function.comp_def]
theorem rowPairs_output {B : ℕ} {α : Type} (past : List (Fin B → List α)) (row : Fin B → List α) :
    (rowPairs past row).flatMap (fun r => r.1++r.2) = columns (past++[row]) := by
  simp [rowPairs,columns,List.flatMap_def,List.map_ofFn,Function.comp_def]

theorem recordLengths {B K : ℕ} {α : Type} (rows : List (Fin B → List α))
    (width : ∀ row ∈ rows, ∀ b, (row b).length = K) (b : Fin B) :
    (rows.flatMap (fun row => row b)).length = rows.length*K := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    rw [width row List.mem_cons_self,ih (fun r h => width r (List.mem_cons_of_mem _ h))]
    omega

theorem blockLength {B K : ℕ} {α : Type} (row : Fin B → List α)
    (width : ∀ b, (row b).length = K) : (List.ofFn row).flatten.length = B*K := by
  rw [BlockRotationData.uniform_volume K]
  · simp
  · intro word mem
    obtain ⟨b,rfl⟩ := List.mem_ofFn.mp mem
    exact width b

def unread {B : ℕ} {α : Type} (rows : List (Fin B → List α)) :=
  rows.flatMap (fun r => (List.ofFn r).flatten)

end CompactRows
open CompactRows

def compactPassCost (B K active : ℕ) :=
  6*(B*K)+B*(4*(active*K+K)+10)+2*(B*((active+1)*K))+4*K+14

private def compactPassSum (B K : ℕ) : ℕ → ℕ → ℕ
  | 0,_ => 1
  | n+1,a => compactPassCost B K a + 2 + compactPassSum B K n (a+1)

def transposeLoop {P U : Type} {Q A : ℕ} : Pr P 8 Q A U :=
  .loop (·.flag) (insertActiveRow.seq (.act (peekR 6)))

private theorem transposeLoop_exec {P U : Type} {A Q B K : ℕ} (body : P → Pr P 8 Q A U)
    (S : Stacks 8 A) (recordWidth rowWidth : List (Fin (A+4)))
    (hK : 0 < K) (hB : 0 < B) (hk : recordWidth.length = K) (hb : rowWidth.length = B*K)
    (rows past : List (Fin B → List (Fin (A+4)))) (prefixWidth : List (Fin (A+4)))
    (width : ∀ r ∈ rows, ∀ b, (r b).length = K) (oldWidth : ∀ r ∈ past, ∀ b, (r b).length = K)
    (hp : prefixWidth.length = past.length*K) (u : HS 8 Q A U)
    (flag : u.flag = (unread rows).head?.isSome) :
    ∃ v width', width' = (List.replicate rows.length recordWidth.reverse).flatten ++ prefixWidth ∧ v.user = u.user ∧ Exec body transposeLoop
      (mk u (transposeStacks S (columns past) (unread rows) prefixWidth recordWidth rowWidth))
      (compactPassSum B K rows.length past.length)
      (mk v (transposeStacks S (columns (past++rows)) [] width' recordWidth rowWidth)) := by
  induction rows generalizing past prefixWidth u with
  | nil =>
    refine ⟨u,prefixWidth,rfl,rfl,?_⟩
    simpa only [List.append_nil,List.length_nil,compactPassSum,unread,List.flatMap_nil,transposeLoop] using (Exec.loop_false (body := body)
      (p := insertActiveRow.seq (.act (peekR 6))) (s := mk u (transposeStacks S (columns past) [] prefixWidth recordWidth rowWidth))
      (f := (·.flag)) flag)
  | cons r rs ih =>
    have wr := width r List.mem_cons_self
    have old' : ∀ z ∈ past++[r], ∀ b, (z b).length = K := by
      intro z hz
      rcases List.mem_append.mp hz with h | h
      · exact oldWidth z h
      · simpa only [List.mem_singleton.mp h] using wr
    let pairs := rowPairs past r
    have lengths : ∀ z ∈ pairs, z.1.length = prefixWidth.length ∧ z.2.length = recordWidth.length := by
      intro z mem
      obtain ⟨b,rfl⟩ := List.mem_ofFn.mp mem
      exact ⟨(recordLengths past oldWidth b).trans hp.symm,(wr b).trans hk.symm⟩
    have count := blockLength r wr
    obtain ⟨v,n,user,step,time⟩ := insertActiveRow_exec body pairs S u (unread rs) prefixWidth recordWidth rowWidth
      (hk ▸ hK) lengths (by rw [rowPairs_incoming,count,hb])
    simp only [pairs,rowPairs_prefix,rowPairs_incoming,rowPairs_output] at step time
    let F := transposeStacks S (columns (past++[r])) (unread rs) (recordWidth.reverse++prefixWidth) recordWidth rowWidth
    let next := {v with flag := (unread rs).head?.isSome}
    have peek : Exec body (.act (peekR 6)) (mk v F) 1 (mk next F) := Exec.act _ _
    obtain ⟨z,ws,clock,same,rest⟩ := ih (past++[r]) (recordWidth.reverse++prefixWidth) (fun z h => width z (List.mem_cons_of_mem _ h))
      old' (by simp [hp,hk,Nat.add_mul]; omega) next rfl
    have full : ((List.ofFn r).flatten).length > 0 := count ▸ Nat.mul_pos hB hK
    have on : u.flag = true := by
      cases eq : (List.ofFn r).flatten with
      | nil => simp [eq] at full
      | cons a l => simpa [unread,eq] using flag
    have outLen := blockLength (fun b => (past++[r]).flatMap (fun z => z b))
      (recordLengths _ old')
    refine ⟨z,ws,by simpa [List.replicate_succ',List.append_assoc] using clock,same.trans user,(Exec.loop_true on (Exec.seq step peek) rest).cast ?_ ?_⟩
    · simp only [columns] at time
      rw [outLen] at time
      simp only [rowPairs,List.length_ofFn,hp,hk,hb,List.length_append,List.length_singleton] at time
      simp only [List.length_cons,List.length_nil,Nat.zero_add,compactPassSum,compactPassCost,List.length_append]
      omega
    · simp [List.append_assoc]

/-- Consume the entire compact rectangle and return it grouped by inherited
block. The program is fixed independently of the dimensions. -/
theorem compactTranspose_exec {P U : Type} {A Q B K : ℕ} (body : P → Pr P 8 Q A U)
    (S : Stacks 8 A) (recordWidth rowWidth : List (Fin (A+4))) (u : HS 8 Q A U)
    (hK : 0 < K) (hB : 0 < B) (hk : recordWidth.length = K) (hb : rowWidth.length = B*K)
    (rows : List (Fin B → List (Fin (A+4)))) (width : ∀ r ∈ rows, ∀ b, (r b).length = K) :
    let start := transposeStacks S [] (rows.flatMap (fun r => (List.ofFn r).flatten)) [] recordWidth rowWidth
    let output := (List.ofFn (fun b => rows.flatMap (fun r => r b))).flatten
    ∃ v width' steps, width' = (List.replicate rows.length recordWidth.reverse).flatten ∧ v.user = u.user ∧ Exec body (.seq (.act (peekR 6)) transposeLoop)
      (mk u start) steps (mk v (transposeStacks S output [] width' recordWidth rowWidth)) ∧
      steps ≤ rows.length*(compactPassCost B K rows.length+2)+2 := by
  intro start output
  let v := {u with flag := (unread rows).head?.isSome}
  have read : Exec body (.act (peekR 6)) (mk u start) 1 (mk v start) := Exec.act _ _
  obtain ⟨z,ws,clock,same,run⟩ := transposeLoop_exec body S recordWidth rowWidth hK hB hk hb
    rows [] [] width (by simp) (by simp) v rfl
  have empty : columns ([] : List (Fin B → List (Fin (A+4)))) = [] := by simp [columns]
  rw [empty] at run
  have bound (n a : ℕ) (h : a+n ≤ rows.length) :
      compactPassSum B K n a ≤ n*(compactPassCost B K rows.length+2)+1 := by
    induction n generalizing a with
    | zero => simp [compactPassSum]
    | succ n ih =>
      have tail := ih (a+1) (by omega)
      have mono : compactPassCost B K a ≤ compactPassCost B K rows.length := by
        unfold compactPassCost
        gcongr <;> omega
      simp only [compactPassSum,Nat.add_mul,Nat.one_mul]
      omega
  exact ⟨z,ws,_,by simpa using clock,same,Exec.seq read run,by simp only [List.length_nil]; have := bound rows.length 0 (by simp); omega⟩

/-- The entire insertion loop costs at most a constant times the padded
volume. This uses the staging label count only for the bound. -/
theorem compactTranspose_volume_bound (w B K : ℕ) (hb : 0 < B) (hk : 0 < K) :
    let A := (IntegerMultBounds.Networks.Shared50ModularControl.prime^w)^16
    let N := IntegerMultBounds.Networks.Shared50ModularControl.prime^(64*(w*64))
    A*(compactPassCost B K A+2)+2 ≤ 52*(A*(B*N*K))+2 := by
  intro A N
  have a : 1 ≤ A := pow_pos (pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _) _
  have scans := compactTranspose_scan_bound w B K
  have bk : B*K ≤ B*(A*K) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left K a)
  have small : B ≤ B*K := Nat.le_mul_of_pos_right B hk
  have key : K ≤ B*K := Nat.le_mul_of_pos_left K hb
  have one : 1 ≤ B*K := Nat.mul_pos hb hk
  have localBill : compactPassCost B K A + 2 ≤ 52*(A*(B*K)) := by
    unfold compactPassCost
    ring_nf at bk small key one ⊢
    omega
  calc
    _ ≤ A*(52*(A*(B*K)))+2 := Nat.add_le_add_right (Nat.mul_le_mul_left _ localBill) _
    _ = 52*(A*(A*(B*K)))+2 := by ring
    _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_left _ scans) _

theorem CompactRows.serialized {α : Type} {m n k : ℕ} (x : Fin (m*(n*k)) → α) :
    List.ofFn x = (List.ofFn (fun a : Fin m => (List.ofFn (fun b : Fin n =>
      List.ofFn fun j : Fin k => x (finProdFinEquiv (a,finProdFinEquiv (b,j))))).flatten)).flatten := by
  have pack {u v : ℕ} (f : Fin (u*v) → α) :
      List.ofFn f = (List.ofFn fun i : Fin u => List.ofFn fun j : Fin v => f (finProdFinEquiv (i,j))).flatten := by
    simpa only [finProdFinEquiv,Equiv.coe_fn_mk,Nat.add_comm,Nat.mul_comm] using List.ofFn_mul f
  rw [pack x]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext a
  exact pack _

/-- Transpose arbitrary complete records and retain the width clock for the inverse pass. -/
theorem transposeRecordBlocks_exec {P U : Type} {q alphabet : ℕ}
    (body : P → Pr P 8 q alphabet U) (A B K : ℕ) (hb : 0 < B) (hk : 0 < K) :
    ∀ (x : Fin (A*(B*K)) → Fin (alphabet+4)) (S : Stacks 8 alphabet)
      (u : HS 8 q alphabet U) (recordWidth rowWidth : List (Fin (alphabet+4))),
      recordWidth.length = K → rowWidth.length = B*K →
      ∃ v width' steps, width' = (List.replicate A recordWidth.reverse).flatten ∧ v.user = u.user ∧ Exec body (.seq (.act (peekR 6)) transposeLoop)
        (mk u (transposeStacks S [] (List.ofFn x) [] recordWidth rowWidth)) steps
        (mk v (transposeStacks S (List.ofFn (compactTranspose x)) [] width' recordWidth rowWidth)) ∧
        steps ≤ A*(compactPassCost B K A+2)+2 := by
  intro x S u recordWidth rowWidth hw hrow
  let r := fun (a : Fin A) (b : Fin B) => List.ofFn (fun j : Fin K => x (finProdFinEquiv (a,finProdFinEquiv (b,j))))
  obtain ⟨v,ws,t,clock,same,run,bill⟩ := compactTranspose_exec body S recordWidth rowWidth u hk hb hw hrow (List.ofFn r)
    (by intro row mem b; obtain ⟨a,rfl⟩ := List.mem_ofFn.mp mem; exact List.length_ofFn)
  simp only [List.length_ofFn] at bill
  refine ⟨v,ws,t,by simpa using clock,same,?_,bill⟩
  rw [serialized x,serialized (compactTranspose x)]
  simpa only [r,List.flatMap_def,List.map_ofFn,Function.comp_def,compactTranspose,Equiv.symm_apply_apply] using run

/-- Transpose the actual compact word for a PR589 remainder, within the
original padded volume and on a fixed eight-register host. -/
theorem remainderCompactTranspose_exec {P U : Type} {q alphabet : ℕ}
    (body : P → Pr P 8 q alphabet U) (w B K : ℕ) (hb : 0 < B) (hk : 0 < K) :
    let A := (IntegerMultBounds.Networks.Shared50ModularControl.prime^w)^16
    let N := IntegerMultBounds.Networks.Shared50ModularControl.prime^(64*(w*64))
    ∀ (x : Fin (A*(B*K)) → Fin (alphabet+4)) (S : Stacks 8 alphabet)
      (u : HS 8 q alphabet U) (recordWidth rowWidth : List (Fin (alphabet+4))),
      recordWidth.length = K → rowWidth.length = B*K →
      ∃ v width' steps, width' = (List.replicate A recordWidth.reverse).flatten ∧ v.user = u.user ∧ Exec body (.seq (.act (peekR 6)) transposeLoop)
        (mk u (transposeStacks S [] (List.ofFn x) [] recordWidth rowWidth)) steps
        (mk v (transposeStacks S (List.ofFn (compactTranspose x)) [] width' recordWidth rowWidth)) ∧
        steps ≤ 52*(A*(B*N*K))+2 := by
  intro A N x S u recordWidth rowWidth hw hrow
  obtain ⟨v,clock,t,stock,user,run,paid⟩ := transposeRecordBlocks_exec body A B K hb hk x S u recordWidth rowWidth hw hrow
  exact ⟨v,clock,t,stock,user,run,paid.trans (compactTranspose_volume_bound w B K hb hk)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
