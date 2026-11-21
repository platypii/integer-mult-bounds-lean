module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryDirectoryChart

/-! Read the next chart's predecessor clock and row count from the physical batch headers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover.Fallback Stack Host M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)

noncomputable def childCount {T Q : ℕ} {P U : Type} (r : Fin 6 ↪ Fin T) (divisor : ℕ) (pred : Bool) : Pr P T Q prime U :=
  let adjust := if pred then Prog.act (.pop (.rt (r 1)) (fun v _ => v) .done) else Prog.act .done
  (((toUnary (r 0) (r 2) (r 3) (r 4) (r 5)).seq (Node.udiv divisor (r 2) (r 1) (r 3))).seq
    (Node.uclear (r 2))).seq adjust

theorem childCount_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 6 ↪ Fin T) (divisor : ℕ) (nz : 1 ≤ divisor) (pred : Bool) (x : ℕ)
    (u : HS T Q prime U) (S : Stacks T prime)
    (source : S.R (r 0) = binSyms x.size x) (empty : ∀ j : Fin 6, 1 ≤ j.val → S.R (r j) = []) :
    ∃ z k, z.user = u.user ∧ k ≤ 23*x+13 ∧
      Exec body (childCount r divisor pred) (mk u S) k (mk z {S with R := Function.update S.R (r 1) (
          List.replicate (x/divisor-(if pred then 1 else 0)) Node.tick)}) := by
  obtain ⟨v,n,user,paid,decode⟩ := toUnary_exec_linear body (a := r 0) (z := r 2) (w := r 3)
    (t := r 4) (t₂ := r 5) (by simp) (Nat.lt_size_self x) u S source
    (empty 3 (by decide)) (empty 4 (by decide)) (empty 5 (by decide))
  rw [empty 2 (by decide),List.append_nil] at decode
  let D : Stacks T prime := {S with R := Function.update S.R (r 2) (List.replicate x Node.tick)}
  obtain ⟨y,m,same,price,divide⟩ := Node.udiv_exec body nz (a := r 2) (b := r 1) (t := r 3)
    (by simp) (by simp) (by simp) v D (by simp [D,empty 3 (by decide)])
  have len : (D.R (r 2)).length = x := by simp [D]
  rw [len] at price divide
  rw [show D.R (r 1) = [] by simp [D,empty 1 (by decide)],List.append_nil] at divide
  let F := {D with R := Function.update D.R (r 1) (List.replicate (x/divisor) Node.tick)}
  obtain ⟨z,final,clear⟩ := Node.uclear_exec body (r 2) y F
  have used : (F.R (r 2)).length = x := by simp [F,len]
  rw [used] at clear
  let B := {S with R := Function.update S.R (r 1) (List.replicate (x/divisor) Node.tick)}
  have reset : Function.update F.R (r 2) [] = B.R := by
    rw [show Function.update F.R (r 2) [] = Function.update (Function.update D.R (r 2) []) (r 1) _ from
      Function.update_comm (r.injective.ne (by decide : (1 : Fin 6) ≠ 2)) ..]
    simp [D,B,← empty 2 (by decide)]
  have core := Exec.seq (Exec.seq decode divide) clear
  have bound : n+m+(2*x+2)+1 ≤ 23*x+13 := by
    have size := (Nat.size_le.mpr Nat.lt_two_pow_self : x.size ≤ x)
    omega
  refine ⟨z,_,final.trans (same.trans user),bound,?_⟩
  apply Exec.seq core
  change Exec body _ (mk z {F with R := Function.update F.R (r 2) []}) 1 _
  rw [reset]
  cases pred with
  | false => simpa [childCount,B] using (Exec.act (body := body) .done (mk z B))
  | true =>
    apply (Exec.act (body := body) (.pop (.rt (r 1)) (fun v _ => v) .done) (mk z B)).cast rfl
    simp [B,Action.run,update_rt,List.tail_replicate]

def childCountSlots (width : Bool) : Fin 6 ↪ Fin 8 :=
  ⟨if width then ![0,2,4,5,6,7] else ![1,3,4,5,6,7],by cases width <;> decide⟩

/-- Ports 0 and 1 read the binary width and row headers. Ports 2 and 3
receive the next predecessor clock and the number of rows in one role. -/
noncomputable def prepareChildCounts {T Q : ℕ} {P U : Type} (r : Fin 8 ↪ Fin T) : Pr P T Q prime U :=
  (childCount ((childCountSlots true).trans r) 64 true).seq (childCount ((childCountSlots false).trans r) 142080 false)

theorem prepareChildCounts_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 8 ↪ Fin T) (batch : Descriptor) (u : HS T Q prime U) (S : Stacks T prime)
    (width : S.R (r 0) = (Routines.hdr batch 3).map bitSymbol)
    (rows : S.R (r 1) = (Routines.hdr batch 1).map bitSymbol)
    (empty : ∀ j : Fin 8, 2 ≤ j.val → S.R (r j) = []) :
    let clock := batch.width/64-1
    let count := batch.rows/142080
    ∃ z k, z.user = u.user ∧ k ≤ 23*(batch.width+batch.rows)+26 ∧
      Exec body (prepareChildCounts r) (mk u S) k
        (mk z {S with R := Function.update (Function.update S.R (r 2) (List.replicate clock Node.tick)) (r 3) (List.replicate count Node.tick)}) := by
  intro clock count
  have high (mode : Bool) (j : Fin 6) (hj : 1 ≤ j.val) : 2 ≤ ((childCountSlots mode) j).val := by
    revert hj
    cases mode <;> fin_cases j <;> decide
  have widthWord : S.R (r 0) = binSyms batch.width.size batch.width := width.trans (canonicalBits_symbols _)
  have rowWord : S.R (r 1) = binSyms batch.rows.size batch.rows := rows.trans (canonicalBits_symbols _)
  obtain ⟨v,n,user,paid,first⟩ := childCount_exec body ((childCountSlots true).trans r) 64 (by decide) true
    batch.width u S widthWord (fun j hj => empty _ (high true j hj))
  let D := {S with R := Function.update S.R (r 2) (List.replicate clock Node.tick)}
  have keep (j : Fin 6) : D.R (r (childCountSlots false j)) = S.R (r (childCountSlots false j)) :=
    Function.update_of_ne (r.injective.ne (by fin_cases j <;> decide)) ..
  obtain ⟨z,m,same,time,second⟩ := childCount_exec body ((childCountSlots false).trans r) 142080 (by decide) false
    batch.rows v D ((keep 0).trans rowWord) (fun j hj => (keep j).trans (empty _ (high false j hj)))
  exact ⟨z,n+m,same.trans user,by omega,Exec.seq first second⟩

/-- Locate both source headers and six temporary tapes on the replay bank. -/
def directoryChildCountBank (K T : ℕ) (room : 6 ≤ T) : Fin 8 ↪ Fin (66+(K+3+T)) where
  toFun j := ⟨if j.val = 0 then 36 else if j.val = 1 then 66+K+1 else 66+K+3+(j.val-2),by split_ifs <;> omega⟩
  inj' := by
    intro j l eq
    apply Fin.ext
    have h := congrArg Fin.val eq
    dsimp only at h
    split_ifs at h <;> omega

theorem directoryChildCountBank_ready {K T N : ℕ} (room : 6 ≤ T) (replay : Fin (66+(K+3+T)) ↪ Fin N)
    (batch : Descriptor) (S : Stacks N prime) (ready : StoppedChartReady K T batch (embStk replay S)) :
    let r := (directoryChildCountBank K T room).trans replay
    S.R (r 0) = (Routines.hdr batch 3).map bitSymbol ∧ S.R (r 1) = (Routines.hdr batch 1).map bitSymbol ∧
      ∀ j : Fin 8, 2 ≤ j.val → S.R (r j) = [] := by
  intro r
  refine ⟨ready.1 3,ready.1 1,?_⟩
  intro j hj
  have place : directoryChildCountBank K T room j = stoppedChartPrivate K T ⟨j.val-2,by omega⟩ := by
    apply Fin.ext
    change (if j.val = 0 then 36 else if j.val = 1 then 66+K+1 else 66+K+3+(j.val-2)) = 66+K+3+(j.val-2)
    split_ifs <;> omega
  change S.R (replay (directoryChildCountBank K T room j)) = []
  rw [place]
  exact (ready.2 _).2

noncomputable def childCountState {T : ℕ} (r : Fin 8 ↪ Fin T) (batch : Descriptor) (S : Stacks T prime) : Stacks T prime :=
  {S with R := Function.update (Function.update S.R (r 2) (List.replicate (batch.width/64-1) Node.tick)) (r 3) (List.replicate (batch.rows/142080) Node.tick)}

/-- The two physical count tapes supply the corresponding scanner metadata
words at the child's own precision, for every choice of directory labels. -/
theorem childCountState_entryWords {T : ℕ} (r : Fin 8 ↪ Fin T) (batch : Descriptor)
    (S : Stacks T prime) (w rows : ℕ) (width : batch.width = 64*(w+1))
    (split : batch.rows = 142080*rows) (root : Bool) (weights : Fin 64 → ZMod (prime^(w+1)))
    (prefixWidth : ℕ) (prefixes : List (Fin (prime+4))) :
    let words := ordinaryEntryWords (batch.between*batch.afterD) batch.beforeRows rows batch.beforeH
      root weights prefixWidth prefixes
    (childCountState r batch S).R (r 2) = words 45 ∧
      (childCountState r batch S).R (r 3) = words 30 := by
  have clock : batch.width/64-1 = w := by omega
  have count : batch.rows/142080 = rows := by omega
  simp [childCountState, ordinaryEntryWords, clock, count, Node.tick]

/-- Lend the decoded counts to a recursive body and release them after it
returns. Both the setup and retirement are charged at the child's volume. -/
theorem withChildCounts_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 8 ↪ Fin T) (port : Fin T) (apart : ∀ j, r j ≠ port)
    (batch : Descriptor) (pos : 0 < volume prime batch) (core : Pr P T Q prime U)
    (budget : ℕ) (u : HS T Q prime U) (S : Stacks T prime) (word : Fin (volume prime batch) → ZMod 2)
    (width : S.R (r 0) = (Routines.hdr batch 3).map bitSymbol)
    (rows : S.R (r 1) = (Routines.hdr batch 1).map bitSymbol)
    (empty : ∀ j : Fin 8, 2 ≤ j.val → S.R (r j) = []) :
    let D := childCountState r batch S
    (∀ v : HS T Q prime U, ∃ y B k, y.user = v.user ∧ k ≤ budget ∧ Exec body core (mk v D) k (mk y B) ∧
      RecordPayload port (fun _ => blank) 0 word B ∧ ∀ j, j ≠ port → B.L j = D.L j ∧ B.R j = D.R j) →
    ∃ z F k, z.user = u.user ∧ k ≤ budget+81*volume prime batch ∧
      Exec body (((prepareChildCounts r).seq core).seq (Prog.seqList ([r 2,r 3].map WordCmd.dropR)))
        (mk u S) k (mk z F) ∧ RecordPayload port (fun _ => blank) 0 word F ∧
      ∀ j, j ≠ port → F.L j = S.L j ∧ F.R j = S.R j := by
  intro D child
  let clock := batch.width/64-1
  let count := batch.rows/142080
  obtain ⟨v,n,user,paid,prep⟩ := prepareChildCounts_exec body r batch u S width rows empty
  obtain ⟨y,B,k,same,time,run,out,frame⟩ := child v
  obtain ⟨z,F,last,erase,left,right⟩ := retire_exec body [r 2,r 3] (by simp) y B
  have clockLen : (B.R (r 2)).length = clock := by rw [(frame _ (apart 2)).2]; simp [D,childCountState,clock]
  have rowsLen : (B.R (r 3)).length = count := by rw [(frame _ (apart 3)).2]; simp [D,childCountState,count]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,clockLen,rowsLen] at erase
  have hp := LeafCore.positive_of_volume pos
  have widthSize : batch.width ≤ volume prime batch := RecursiveHeaderBounds.values_le_volume Shared50ModularControl.prime_prime.two_le batch hp 3
  have rowsSize : batch.rows ≤ volume prime batch := RecursiveHeaderBounds.values_le_volume Shared50ModularControl.prime_prime.two_le batch hp 1
  have clockSize : clock ≤ batch.width := (Nat.sub_le ..).trans (Nat.div_le_self ..)
  have countSize : count ≤ batch.rows := Nat.div_le_self ..
  refine ⟨z,F,_,last.trans (same.trans user),?_,Exec.seq (Exec.seq prep run) erase,?_,?_⟩
  · omega
  · intro t
    change readAt blank (F.L port) (F.R port) (t-0) = _
    rw [left,right,if_neg (by simp [(apart 2).symm,(apart 3).symm])]
    exact out t
  · intro j ne
    refine ⟨(congrFun left j).trans (frame j ne).1,?_⟩
    rw [right]
    by_cases a : j = r 2
    · subst j; simp [empty 2 (by decide)]
    by_cases b : j = r 3
    · subst j; simp [empty 3 (by decide)]
    simpa [a,b,D,childCountState,Function.update_of_ne] using (frame j ne).2

end IntegerMultBounds.MathlibTM2.M6.BitNode
