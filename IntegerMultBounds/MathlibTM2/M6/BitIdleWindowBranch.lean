module

public import IntegerMultBounds.MathlibTM2.M6.BitPreparedIdleDirectory

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout IntervalDescriptor

/-- Compile the leaf branch at each occurrence on the same 72-register
dispatch layout as the active entry. Its budget uses the scheduled width. -/
theorem idleWindowLeafEntries [M8.Machine.Net] {Q : ℕ} {U : Type} (capacity : columnCapacity ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    ∃ (C : ℝ) (N : ℕ) (body : Unit → Pr Unit (72+N) Q prime U), 0 ≤ C ∧
      ∀ (i : Fin 9) (j : Fin idleCopies.length), ∃ code : Pr Unit (72+N) Q prime U,
      ∀ p : CutoffNodeInput, let bank := Fin.castAddEmb N (n := 72)
      let child := scheduledChild prime p.node (idleDirectoryIndex (i,j))
      ∀ (word : Fin p.cells → ZMod 2) u S,
      IdleDispatchReady bank p.w p.idleWidth p.root.width.size p.cutoff S →
      (∀ k : Fin N, S.L (k.natAdd 72) = [] ∧ S.R (k.natAdd 72) = []) →
      RecordPayload (bank 24) (fun _ => blank) 0 word S →
      ∃ z F n changed, Exec body code (mk u S) n (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F n ⌊C*(child.width : ℝ)^M8.Machine.BudgetBound.tau*volume prime child⌋₊ ∧
        RecordPayload (bank 24) (fun _ => blank) 0 changed F ∧
        parentIntervalRead i idleCopies[j.val].2 (p.w+1) (p.idleWidth*142080) word changed ∧
        ∀ k, k ≠ bank 24 → F.L k = S.L k ∧ F.R k = S.R k := by
  obtain ⟨C,N,body,nonneg,build⟩ := scheduledIdleInterval (U := U) capacity mergeCap
  refine ⟨C,N,body,nonneg,?_⟩
  intro i j
  obtain ⟨code,run⟩ := build i j
  refine ⟨code,?_⟩
  intro p bank child word u S ready free payload
  let e := idleInterval i idleCopies[j.val].2
  let lane := phaseIntervalChild (e.1+1) (e.2+1) (p.w+1) p.idleWidth 64
  let wide := {lane with afterD := lane.afterD*142080}
  have bounds := idleBounds i idleCopies[j.val].2
  have shape : wide = phaseIntervalChild (e.1+1) (e.2+1) (p.w+1) (p.idleWidth*142080) 64 := by
    simp only [wide,lane,phaseIntervalChild,Nat.mul_assoc]
  have size : volume prime wide = p.cells := (congrArg (volume prime) shape).trans
    (intervalChild_volume (Nat.succ_le_succ bounds.1) (Nat.succ_le_succ bounds.2) _ _)
  obtain ⟨position,_,coords,leaf⟩ := run p.node (p.w+1) p.groups (Nat.succ_pos _) p.width p.rows p.idlePositive
  have blank (k : Fin 72) (h : k.val ≠ 2 ∧ k.val ≠ 28 ∧ k.val ≠ 53 ∧ k.val ≠ 71 ∧ k.val ≠ 5 ∧ k.val ≠ 6)
      (ne : k ≠ 24) : S.L (bank k) = [] ∧ S.R (bank k) = [] := by
    obtain ⟨l,r⟩ := ready k ne
    exact ⟨l,r.trans (by simp [idleDispatchWord,h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2])⟩
  have clock : (S.R (bank 71)).length = p.w+1 := by rw [(ready 71 (by decide)).2]; simp [idleDispatchWord]
  obtain ⟨z,F,n,y,exec,paid,user,out,action,frame⟩ := leaf (fun k => word (k.cast size)) u S
    (ready 2 (by decide)).2 (ready 28 (by decide)).2 (ready 53 (by decide)).2 clock
    (fun k lo hi => (blank k (by omega) ((by decide : ∀ k : Fin 72, 59 ≤ k.val → k ≠ 24) k lo)).2)
    (recordPayload_castInput size _ _ _ payload) (ready 59 (by decide)).1
    (fun k => blank _ ((by decide : ∀ k, let v := (descriptorPorts k).val
      v ≠ 2 ∧ v ≠ 28 ∧ v ≠ 53 ∧ v ≠ 71 ∧ v ≠ 5 ∧ v ≠ 6) k)
      ((by decide : ∀ k, descriptorPorts k ≠ 24) k)) free
  have width : wide.width = child.width := by
    change ((e.2+1)-(e.1+1))*(p.w+1) = nodeChildren5.get (idleDirectoryIndex (i,j))*(p.node.width/64)
    rw [Nat.add_sub_add_right,p.width,Nat.mul_div_cancel_left _ (by decide),idleDirectoryIndex_rank]
  obtain ⟨changed,result,read⟩ := scheduledIdleParentRecord (bank 24) F i idleCopies[j.val].2 (p.w+1)
    (p.idleWidth*142080) child wide shape size position coords width word y out action
  exact ⟨z,F,n,changed,exec,user,paid,result,read,frame⟩

/-- The cutoff test runs on the occurrence's dispatch bank and returns the
original stacks to the selected branch. Equality selects the stopped entry. -/
theorem idleWindowBranch {A U : Type} {T Q : ℕ} (body : A → Pr A T Q prime U)
    (raw : Fin 72 ↪ Fin T) (i : Fin 9) (j : Fin idleCopies.length)
    (large leaf : Pr A T Q prime U) :
    ∃ code : Pr A T Q prime U, ∀ (p : CutoffNodeInput) u S,
      IdleDispatchReady raw p.w p.idleWidth p.root.width.size p.cutoff S →
      let child := scheduledChild prime p.node (idleDirectoryIndex (i,j))
      ∀ (result : Stacks T prime → Prop) (price : ℕ),
      (∀ v, ∃ z F n, Exec body (if p.cutoff < child.width then large else leaf) (mk v S) n (mk z F) ∧
        z.user = v.user ∧ CleanupBound S F n price ∧ result F) →
      ∃ z F n, Exec body code (mk u S) n (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F n (2940*((prime^(p.w+1))^128*p.idleWidth)+price) ∧ result F := by
  let index := idleDirectoryIndex (i,j)
  let rank := nodeChildren5.get index
  let reg := (Fin.natAddEmb 5 (m := 10)).trans (Fin.castLEEmb (by decide : 15 ≤ 72))
  let cmp := reg.trans raw
  refine ⟨(ordinaryCutoffTest cmp rank).seq (.cond (fun z => symBit (z.scan (cmp 7))) large leaf),?_⟩
  intro p u S ready child result price selected
  have scaled : (p.w+1)*rank = child.width := by
    change _ = rank*(p.node.width/64)
    rw [p.width,Nat.mul_div_cancel_left _ (by decide),Nat.mul_comm]
  have inherited := directoryDigits_bound prime p.root p.path
  have rootBound : p.node.width ≤ p.root.width := by unfold CutoffNodeInput.node; omega
  have rankFits : rank ≤ 64 := (nodeChildren5_bounds index).2.trans (by decide : 42 ≤ 64)
  have childBound : (p.w+1)*rank ≤ p.root.width :=
    (Nat.mul_le_mul_left _ rankFits).trans ((Nat.mul_comm (p.w+1) 64) ▸ p.width ▸ rootBound)
  have clock : (S.R (cmp 0)).length = p.w := by
    change (S.R (raw 5)).length = _
    rw [(ready 5 (by decide)).2]; simp [idleDispatchWord]
  have empty (k : Fin 10) (hk : 2 ≤ k.val) : S.R (cmp k) = [] := by
    have bounds : 7 ≤ (reg k).val ∧ (reg k).val ≤ 14 := (by decide : ∀ k : Fin 10,
      2 ≤ k.val → 7 ≤ (reg k).val ∧ (reg k).val ≤ 14) k hk
    refine (ready (reg k) ((by decide : ∀ k : Fin 10, reg k ≠ 24) k)).2.trans ?_
    simp [idleDispatchWord,show (reg k).val ≠ 2 by omega,show (reg k).val ≠ 28 by omega,
      show (reg k).val ≠ 53 by omega,show (reg k).val ≠ 71 by omega,show (reg k).val ≠ 5 by omega,
      show (reg k).val ≠ 6 by omega]
  obtain ⟨v,t,user,flag,paid,test⟩ := ordinaryCutoffTest_exec body cmp rank p.w p.root.width.size p.cutoff
    ((p.active.trans rootBound).trans_lt (Nat.lt_size_self _)) (Nat.size_le_size childBound)
    u S clock (ready 6 (by decide)).2 empty
  obtain ⟨z,F,n,run,last,bill,out⟩ := selected v
  have branch : Exec body (.cond (fun z => symBit (z.scan (cmp 7))) large leaf) (mk v S) (n+1) (mk z F) := by
    rw [scaled] at flag
    by_cases active : p.cutoff < child.width
    · exact Exec.cond_true (by simp [mk_var,flag,active]) (by simpa only [ite_eq_left active] using run)
    · exact Exec.cond_false (by simp [mk_var,flag,active]) (by simpa only [ite_eq_right active] using run)
  have compare := ordinaryChildComparison_volume_le p.root p.depth p.b p.cutoff rank p.w p.idleWidth
    p.levels p.base p.rootWidth p.stop (p.width ▸ p.active) rankFits p.idlePositive
  refine ⟨z,F,_,test.seq branch,last.trans user,?_,out⟩
  intro js nd
  have bound := bill js nd
  dsimp only at compare
  omega

/-- Install the stopped procedures alongside the active table. Every cutoff
decision now executes a concrete branch, with one shared bank for leaf work. -/
theorem dispatchIdleWindow [M8.Machine.Net] {A U : Type} {T Q : ℕ} (capacity : columnCapacity ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (i : Fin 9) (body : A → Pr A T Q prime U) (entry : Fin idleCopies.length → A)
    (raw : Fin idleCopies.length → Fin 72 ↪ Fin T) (fields : Fin idleCopies.length → Fin 6 ↪ Fin T)
    (scratch : List (Fin T)) :
    let Job := Fin idleCopies.length
    let Label := A ⊕ Job
    ∃ (K : ℕ) (C : ℝ) (table : Label → Pr Label (T+K) Q prime U) (code : Job → Pr Label (T+K) Q prime U),
      let bank := Fin.castAddEmb K (n := T)
      0 ≤ C ∧ (∀ f, table (.inl f) = embProg bank Sum.inl (body f)) ∧
      ∀ (D leafRate : ℝ) (permits) (fixed base swaps : ℕ),
      (∀ j, ScheduledIdleRecordRun body (.call (entry j)) (raw j) (fields j) scratch
        i j D leafRate permits fixed base swaps) →
      ∀ j (p : CutoffNodeInput) blocks, p.root.Positive → 142080^(p.depth+1) ∣ p.root.rows →
      p.root.beforeH = blocks*prime^(64*p.root.width) →
      let index := idleDirectoryIndex (i,j)
      let child := scheduledChild prime p.node index
      let fuel := p.depth-(p.path.length+1)
      (p.cutoff < child.width → ∀ (x : {c : CutoffNodeInput // c.cutoff < c.node.width}),
        x.val.root = p.root → x.val.path = p.path++[index] → x.val.cutoff = p.cutoff →
        ∀ k : Fin nodeChildren5.length, let d := scheduledChild prime child k
        p.cutoff < d.width → permits x k.val (cutoffTreeBudget D leafRate p.cutoff (fuel-1) d)) →
      ∀ (word : Fin p.cells → ZMod 2) u S,
        RecordPayload (bank (raw j 24)) (fun _ => blank) 0 word S →
        IdleDispatchReady ((raw j).trans bank) p.w p.idleWidth p.root.width.size p.cutoff S →
        (∀ t ∈ scratch, S.L (bank t) = [] ∧ S.R (bank t) = []) →
        (∀ k, S.R (bank (fields j k)) = (Routines.hdr (role p.node 142080) k).map bitSymbol) →
        (∀ k : Fin K, S.L (k.natAdd T) = [] ∧ S.R (k.natAdd T) = []) →
        ∃ z F n y, Exec table (code j) (mk u S) n (mk z F) ∧ z.user = u.user ∧
          CleanupBound S F n (2940*((prime^(p.w+1))^128*p.idleWidth) +
            if p.cutoff < child.width then idleRecordOverhead p fixed base swaps+cutoffTreeBudget D leafRate p.cutoff fuel child
            else ⌊C*(child.width : ℝ)^M8.Machine.BudgetBound.tau*volume prime child⌋₊) ∧
          RecordPayload (bank (raw j 24)) (fun _ => blank) 0 y F ∧
          parentIntervalRead i idleCopies[j.val].2 (p.w+1) (p.idleWidth*142080) word y ∧
          ∀ t, t ≠ bank (raw j 24) → F.L t = S.L t ∧ F.R t = S.R t := by
  classical
  intro Job Label
  obtain ⟨C,N,leafBody,nonneg,build⟩ := idleWindowLeafEntries (U := U) capacity mergeCap
  choose leaf runLeaf using build i
  let bank := Fin.castAddEmb (72+N) (n := T)
  let regs := Fin.castAddEmb N (n := 72)
  choose place links outside using fun j => adjacentStagePlacement (raw j) regs
  let table : Label → Pr Label (T+(72+N)) Q prime U := Sum.elim
    (fun f => embProg bank Sum.inl (body f)) (fun j => embProg (place j) (fun _ => Sum.inr j) (leafBody ()))
  let activeCode (j : Job) : Pr Label (T+(72+N)) Q prime U := embProg bank Sum.inl (.call (entry j) : Pr A T Q prime U)
  let leafCode (j : Job) : Pr Label (T+(72+N)) Q prime U := embProg (place j) (fun _ => Sum.inr j) (leaf j)
  choose code compare using fun j => idleWindowBranch table ((raw j).trans bank) i j (activeCode j) (leafCode j)
  refine ⟨72+N,C,table,code,nonneg,fun _ => rfl,?_⟩
  intro D leafRate permits fixed base swaps large j p blocks positive rows align index child fuel children word u S payload ready fresh roles empty
  let result := fun F : Stacks (T+(72+N)) prime => ∃ y, RecordPayload (bank (raw j 24)) (fun _ => blank) 0 y F ∧
    parentIntervalRead i idleCopies[j.val].2 (p.w+1) (p.idleWidth*142080) word y ∧
    ∀ t, t ≠ bank (raw j 24) → F.L t = S.L t ∧ F.R t = S.R t
  obtain ⟨z,F,n,exec,user,paid,y,out,read,frame⟩ := compare j p u S ready result
    (if p.cutoff < child.width then idleRecordOverhead p fixed base swaps + cutoffTreeBudget D leafRate p.cutoff fuel child
     else ⌊C*(child.width : ℝ)^M8.Machine.BudgetBound.tau*volume prime child⌋₊) (by
    intro v
    by_cases h : p.cutoff < child.width
    · rw [ite_eq_left h]
      obtain ⟨a,E,n,y,exec,user,paid,out,read,frame⟩ := large j p blocks positive rows align h (children h) word
        (embDn bank v) (embStk bank S) payload ready fresh roles
      obtain ⟨z,F,lifted,_,last,view,off⟩ := exec_emb bank.injective (body' := table) (ι := Sum.inl)
        (fun _ => rfl) exec v rfl S rfl
      rw [← view] at paid out frame
      refine ⟨z,F,n,lifted,last.trans user,?_,y,out,read,?_⟩
      · simpa only [ite_eq_left h] using CleanupBound.place bank off paid
      · intro t ne
        by_cases hit : ∃ k, bank k = t
        · obtain ⟨k,rfl⟩ := hit
          exact frame k (fun eq => ne (congrArg bank eq))
        · exact off t (fun k eq => hit ⟨k,eq⟩)
    · rw [ite_eq_right h]
      have link (k : Fin 72) : place j (regs k) = bank (raw j k) := links j k
      have localReady : IdleDispatchReady regs p.w p.idleWidth p.root.width.size p.cutoff (embStk (place j) S) := by
        intro k ne
        simpa only [embStk,Function.comp_apply,link,Function.Embedding.trans_apply] using ready k ne
      have localPayload : RecordPayload (regs 24) (fun _ => blank) 0 word (embStk (place j) S) := by
        intro t
        simpa only [embStk,Function.comp_apply,link] using payload t
      have clear (k : Fin N) := outside j (k.natAdd 72) (fun r => (suffixApart k r).symm)
      obtain ⟨a,E,n,y,exec,user,paid,out,read,frame⟩ := runLeaf j p word (embDn (place j) v) (embStk (place j) S)
        localReady (fun k => by simpa only [embStk,Function.comp_apply,clear] using empty (k.natAdd 72)) localPayload
      obtain ⟨z,F,lifted,_,last,view,off⟩ := exec_emb (place j).injective (body' := table) (ι := fun _ => Sum.inr j)
        (fun _ => rfl) exec v rfl S rfl
      rw [← view] at paid out frame
      refine ⟨z,F,n,lifted,last.trans user,?_,y,?_,read,?_⟩
      · simpa only [ite_eq_right h] using CleanupBound.place (place j) off paid
      · intro t
        rw [← link 24]
        exact out t
      · intro t ne
        by_cases hit : ∃ k, place j k = t
        · obtain ⟨k,rfl⟩ := hit
          exact frame k (fun eq => ne ((congrArg (place j) eq).trans (link 24)))
        · exact off t (fun k eq => hit ⟨k,eq⟩))
  exact ⟨z,F,n,y,exec,user,paid,out,read,frame⟩

/-- The comparisons over a full window add a linear toll. The remaining
sum contains precisely the branch chosen at each scheduled occurrence. -/
theorem dispatchIdleWindowBill (p : CutoffNodeInput) (price : Fin idleCopies.length → ℕ) :
    (∑ j, (2940*((prime^(p.w+1))^128*p.idleWidth)+price j)) =
      735*p.cells+∑ j, price j := by
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,idleCopies_length,nsmul_eq_mul,
    CutoffNodeInput.cells]
  ring

end IntegerMultBounds.MathlibTM2.M6.BitNode
