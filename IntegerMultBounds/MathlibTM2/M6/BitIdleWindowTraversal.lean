module

public import IntegerMultBounds.MathlibTM2.M6.BitIdleWindowBranch

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout

/-- Execute in physical copy order. Shared headers and scratch remain exactly
as they were at entry, so every branch can borrow the same workspace. -/
theorem traverseIdleRecords {P U : Type} {T Q w W : ℕ} (i : Fin 9) (body : P → Pr P T Q prime U)
    (fan : Fin 142081 ↪ Fin T) (code : Fin idleCopies.length → Pr P T Q prime U)
    (price : Fin idleCopies.length → ℕ) (S : Stacks T prime) (u : HS T Q prime U)
    (x : Fin 142081 → Fin ((prime^w)^128*W) → ZMod 2)
    (live : ∀ r, RecordPayload (fan r) (fun _ => blank) 0 (x r) S)
    (each : ∀ j, let k := idleCopies[j.val]
      ∀ word v D, RecordPayload (fan (idleTape i k)) (fun _ => blank) 0 word D →
      (∀ t, (∀ r, fan r ≠ t) → D.L t = S.L t ∧ D.R t = S.R t) →
      ∃ z F n y, Exec body (code j) (mk v D) n (mk z F) ∧ z.user = v.user ∧ CleanupBound D F n (price j) ∧
        RecordPayload (fan (idleTape i k)) (fun _ => blank) 0 y F ∧ parentIntervalRead i k.2 w W word y ∧
        ∀ t, t ≠ fan (idleTape i k) → F.L t = D.L t ∧ F.R t = D.R t) :
    ∃ y F z n, Exec body (Prog.seqList (idleCopies.map (fun k => code (idleCopyIndex k)))) (mk u S) n (mk z F) ∧
      CleanupBound S F n ((∑ j, price j)+1) ∧ z.user = u.user ∧
      (∀ r, RecordPayload (fan r) (fun _ => blank) 0 (y r) F) ∧
      (∀ j : Fin W, let addr := fun v => flatWindowEquiv w W (windowState w v,j)
        readRoles addr y = (Piece.remainder i.val).run (readRoles addr x)) ∧
      ∀ t, (∀ r, fan r ≠ t) → F.L t = S.L t ∧ F.R t = S.R t := by
  classical
  let invariant := fun (data : Fin 142081 → Fin ((prime^w)^128*W) → ZMod 2) (D : Stacks T prime) =>
    (∀ r, RecordPayload (fan r) (fun _ => blank) 0 (data r) D) ∧
    ∀ t, (∀ r, fan r ≠ t) → D.L t = S.L t ∧ D.R t = S.R t
  obtain ⟨y,F,z,n,exec,paid,user,final,actions,off⟩ := idleCopiesWithPotential i body
    (fun k => code (idleCopyIndex k)) (fun k => (price (idleCopyIndex k) : ℝ)) (fun _ _ _ => True)
    (fun _ => invariant) (fun k => parentIntervalRead i k.2 w W)
    (fun (js : {ls : List (Fin T) // ls.Nodup}) D => (tapeCharge cleanupWeight js.val D : ℝ)) (by
      intro k past rest data D v _ state _
      have run := each (idleCopyIndex k)
      simp only [idleCopyIndex_get] at run
      obtain ⟨z,F,n,a,exec,user,paid,out,read,frame⟩ := run _ v D (state.1 _) state.2
      refine ⟨Function.update data (idleTape i k) a,F,z,n,exec,?_,user,⟨?_,?_⟩,fun _ _ _ => trivial,?_,
        fun r ne => Function.update_of_ne ne ..⟩
      · intro js
        exact_mod_cast paid js.val js.property
      · intro r
        by_cases eq : r = idleTape i k
        · subst r
          simpa only [Function.update_self] using out
        · rw [Function.update_of_ne eq]
          have keep := frame _ (fan.injective.ne eq)
          intro t
          simp only [keep.1,keep.2]
          exact state.1 r t
      · intro t away
        have keep := frame _ (away _).symm
        have old := state.2 t away
        exact ⟨keep.1.trans old.1,keep.2.trans old.2⟩
      · simpa only [Function.update_self] using read)
    x S u ⟨live,fun _ _ => ⟨rfl,rfl⟩⟩ (fun _ => trivial)
  refine ⟨y,F,z,n,exec,?_,user,final.1,parentIdleWindow_read i w W x y actions off,final.2⟩
  intro js nd
  have h := paid ⟨js,nd⟩
  change n+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+((∑ j, price j)+1)
  rw [← sumIndexed idleCopies idleCopyIndex idleCopyIndex_at price]
  apply (Nat.cast_le (α := ℝ)).mp
  simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_list_sum,List.map_map,Function.comp_def,add_assoc] using h

/-- Prepare the shared window, then run every scheduled branch on the loaded
parent fan. Only the selected branch contributes to each occurrence's bill. -/
theorem compiledIdleWindow [M8.Machine.Net] {P U : Type} {N Q : ℕ}
    {body : P → Pr P N Q prime U} {dst : Fin (142081+2) ↪ Fin N} {leafRate : ℝ}
    {permits : {c : CutoffNodeInput // c.cutoff < c.node.width} → ℕ → ℕ → Prop}
    (family : RecordTreeFamily Subtype.val body dst leafRate permits)
    (column : columnCapacity ≤ Q) (swapCap : (@rowSwapBlock BinaryRadixEqualShared.supplierNet).states ≤ Q)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (headerCap : (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080) ≤ Q)
    (i : Fin 9) :
    let Job := Fin idleCopies.length
    let Label := (Job ⊕ (Σ _ : Job, Option (Empty ⊕ P))) ⊕ Job
    ∃ (T : ℕ) (table : Label → Pr Label T Q prime U) (setup code : Pr Label T Q prime U)
      (fan : Fin 142081 ↪ Fin T) (master : Fin 12 ↪ Fin T) (seedRate fixed base swaps : ℕ)
      (minimum C : ℝ), 0 ≤ minimum ∧ 0 ≤ C ∧ ∀ D, minimum ≤ D →
      ∀ (p : CutoffNodeInput) blocks, p.root.Positive → 142080^(p.depth+1) ∣ p.root.rows →
      p.root.beforeH = blocks*prime^(64*p.root.width) →
      let child j := scheduledChild prime p.node (idleDirectoryIndex (i,j))
      let fuel := p.depth-(p.path.length+1)
      (∀ j, p.cutoff < (child j).width → ∀ (x : {c : CutoffNodeInput // c.cutoff < c.node.width}),
        x.val.root = p.root → x.val.path = p.path++[idleDirectoryIndex (i,j)] → x.val.cutoff = p.cutoff →
        ∀ k : Fin nodeChildren5.length, let d := scheduledChild prime (child j) k
        p.cutoff < d.width → permits x k.val (cutoffTreeBudget D leafRate p.cutoff (fuel-1) d)) →
      let branch j := if p.cutoff < (child j).width then idleRecordOverhead p fixed base swaps+
        cutoffTreeBudget D leafRate p.cutoff fuel (child j)
        else ⌊C*((child j).width : ℝ)^M8.Machine.BudgetBound.tau*volume prime (child j)⌋₊
      ∀ u S, (∀ k, S.R (master k) = nodeSeedWords p k) →
      (∀ t, (∀ k, master k ≠ t) → S.L t = [] ∧ S.R t = []) →
      ∃ v E m, Exec table setup (mk u S) m (mk v E) ∧ v.user = u.user ∧ CleanupBound S E m (seedRate*p.cells) ∧
      ∀ (x : Fin 142081 → Fin p.cells → ZMod 2) a G,
        (∀ r, RecordPayload (fan r) (fun _ => blank) 0 (x r) G) →
        (∀ t, (∀ r, fan r ≠ t) → G.L t = E.L t ∧ G.R t = E.R t) →
        ∃ y F z n, Exec table code (mk a G) n (mk z F) ∧ CleanupBound G F n (735*p.cells+(∑ j, branch j)+1) ∧
          z.user = a.user ∧ (∀ r, RecordPayload (fan r) (fun _ => blank) 0 (y r) F) ∧
          (∀ j : Fin (p.idleWidth*142080), let addr := fun v => flatWindowEquiv (p.w+1) (p.idleWidth*142080) (windowState (p.w+1) v,j)
            readRoles addr y = (Piece.remainder i.val).run (readRoles addr x)) ∧
          ∀ t, (∀ r, fan r ≠ t) → F.L t = G.L t ∧ F.R t = G.R t := by
  intro Job Label
  obtain ⟨H,fan,master,raw,fields,scratch,active,init,seedRate,fixed,base,swaps,minimum,nonneg,
    payload,rawOff,fieldOff,scratchOff,prepare,large⟩ := preparedIdleDirectory family swapCap capacity headerCap i
  obtain ⟨K,C,table,code,pos,installed,run⟩ := dispatchIdleWindow column capacity i active Sum.inl raw fields scratch
  let bank := Fin.castAddEmb K (n := H)
  let owners := fan.trans bank
  refine ⟨H+K,table,embProg bank Sum.inl init,Prog.seqList (idleCopies.map fun k => code (idleCopyIndex k)),
    owners,master.trans bank,seedRate,fixed,base,swaps,minimum,C,nonneg,pos,?_⟩
  intro D enough p blocks positive rows align child fuel children branch u S words empty
  obtain ⟨b,B,m,exec,user,paid,ready,roles,fresh,_⟩ := prepare p (embDn bank u) (embStk bank S) words
    (fun t away => empty (bank t) (fun k => bank.injective.ne (away k)))
  obtain ⟨v,E,lifted,_,last,view,off⟩ := exec_emb bank.injective installed exec u rfl S rfl
  rw [← view] at paid ready roles fresh
  rw [embDn_user] at user
  refine ⟨v,E,m,lifted,last.trans user,CleanupBound.place bank off paid,?_⟩
  intro x a G live loaded
  let price j := 2940*((prime^(p.w+1))^128*p.idleWidth)+branch j
  have toll : (∑ j, price j) = 735*p.cells+∑ j, branch j := dispatchIdleWindowBill p branch
  rw [← toll]
  apply traverseIdleRecords i table owners code price G a x live
  intro j k word v R input frame
  have keep (t) (ne : ∀ r, owners r ≠ t) : R.L t = E.L t ∧ R.R t = E.R t :=
    ⟨(frame t ne).1.trans (loaded t ne).1,(frame t ne).2.trans (loaded t ne).2⟩
  have slot : bank (raw j 24) = owners (idleTape i k) := congrArg bank (payload j)
  rw [← slot] at input ⊢
  apply run D leafRate permits fixed base swaps (large D enough) j p blocks positive rows align (children j)
    word v R input
  · intro h ne
    have same := keep (bank (raw j h)) (fun r => bank.injective.ne (rawOff j h ne r).symm)
    exact ⟨same.1.trans (ready j h ne).1,same.2.trans (ready j h ne).2⟩
  · intro t mem
    have same := keep (bank t) (fun r => bank.injective.ne (scratchOff t mem r).symm)
    exact ⟨same.1.trans (fresh t mem).1,same.2.trans (fresh t mem).2⟩
  · intro h
    exact (keep _ (fun r => bank.injective.ne (fieldOff j h r).symm)).2.trans (roles j h)
  · intro t
    have same := keep (t.natAdd H) (fun r => (suffixApart t (fan r)).symm)
    have old := off (t.natAdd H) (fun r => (suffixApart t r).symm)
    have blank := empty (t.natAdd H) (fun k => (suffixApart t (master k)).symm)
    exact ⟨same.1.trans (old.1.trans blank.1),same.2.trans (old.2.trans blank.2)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
