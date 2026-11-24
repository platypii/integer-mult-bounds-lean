module

public import IntegerMultBounds.MathlibTM2.M6.BitIdleWindowTraversal

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback SweepFile M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout

/-- Give an in-place owner traversal its two volume counters and materialize
the returned words for the next packed stage. -/
theorem packedOwnerTraversal {P U : Type} {T Q : ℕ} (owners : Fin 142081 ↪ Fin T)
    (body : P → Pr P T Q prime U) (worker : Pr P T Q prime U) :
    let bank := Fin.castAddEmb 2 (n := T)
    let fan := stageFan owners
    let place := Exit.chart 0 (T+2)
    let host := fun f => embProg place id (embProg bank id (body f))
    ∃ code, ∀ {V : ℕ} (prepared : Stacks (Exit.size 0 (T+2)) prime) (price : ℕ)
      (effect : (Fin 142081 → Fin V → ZMod 2) → (Fin 142081 → Fin V → ZMod 2) → Prop),
      (∀ t, (∀ k, place k ≠ t) → prepared.L t = [] ∧ prepared.R t = []) →
      (∀ x u S, (∀ r, RecordPayload (owners r) (fun _ => blank) 0 (x r) S) →
        (∀ t, (∀ r, owners r ≠ t) → S.L t = prepared.L (place (bank t)) ∧ S.R t = prepared.R (place (bank t))) →
        ∃ y F z n, Exec body worker (mk u S) n (mk z F) ∧ CleanupBound S F n price ∧
          z.user = u.user ∧ (∀ r, RecordPayload (owners r) (fun _ => blank) 0 (y r) F) ∧ effect x y) →
      PackedPieceHandoffWithCharge cleanupWeight V effect host code (fan.trans place) (returnedFan fan)
        prepared
        (price+(142081*(10*V+10)+1)) := by
  intro bank fan place host
  have shared (r : Fin 142081) : fan (r.castAdd 2) = bank (owners r) := by
    simp [fan,bank,stageFan,@finSumFinEquiv_symm_apply_castAdd 142081 2]
  have counter (j : Fin 2) : fan (j.natAdd 142081) = j.natAdd T := by
    simp [fan,stageFan,@finSumFinEquiv_symm_apply_natAdd 142081 2]
  obtain ⟨code,pack⟩ := flatWordStageWithSeedCharge fan (fun f => embProg bank id (body f)) (embProg bank id worker)
  refine ⟨code,?_⟩
  intro V prepared price effect blankOutside run
  let seed := embStk place prepared
  have sameStacks : flatStageSeed seed = prepared := by
    have onOrOff (f : Fin (Exit.size 0 (T+2)) → List (Fin (prime+4)))
        (empty : ∀ t, (∀ k, place k ≠ t) → f t = []) :
        Function.extend place (f ∘ place) (fun _ => []) = f := by
      funext t
      by_cases h : ∃ k, place k = t
      · obtain ⟨k,rfl⟩ := h
        exact place.injective.extend_apply ..
      · rw [Function.extend_apply' _ _ _ h,empty t (fun k eq => h ⟨k,eq⟩)]
    have l := onOrOff prepared.L (fun t h => (blankOutside t h).1)
    have r := onOrOff prepared.R (fun t h => (blankOutside t h).2)
    unfold flatStageSeed
    change Stacks.mk prepared.inp prepared.out (Function.extend place (prepared.L ∘ place) (fun _ => []))
      (Function.extend place (prepared.R ∘ place) (fun _ => [])) = prepared
    rw [l,r]
  rw [← sameStacks]
  apply pack
  intro x u S words stock
  obtain ⟨y,E,b,n,exec,paid,user,out,result⟩ := run x (embDn bank u) (embStk bank S) (by
    intro r
    have h := fanPayload words.helperFan r
    rw [shared] at h
    exact h) (by
    intro t away
    have outside (k) : fan k ≠ bank t := by
      induction k using Fin.addCases with
      | left r => rw [shared]; exact bank.injective.ne (away r)
      | right j => rw [counter]; exact suffixApart j t
    exact stock _ outside)
  obtain ⟨z,F,lifted,_,same,view,off⟩ := exec_emb (ι := id) (body' := fun f => embProg bank id (body f)) bank.injective (fun _ => rfl) exec u rfl S rfl
  rw [← view] at paid out
  refine ⟨z,F,n,y,lifted,CleanupBound.place bank off paid,same.trans user,?_,result⟩
  apply helperFan_of_payloads words.helperFan
  · intro r
    rw [shared]
    exact out r
  · intro j
    rw [counter]
    exact off _ (fun t => (suffixApart j t).symm)

/-- Run the cutoff window on a packed stage and return exact owner words and
volume counters. Setup and handoff execute in the same procedure table. -/
theorem compiledIdleWindowHandoff [M8.Machine.Net] {P U : Type} {N Q : ℕ}
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
      (src dst : Fin (142081+2) ↪ Fin T) (master : Fin 12 ↪ Fin T) (seedRate fixed base swaps : ℕ)
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
      PackedPieceHandoffWithCharge cleanupWeight p.cells
        (fun x y => ∀ j : Fin (p.idleWidth*142080),
          let addr := fun v => flatWindowEquiv (p.w+1) (p.idleWidth*142080) (windowState (p.w+1) v,j)
          readRoles addr y = (Piece.remainder i.val).run (readRoles addr x))
        table code src dst E ((735*p.cells+(∑ j, branch j)+1)+(142081*(10*p.cells+10)+1)) := by
  intro Job Label
  obtain ⟨T,body,init,worker,owners,master,seedRate,fixed,base,swaps,minimum,C,nonneg,pos,build⟩ :=
    compiledIdleWindow family column swapCap capacity headerCap i
  let bank := Fin.castAddEmb 2 (n := T)
  let fan := stageFan owners
  let place := Exit.chart 0 (T+2)
  let inner := fun f => embProg bank id (body f)
  let host := fun f => embProg place id (inner f)
  let setup := embProg place id (embProg bank id init)
  obtain ⟨code,pack⟩ := packedOwnerTraversal owners body worker
  refine ⟨_,host,setup,code,fan.trans place,returnedFan fan,(master.trans bank).trans place,
    seedRate,fixed,base,swaps,minimum,C,nonneg,pos,?_⟩
  intro D enough p blocks positive rows align child fuel children branch u S words fresh
  let v := embDn place u
  let B := embStk place S
  obtain ⟨a,E,n,exec,user,paid,run⟩ := build D enough p blocks positive rows align children
    (embDn bank v) (embStk bank B) words (fun t away => fresh (place (bank t))
      (fun k => place.injective.ne (bank.injective.ne (away k))))
  obtain ⟨b,F,innerRun,_,bu,innerView,offBank⟩ := exec_emb (ι := id) (body' := inner) bank.injective
    (fun _ => rfl) exec v rfl B rfl
  obtain ⟨z,G,outerRun,_,zu,outerView,offPlace⟩ := exec_emb (ι := id) (body' := host) place.injective
    (fun _ => rfl) innerRun u rfl S rfl
  rw [← innerView] at paid run
  have cost := CleanupBound.place bank offBank paid
  rw [← outerView] at cost run
  refine ⟨z,G,n,outerRun,zu.trans (bu.trans user),CleanupBound.place place offPlace cost,?_⟩
  apply pack
  · intro t away
    have off := offPlace t away
    have blank := fresh t (fun k => away (bank (master k)))
    exact ⟨off.1.trans blank.1,off.2.trans blank.2⟩
  · intro x u S words fresh
    obtain ⟨y,F,z,n,exec,paid,user,out,action,_⟩ := run x u S words fresh
    exact ⟨y,F,z,n,exec,paid,user,out,action⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
