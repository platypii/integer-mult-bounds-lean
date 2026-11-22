module

public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedHelper

/-! Run the borrowed invocation on the permanent owner tapes of the packing program. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)

theorem ownerStage_fan_exec {V k T Q : ℕ} {P U : Type}
    (stage : SharedBankStage.Stage _ k prime (phaseOwners (N := V)))
    (bank : Fin stage.tapes ↪ Fin T) (fan : Fin (k+2) ↪ Fin T)
    (shared : ∀ i, bank (stage.slots i) = fan (i.castAdd 2))
    (apart : ∀ j : Fin 2, ∀ i, bank i ≠ fan (j.natAdd k))
    (fits : stage.states ≤ Q) (body : P → Pr P T Q prime U) (data : Fin k → Fin V → ZMod 2)
    (u : HS T Q prime U) (S : Stacks T prime)
    (ready : ChartPrivateReady stage (embStk bank S)) (rep : HelperFan fan data S) :
    ∃ z F m, Exec body (embProg bank (Empty.elim : Empty → P) (foreign (liftQ stage.program fits)))
        (mk u S) m (mk z F) ∧ m ≤ stage.cost*(stage.tapes+5)+6 ∧ z.user = u.user ∧
      HelperFan fan (stage.transform data) F ∧
      ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  have encoded (x : Fin k → Fin V → ZMod 2) (j : Fin k) : SparseRoleCircuit.encoded (a := prime) x j = fun i => SparseRoleCircuit.encode (x j i) := rfl
  have owners : RepT (phaseOwners data) (embStk (bank ∘ stage.slots) S).L (embStk (bank ∘ stage.slots) S).R := by
    intro i z
    simpa only [phaseOwners,PointwiseRoleGate.bank,Tapes.append,Fin.addCases_left,embStk,Function.comp_apply,
      encoded,shared] using rep (i.castAdd 2) z
  obtain ⟨z,F,m,exec,cost,user,_,out,_,off⟩ := ownerStage_exec_emb stage bank fits body data u S ready owners
  refine ⟨z,F,m,exec,cost,user,?_,off⟩
  intro i
  refine Fin.addCases (fun i h => ?_) (fun j h => ?_) i
  · simpa only [phaseOwners,PointwiseRoleGate.bank,Tapes.append,Fin.addCases_left,embStk,Function.comp_apply,
      encoded,shared] using out i h
  · obtain ⟨left,right⟩ := off _ (apart j)
    simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_right,embStk,Function.comp_apply,left,right]
      using rep (j.natAdd k) h

/-- Reserve two control tapes beyond the actual stage, and use its existing
payload slots as the owner tapes of the packing program. -/
def stageFan {k t : ℕ} (slots : Fin k ↪ Fin t) : Fin (k+2) ↪ Fin (t+2) :=
  finSumFinEquiv.symm.toEmbedding.trans
    ((slots.sumMap (Function.Embedding.refl (Fin 2))).trans finSumFinEquiv.toEmbedding)

theorem borrowedCall_exec [M8.Machine.Net] (n : Fin 9) (p : Fin 32 × Fin 5)
    (w B K : ℕ) (hw : 0 < w) (hb : 0 < B) (hk : 0 < K) (engine : CopyTranspose := CopyTranspose.original) :
    let blocks := (prime^w)^112*B
    let V := (prime^w)^16*(blocks*prime^(64*(w*64))*K)
    ∃ stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
      let bank := Fin.castAddEmb 2 (n := stage.tapes)
      let fan := stageFan ⟨stage.slots,stage.slots_injective⟩
      ∀ {P U : Type} {Q : ℕ} (fits : stage.states ≤ Q) (body : P → Pr P (stage.tapes+2) Q prime U)
        data u S, ChartPrivateReady stage (embStk bank S) → HelperFan fan data S →
      ∃ z F m out, Exec body (embProg bank (Empty.elim : Empty → P) (foreign (liftQ stage.program fits)))
        (mk u S) m (mk z F) ∧ m ≤ stage.cost*(stage.tapes+5)+6 ∧ z.user = u.user ∧
        HelperFan fan out F ∧ BorrowedStep n w blocks K p data out := by
  intro blocks V
  have positive : 0 < blocks := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hb
  obtain ⟨_,build⟩ := borrowedInvocation_stage n p.1 p.2 engine
  obtain ⟨stage,_,act,off⟩ := build w blocks K hw positive hk
  refine ⟨stage,?_⟩
  intro bank fan P U Q fits body data u S ready rep
  have shared (i) : bank (stage.slots i) = fan (i.castAdd 2) := by simp [fan,bank,stageFan,@finSumFinEquiv_symm_apply_castAdd 142081 2]
  have apart (j : Fin 2) (i) : bank i ≠ fan (j.natAdd 142081) := by
    simp [bank,fan,stageFan,@finSumFinEquiv_symm_apply_natAdd 142081 2]
    intro eq
    have h := congrArg Fin.val eq
    change i.val = stage.tapes+j.val at h
    omega
  obtain ⟨z,F,m,exec,paid,user,done,_⟩ := ownerStage_fan_exec stage bank fan shared apart fits body data u S ready rep
  exact ⟨z,F,m,stage.transform data,exec,paid,user,done,act data,off data⟩

open RecursiveInterchangeLayout (volume) in
/-- The two chart passes surrounding allocated COPY can be hosted separately.
Their interpreter overhead is uniform in the width and does not involve a
recursive call. -/
theorem borrowedChart_host [M8.Machine.Net] (n : Fin 9) (p : Fin 32 × Fin 5) (enter : Bool) :
    ∃ C : ℝ, ∀ w B K : ℕ, 0 < w → 0 < B → 0 < K →
    let v := copyLabelLayout w B K
    let V := volume prime v
    ∃ stage : SharedBankStage.Stage _ 142081 prime (copyOwners (v := v)),
      (∃ S : Stacks stage.tapes prime, ∀ j, (∀ i, stage.slots i ≠ j) → ∀ h, stage.metadata.tape j h =
        readAt blank (S.L j) (S.R j) (h-stage.metadata.head j)) ∧
      (∀ x (i : Fin 661), let A := registerChart w n i.val
        Cover.LabelPermutation.Transport v B w (fun g => g*(if enter then A.transpose else A))
          (M8.RevMachine.ext (x (ownerTape n p.1 p.2 i)))
          (M8.RevMachine.ext (stage.transform x (ownerTape n p.1 p.2 i)))) ∧
      (∀ x k, (∀ i, ownerTape n p.1 p.2 i ≠ k) → stage.transform x k = x k) ∧
      ∀ {P U : Type} {T Q : ℕ} (bank : Fin stage.tapes ↪ Fin T) (fan : Fin (142081+2) ↪ Fin T),
        (∀ i, bank (stage.slots i) = fan (i.castAdd 2)) →
        (∀ j : Fin 2, ∀ i, bank i ≠ fan (j.natAdd 142081)) →
        ∀ (fits : stage.states ≤ Q) (body : P → Pr P T Q prime U) data u S,
        (∀ j, (∀ i, stage.slots i ≠ j) → ∀ h, stage.metadata.tape j h =
          readAt blank (S.L (bank j)) (S.R (bank j)) (h-stage.metadata.head j)) →
        HelperFan fan data S →
        ∃ z F m, Exec body (embProg bank (Empty.elim : Empty → P) (foreign (liftQ stage.program fits)))
          (mk u S) m (mk z F) ∧ (m : ℝ) ≤ C*V*(w : ℝ)^M8.Machine.BudgetBound.tau ∧
          z.user = u.user ∧ HelperFan fan (stage.transform data) F ∧
          ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨coeff,tapes,build⟩ := borrowedRoute_fixed n p.1 p.2 enter
  let factor := tapes+5
  obtain ⟨C,bound⟩ := labelRoute_cost_bound ((coeff+661)*factor+6) (661*252*factor)
  refine ⟨C,?_⟩
  intro w B K hw hb hk v V
  obtain ⟨stage,count,initial,bill,reads,off⟩ := build w B K hw hb hk
  obtain ⟨seed,repSeed⟩ := copyChartStacks v (M8.Stage2Machine.Straight.words (Cover.LabelSchedule.base v w)) 142081 stage.tapes
  rw [← initial] at repSeed
  refine ⟨stage,⟨seed,?_⟩,reads,off,?_⟩
  · intro j unused h
    have away : ¬∃ i, stage.slots i = j := fun ⟨i,eq⟩ => unused i eq
    have tape := congrArg (fun A : Tapes stage.tapes prime => A.tape j h) (stage.strip_input 0)
    have head := congrArg (fun A : Tapes stage.tapes prime => A.head j) (stage.strip_input 0)
    simp only [SharedBank.strip,away,ite_false] at tape head
    rw [← tape,← head]
    exact repSeed j h
  intro P U T Q bank fan shared apart fits body data u S ready rep
  have same : @phaseOwners 142081 V = copyOwners (v := v) := by
    funext x
    apply congrArg₂ Tapes.mk
    · rfl
    · funext j
      exact (sourceWord_cast (v := v) rfl (x j)).symm
  have host := @ownerStage_fan_exec V 142081 T Q P U
  unfold ChartPrivateReady at host
  rw [same] at host
  obtain ⟨z,F,m,exec,paid,user,done,keep⟩ := host stage bank fan shared apart fits body data u S ready rep
  refine ⟨z,F,m,exec,le_trans ?_ (bound V w hw),user,done,keep⟩
  have pos : 1 ≤ V := by
    change 0 < V
    dsimp [V,v,copyLabelLayout,volume]
    have := Shared50ModularControl.prime_prime.pos
    positivity
  rw [count] at paid
  have time := paid.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (tapes+5) bill) 6)
  change m ≤ (coeff*V+661*(252*LeafCore.coreCost V (w*64)+1))*factor+6 at time
  exact_mod_cast (show m ≤ ((coeff+661)*factor+6)*V+661*252*factor*LeafCore.coreCost V (w*64) by
    have scale := Nat.mul_le_mul_left (661*factor+6) pos
    ring_nf at time scale ⊢
    omega)

open IntegerMultBounds.Networks.Certificates.PR589 in
/-- Execute allocated COPY windows in order. Only unvisited windows need
their private initialization; the common invariant survives every call. -/
theorem copyWindows_exec {T Q : ℕ} {P U X : Type} (body : P → Pr P T Q prime U)
    (n : Fin 9) (r : Fin 32) (d : Fin 5) (w B K : ℕ)
    (view : X → Fin 142081 → Fin (RecursiveInterchangeLayout.volume prime (copyLabelLayout w B K)) → ZMod 2)
    (ready : X → Stacks T prime → Prop) (saved : Fin Copy.lifecycles.length → Stacks T prime → Prop)
    (price : Fin Copy.lifecycles.length → ℕ)
    (window : ∀ i, ∃ code, ∀ x u S, ready x S → saved i S →
      ∃ z F t y, Exec body code (mk u S) t (mk z F) ∧ t ≤ price i ∧ z.user = u.user ∧ ready y F ∧
        CopyWindowEffect n r d Copy.lifecycles[i.val] w B K (view x) (view y) ∧
        ∀ j, j ≠ i → saved j S → saved j F)
    (ls : List (Fin Copy.lifecycles.length)) (unique : ls.Nodup) :
    ∃ code, ∀ x u S, ready x S → (∀ i ∈ ls, saved i S) →
      ∃ z F t y, Exec body code (mk u S) t (mk z F) ∧ t ≤ (ls.map price).sum+1 ∧ z.user = u.user ∧ ready y F ∧
        CopyScheduleEffect n r d w B K (ls.map fun i => Copy.lifecycles[i.val]) (view x) (view y) := by
  induction ls with
  | nil => exact ⟨.act .done,fun x u S ok _ => ⟨u,S,1,x,Exec.act ..,by simp,rfl,ok,rfl⟩⟩
  | cons i ls ih =>
    obtain ⟨code,run⟩ := window i
    obtain ⟨tail,rest⟩ := ih (List.nodup_cons.mp unique).2
    refine ⟨.seq code tail,?_⟩
    intro x u S ok fresh
    obtain ⟨v,D,k,a,exec,charge,user,mid,act,keep⟩ := run x u S ok (fresh i List.mem_cons_self)
    obtain ⟨z,F,m,y,done,paid,same,final,trace⟩ := rest a v D mid (fun j hj =>
      keep j (fun eq => (List.nodup_cons.mp unique).1 (eq ▸ hj)) (fresh j (List.mem_cons_of_mem _ hj)))
    refine ⟨z,F,_,y,Exec.seq exec done,?_,same.trans user,final,view a,act,trace⟩
    simp only [List.map_cons,List.sum_cons]
    omega

open RecursiveInterchangeLayout (volume) in
open M8.RevMachine Certificates.PR589 in
/-- Surround a COPY schedule on the permanent bank with its entry and exit
charts. The middle program's whole time allowance occurs once. -/
theorem borrowedCopy_host [M8.Machine.Net] (n : Fin 9) (p : Fin 32 × Fin 5) :
    ∃ C : ℝ, ∀ w B K : ℕ, 0 < w → 0 < B → 0 < K →
    let v := copyLabelLayout w B K
    let V := volume prime v
    ∃ stages : Bool → SharedBankStage.Stage _ 142081 prime (copyOwners (v := v)),
    (∀ k, ∃ S : Stacks (stages k).tapes prime, ∀ j, (∀ i, (stages k).slots i ≠ j) → ∀ h,
      (stages k).metadata.tape j h = readAt blank (S.L j) (S.R j) (h-(stages k).metadata.head j)) ∧
    ∀ {P U : Type} {T Q : ℕ} (bank : ∀ k, Fin (stages k).tapes ↪ Fin T) (fan : Fin (142081+2) ↪ Fin T),
      (∀ k i, bank k ((stages k).slots i) = fan (i.castAdd 2)) →
      (∀ k (j : Fin 2) i, bank k i ≠ fan (j.natAdd 142081)) →
      ∀ (fits : ∀ k, (stages k).states ≤ Q) (body : P → Pr P T Q prime U)
        (price : ℕ) (saved : Stacks T prime → Prop) (middle : Pr P T Q prime U),
      let ready := fun k (S : Stacks T prime) => ∀ j, (∀ i, (stages k).slots i ≠ j) → ∀ h,
        (stages k).metadata.tape j h = readAt blank (S.L (bank k j)) (S.R (bank k j)) (h-(stages k).metadata.head j)
      let chart := fun k => embProg (bank k) (Empty.elim : Empty → P) (foreign (liftQ (stages k).program (fits k)))
      (∀ x u S, HelperFan fan x S → ready true S → saved S →
        ∃ z F m y, Exec body middle (mk u S) m (mk z F) ∧ m ≤ price ∧ z.user = u.user ∧
          HelperFan fan y F ∧ ready true F ∧ CopyScheduleEffect n p.1 p.2 w B K Copy.lifecycles x y) →
      ∀ (data : Fin 142081 → Fin V → ZMod 2) u S, ready false S → HelperFan fan data S →
      (∀ D : Stacks T prime, (∀ j, (∀ i, bank false i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j) →
        ready true D ∧ saved D) →
      ∃ z F m out, Exec body (.seq (chart false) (.seq middle (chart true))) (mk u S) m (mk z F) ∧
        (m : ℝ) ≤ C*V*(w : ℝ)^M8.Machine.BudgetBound.tau + price ∧ z.user = u.user ∧ HelperFan fan out F ∧
        (∀ g z, borrowedRead (B := B) (K := K) n p.1 p.2 g z out = borrowedScatter w (borrowedRead n p.1 p.2 g z data)) ∧
        ∀ k, k ≠ Fin.last 142080 → (∀ i, ownerTape n p.1 p.2 i ≠ k) → out k = data k := by
  choose coeff build using borrowedChart_host n p
  refine ⟨coeff false + coeff true,?_⟩
  intro w B K hw hb hk v V
  choose stages seed transport off run using fun k => build k w B K hw hb hk
  refine ⟨stages,seed,?_⟩
  intro P U T Q bank fan shared apart fits body price saved middle ready chart copies data u S start rep fresh
  obtain ⟨a,D,l,entry,li,au,atEntry,keep⟩ := run false (bank false) fan (shared false) (apart false)
    (fits false) body data u S start rep
  obtain ⟨b,G,m,mid,copy,mi,ba,atExit,exitReady,effect⟩ := copies _ a D atEntry (fresh D keep).1 (fresh D keep).2
  obtain ⟨z,F,r,leave,ri,zb,done,_⟩ := run true (bank true) fan (shared true) (apart true)
    (fits true) body mid b G exitReady atExit
  refine ⟨z,F,_,_,Exec.seq entry (Exec.seq copy leave),?_,zb.trans (ba.trans au),done,?_,?_⟩
  · simp only [Nat.cast_add]
    rw [add_mul,add_mul]
    have bound : (m : ℝ) ≤ price := by exact_mod_cast mi
    linarith
  · intro g cell
    funext i
    by_cases live : i < 661
    · simpa only [borrowedScatter,Copy.extendStored,dite_eq_left live] using
        borrowedScatter_read n p.1 p.2 (transport false data) effect (transport true mid) g cell ⟨i,live⟩
    · simp [borrowedRead,borrowedScatter,Copy.extendStored,live]
  · intro k live outside
    exact (off true mid k outside).trans ((copySchedule_other effect k live outside).trans (off false data k outside))

open Certificates.PR589 in
/-- Join the allocated scalar phases to the charted COPY on one host.
Only COPY changes address representation; the joins themselves cost no steps. -/
theorem borrowedPhases_exec {P U : Type} {T Q w B K : ℕ} (body : P → Pr P T Q prime U)
    (n : Fin 9) (p : Fin 32 × Fin 5) (left copy right : Pr P T Q prime U) :
    let V := (prime^w)^16*(B*prime^(64*(w*64))*K)
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n p.1 p.2,ownerTape_injective ..⟩
    let view := fun (a : Fin 142081 → Fin V → ZMod 2) k i => a k (Fin.cast (copyLabel_volume w B K) i)
    ∀ (x a b y : Fin 142081 → Fin V → ZMod 2) u S v D z F q G l m r,
      Exec body left (mk u S) l (mk v D) → Exec body copy (mk v D) m (mk z F) →
      Exec body right (mk z F) r (mk q G) →
      (∀ j, phaseRead owner a j = labelPhase w (sectionD++sectionA) (Frames.snapshot Frames.initialRefs) (phaseRead owner x j)) →
      (∀ g cell, borrowedRead n p.1 p.2 g cell (view b) =
        borrowedScatter w (borrowedRead n p.1 p.2 g cell (view a))) →
      (∀ j, phaseRead owner y j = labelPhase w (sectionB++sectionC) (Frames.scatterFinish Frames.beforeScatter) (phaseRead owner b j)) →
      (∀ k, (∀ i, owner i ≠ k) → a k = x k) →
      (∀ k, k ≠ Fin.last 142080 → (∀ i, owner i ≠ k) → view b k = view a k) →
      (∀ k, (∀ i, owner i ≠ k) → y k = b k) →
      Exec body (.seq left (.seq copy right)) (mk u S) (l+(m+r)) (mk q G) ∧
        BorrowedStep n w B K p x y := by
  intro V owner view x a b y u S v D z F q G l m r enter middle leave first scatter last offA offB offC
  refine ⟨Exec.seq enter (Exec.seq middle leave),?_,?_⟩
  · intro g cell
    have moved := scatter g cell
    simp only [view,borrowedRead_flat] at moved
    change phaseRead owner y (labelSpectator g cell) = _
    rw [last,moved,first]
  · intro k live outside
    apply (offC k outside).trans
    apply Eq.trans _ (offA k outside)
    funext i
    exact congrFun (offB k live outside) (Fin.cast (copyLabel_volume w B K).symm i) |>.trans (by simp [view])

open Cover.Fallback RecursiveInterchangeLayout Certificates.PR589 in
/-- The allocated rank-seven worker accepts the aligned block and tail used
by the borrowed sweep. Each window retains its own child record and budget. -/
theorem borrowedWindow_host [M8.Machine.Net] (n : Fin 9) (p : Fin 32 × Fin 5) (j : Fin Copy.lifecycles.length) :
    ∃ (T states : ℕ) (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (fan : Fin (142081+2) ↪ Fin T),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q → ∀ (body : P → Pr P T Q prime U) (f : P),
    ∃ base swaps leaf fixed : ℕ, ∀ (node : Descriptor) (w B rows : ℕ),
    node.width = 64*(w+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    let M := prime^(w+1)
    let K := node.beforeRows*rows*node.between*node.afterD
    let blocks := M^112*B
    let W := blocks*prime^(64*((w+1)*64))*K
    let V := M^16*W
    let desc := scheduledChild prime node (copyChildPosition (n,p,j))
    let view := fun (x : Fin 142081 → Fin V → ZMod 2) k i => x k (Fin.cast (copyLabel_volume (w+1) blocks K) i)
    0 < W → ∃ position : Fin (volume prime desc) ≃ Fin V,
      (∀ k, (position k).val = (CopyChildLayout.packActive desc k).val) ∧
      ∀ record, ∃ prepared : Stacks T prime, ∀ budget,
      ScheduledChildExec node desc w W ports record position body f budget →
      ∃ code, ∀ data u S, HelperFan fan data S →
        (∀ k, (∀ h, fan h ≠ k) → S.L k = prepared.L k ∧ S.R k = prepared.R k) →
        ∃ z F t out, Exec body code (mk u S) t (mk z F) ∧
          t ≤ (base+swaps*swapVolumeRate w)*V + leaf*M8.RevMachine.LeafCore.coreCost V ((w+1)*64) + fixed + budget ∧
          z.user = u.user ∧ HelperFan fan out F ∧
          CopyWindowEffect n p.1 p.2 Copy.lifecycles[j.val] (w+1) blocks K (view data) (view out) := by
  obtain ⟨T,states,ports,fan,build⟩ := scheduledCopyWindow_layout n p.1 p.2 j
  refine ⟨T,states,ports,fan,?_⟩
  intro P U Q fits body f
  obtain ⟨base,swaps,leaf,fixed,run⟩ := build fits body f
  refine ⟨base,swaps,leaf,fixed,?_⟩
  intro node w B rows width split label M K blocks W V desc view pos
  exact run node w B rows blocks K width split label (by dsimp [blocks,K,M]; ring) pos

end IntegerMultBounds.MathlibTM2.M6.BitNode
