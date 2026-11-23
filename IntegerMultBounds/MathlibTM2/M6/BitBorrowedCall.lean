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

open IntegerMultBounds.Networks.Certificates.PR589 in
-- The routed COPY wrappers are available in 116e7160.
/-- Execute allocated COPY windows in order. Only unvisited windows need
their private initialization; the common invariant survives every call. -/
theorem scheduledWindows_exec {T Q : ℕ} {P U X : Type} (charged : Bool) (body : P → Pr P T Q prime U)
    (effect : Fin Copy.lifecycles.length → X → X → Prop)
    (trace : List (Fin Copy.lifecycles.length) → X → X → Prop)
    (empty : ∀ x, trace [] x x)
    (cons : ∀ i ls x y z, effect i x y → trace ls y z → trace (i :: ls) x z)
    (ready : X → Stacks T prime → Prop) (saved : Fin Copy.lifecycles.length → Stacks T prime → Prop)
    (price : Fin Copy.lifecycles.length → ℕ)
    (code : Fin Copy.lifecycles.length → Pr P T Q prime U)
    (window : ∀ i, ∀ x u S, ready x S → saved i S →
      ∃ z F t y, Exec body (code i) (mk u S) t (mk z F) ∧ workerCost charged S F t (price i) ∧ z.user = u.user ∧ ready y F ∧
        effect i x y ∧
        ∀ j, j ≠ i → saved j S → saved j F)
    (ls : List (Fin Copy.lifecycles.length)) (unique : ls.Nodup) :
    ∀ x u S, ready x S → (∀ i ∈ ls, saved i S) →
      ∃ z F t y, Exec body (ls.foldr (fun i tail => (code i).seq tail) (.act .done)) (mk u S) t (mk z F) ∧ workerCost charged S F t ((ls.map price).sum+1) ∧ z.user = u.user ∧ ready y F ∧
        trace ls x y := by
  induction ls with
  | nil => exact fun x u S ok _ => ⟨u,S,1,x,Exec.act ..,by cases charged <;> simp [workerCost,CleanupBound,Nat.add_comm],rfl,ok,empty x⟩
  | cons i ls ih =>
    have run := window i
    have rest := ih (List.nodup_cons.mp unique).2
    intro x u S ok fresh
    obtain ⟨v,D,k,a,exec,charge,user,mid,act,keep⟩ := run x u S ok (fresh i List.mem_cons_self)
    obtain ⟨z,F,m,y,done,paid,same,final,trace⟩ := rest a v D mid (fun j hj =>
      keep j (fun eq => (List.nodup_cons.mp unique).1 (eq ▸ hj)) (fresh j (List.mem_cons_of_mem _ hj)))
    refine ⟨z,F,_,y,Exec.seq exec done,?_,same.trans user,final,cons i ls x a y act trace⟩
    simpa only [List.map_cons,List.sum_cons,Nat.add_assoc] using workerCost.seq charge paid

open Certificates.PR589 Cover in
/-- An ordered trace of the individual COPY windows acts by the selected COPY
word on labels and fixes the owners outside the invocation. -/
theorem copyWindowTrace {w B K : ℕ} (n : Fin 9) (r : Fin 32) (d : Fin 5) :
    let V := (prime^w)^16*(B*prime^(64*(w*64))*K)
    let X := Fin 142081 → Fin V → ZMod 2
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
    ∀ x y : X, (List.finRange Copy.lifecycles.length).foldr (fun i next a =>
      ∃ b, CopyFanoutEffect n r d _ (List.getElem_mem (l := Copy.lifecycles) i.isLt) w B K a b ∧ next b)
      (fun a => a = y) x →
      (∀ g (cell : LabelEntry.Cell (copyLabelLayout w B K) B), phaseRead owner y (labelSpectator g cell) =
        Copy.run (selectedFrame w) Copy.lifecycles (phaseRead owner x (labelSpectator g cell))) ∧
      ∀ k, k ≠ Fin.last 142080 → (∀ j, owner j ≠ k) → y k = x k := by
  intro V X owner x y steps
  let trace := fun (ls : List (Fin Copy.lifecycles.length)) (x y : X) =>
    (∀ g (cell : LabelEntry.Cell (copyLabelLayout w B K) B),
      phaseRead owner y (labelSpectator g cell) = ls.foldl
        (fun a i => scatterWindow (selectedWord w) Copy.lifecycles[i.val] a) (phaseRead owner x (labelSpectator g cell))) ∧
    ∀ k, k ≠ Fin.last 142080 → (∀ j, owner j ≠ k) → y k = x k
  have fold (ls : List (Fin Copy.lifecycles.length)) (a : X) :
      ls.foldr (fun i next data => ∃ b, CopyFanoutEffect n r d _ (List.getElem_mem (l := Copy.lifecycles) i.isLt)
        w B K data b ∧ next b) (fun b => b = y) a → trace ls a y := by
    induction ls generalizing a with
    | nil =>
      intro eq
      subst a
      exact ⟨fun _ _ => rfl,fun _ _ _ => rfl⟩
    | cons i ls ih =>
      rintro ⟨b,act,rest⟩
      obtain ⟨tail,off⟩ := ih b rest
      refine ⟨fun g cell => ?_,fun k live outside => (off k live outside).trans (act.2.2.1 k live (fun j _ => outside j))⟩
      rw [tail g cell,phaseRead_fanout _ act]
      rfl
  obtain ⟨action,off⟩ := fold _ x steps
  refine ⟨?_,off⟩
  intro g cell
  have h := action g cell
  rw [← List.foldl_map (g := fun a life => scatterWindow (selectedWord w) life a) (f := fun i : Fin Copy.lifecycles.length => Copy.lifecycles[i.val]),
    ← List.ofFn_eq_map,List.ofFn_getElem] at h
  exact h.trans ((modular_scatter w).choose_spec.2.2.2.1 _)

open Certificates.PR589 Cover in
/-- Sequence the recursive fanouts directly on the permanent owner bank.
Every label sees the selected COPY word, and unrelated owners retain their data. -/
theorem commonWindows_exec {T Q w B K : ℕ} {P U : Type} (charged : Bool) (body : P → Pr P T Q prime U)
    (n : Fin 9) (r : Fin 32) (d : Fin 5) (fan : Fin (142081+2) ↪ Fin T)
    (saved : Fin Copy.lifecycles.length → Stacks T prime → Prop)
    (price : Fin Copy.lifecycles.length → ℕ) (code : Fin Copy.lifecycles.length → Pr P T Q prime U) :
    let V := (prime^w)^16*(B*prime^(64*(w*64))*K)
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
    let X := Fin 142081 → Fin V → ZMod 2
    (∀ i, ∀ (x : X) u S, HelperFan fan x S → saved i S →
      ∃ z F t y, Exec body (code i) (mk u S) t (mk z F) ∧ workerCost charged S F t (price i) ∧ z.user = u.user ∧ HelperFan fan y F ∧
        CopyFanoutEffect n r d _ (List.getElem_mem (l := Copy.lifecycles) i.isLt) w B K x y ∧
        ∀ j, j ≠ i → saved j S → saved j F) →
    ∀ (x : X) u S, HelperFan fan x S → (∀ i, saved i S) →
      ∃ z F t y, Exec body ((List.finRange _).foldr (fun i tail => (code i).seq tail) (.act .done)) (mk u S) t (mk z F) ∧ workerCost charged S F t ((List.ofFn price).sum+1) ∧
        z.user = u.user ∧ HelperFan fan y F ∧
        (∀ g (cell : LabelEntry.Cell (copyLabelLayout w B K) B),
          phaseRead owner y (labelSpectator g cell) =
            Copy.run (selectedFrame w) Copy.lifecycles (phaseRead owner x (labelSpectator g cell))) ∧
        ∀ k, k ≠ Fin.last 142080 → (∀ j, owner j ≠ k) → y k = x k := by
  intro V owner X window
  let trace := fun (ls : List (Fin Copy.lifecycles.length)) (x y : X) => ls.foldr (fun i next a =>
    ∃ b, CopyFanoutEffect n r d _ (List.getElem_mem (l := Copy.lifecycles) i.isLt) w B K a b ∧ next b) (fun a => a = y) x
  have run := scheduledWindows_exec charged body _ trace (fun _ => rfl)
    (fun _ _ _ y _ act tail => ⟨y,act,tail⟩) (HelperFan fan) saved price code window (List.finRange _) (List.nodup_finRange _)
  intro x u S rep fresh
  obtain ⟨z,F,t,y,exec,paid,user,done,steps⟩ := run x u S rep (fun i _ => fresh i)
  exact ⟨z,F,t,y,exec,by simpa only [List.ofFn_eq_map] using paid,user,done,copyWindowTrace n r d x y steps⟩

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
theorem borrowedWindow_host [M8.Machine.Net] (charged : Bool) (n : Fin 9) (p : Fin 32 × Fin 5) (j : Fin Copy.lifecycles.length) :
    ∃ (T states : ℕ) (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (fan : Fin (142081+2) ↪ Fin T),
    (∀ j : Fin (rowSwapBlock.tapes+35), j.val ≠ 24 → ∀ h, fan h ≠ ports j) ∧
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q → ∀ (body : P → Pr P T Q prime U) (f : P),
    ∃ (base : ℕ) (code : Pr P T Q prime U), ∀ (node : Descriptor) (w B rows : ℕ),
    node.width = 64*(w+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    let M := prime^(w+1)
    let K := node.beforeRows*rows*node.between*node.afterD
    let blocks := M^112*B
    let W := blocks*prime^(64*((w+1)*64))*K
    let V := M^16*W
    let desc := scheduledChild prime node (copyChildPosition (n,p,j))
    0 < W → ∃ position : Fin (volume prime desc) ≃ Fin V,
      CopyIntervalPositions desc (w+1) W position ∧
      ∀ record, ∃ prepared : Stacks T prime, WorkerEntryWords (scheduledRecordPorts ports) record prepared ∧ ∀ budget,
      ScheduledChildExec node desc w W ports record position body f budget charged →
      ∀ data u S, HelperFan fan data S →
        (∀ k, (∀ h, fan h ≠ k) → S.L k = prepared.L k ∧ S.R k = prepared.R k) →
        ∃ z F t out, Exec body code (mk u S) t (mk z F) ∧
          workerCost charged S F t (nativePrice charged (base*V + 12) + budget) ∧
          z.user = u.user ∧ HelperFan fan out F ∧
          CopyFanoutEffect n p.1 p.2 Copy.lifecycles[j.val] (List.getElem_mem ..) (w+1) blocks K data out := by
  obtain ⟨T,states,ports,fan,apart,build⟩ := commonCopyWindow_layout true charged n p.1 p.2 j
  refine ⟨T,states,ports,fan,apart,?_⟩
  intro P U Q fits body f
  obtain ⟨base,swaps,code,run⟩ := build fits body f
  refine ⟨base,code,?_⟩
  intro node w B rows width split label M K blocks W V desc pos
  obtain ⟨position,coords,worker⟩ := run node w B rows blocks K width split label (by dsimp [blocks,K,M]; ring) pos
  refine ⟨position,coords,?_⟩
  intro record
  obtain ⟨prepared,archive,build⟩ := worker record
  refine ⟨prepared,archive,?_⟩
  intro budget child
  have execute := build budget child
  intro data u S live saved
  obtain ⟨z,F,t,out,exec,paid,user,done,act⟩ := execute data u S live saved
  exact ⟨z,F,t,out,exec,by simpa only [Bool.true_and,ite_true,Nat.zero_mul,Nat.add_zero] using paid,user,done,act⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
