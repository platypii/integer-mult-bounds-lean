module

public import IntegerMultBounds.MathlibTM2.M6.BitOwnerStash
public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleLeaf

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Fast Cover.Fallback
open RecursiveInterchangeLayout
open Shared50ModularControl (prime)

/-- A child may borrow the right stack of the record tape. Charge its execution
once and retain the caller’s arbitrary left stack and older archive frames. -/
theorem callWithInvocationRecord {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (entry : P) (ports : Fin 35 ↪ Fin T) (archive : Fin T) (apart : archive ≠ ports 34) :
    ∃ code : Pr P T Q prime U, ∀ (word : List (Fin (prime+4))), blank ∉ word →
      let record := ports 34
      ∀ (u : HS T Q prime U) (S : Stacks T prime) (price : ℕ) (result : Stacks T prime → Prop),
      S.R record = word →
      let saved := blank :: word.reverse ++ blank :: S.R archive
      let parked := {S with R := Function.update (Function.update S.R record []) archive saved}
      (∀ v : HS T Q prime U, v.user = u.user → ∃ z F n,
        Exec body (body entry) (mk v parked) n (mk z F) ∧
        CleanupBound parked F n price ∧ z.user = v.user ∧
        F.R archive = saved ∧ F.L record = S.L record ∧ result F) →
      ∃ z F n G, Exec body code (mk u S) n (mk z F) ∧ CleanupBound S F n (price+4*word.length+14) ∧
        z.user = u.user ∧ result G ∧
        (∀ j, j ≠ record → j ≠ archive → F.L j = G.L j ∧ F.R j = G.R j) ∧
        F.L record = S.L record ∧ F.R record = word ∧ F.L archive = G.L archive ∧ F.R archive = S.R archive := by
  let record := ports 34
  let xs := [record]
  refine ⟨(synStash archive blank xs).seq ((Prog.call entry).seq
    ((bclear record).seq (synUnstash archive blank xs))),?_⟩
  intro word safe rec u S price result stack saved parked run
  change S.R record = word at stack
  have clr : synClr S.R xs = Function.update S.R record [] := by
    funext j
    by_cases eq : j = record <;> simp [synClr,xs,eq]
  have frame : synStk S.R blank xs ++ blank :: S.R archive = saved := by
    simp [xs,synStk,stack,saved]
  have nd : xs.Nodup := by simp [xs]
  have off : archive ∉ xs := by simpa [xs,record] using apart
  obtain ⟨v,k,user,saveCost,save⟩ := stashRight_exec body archive blank xs nd off u S
  rw [clr,frame] at save
  obtain ⟨z,G,n,exec,paid,same,kept,left,out⟩ := run v user
  change G.L record = S.L record at left
  obtain ⟨q,qu,_,clear⟩ := bclear_exec body record z G
  let R := Function.update G.R record word
  have restore : Function.update G.R record [] =
      Function.update (synClr R xs) archive (synStk R blank xs ++ blank :: S.R archive) := by
    funext j
    by_cases ha : j = archive
    · subst j
      simpa [R,record,apart,xs,synStk,saved] using kept
    · by_cases hr : j = record <;> simp [R,synClr,xs,ha,hr,show record ≠ archive from apart.symm]
  obtain ⟨v',l,last,backCost,back⟩ := unstashRight_exec body archive blank xs nd off R (S.R archive)
    (by simpa [R,xs] using safe) q {G with R := Function.update G.R record []} restore
  let F := {G with R := Function.update R archive (S.R archive)}
  have ret : F.R record = word := by simp [F,R,record,apart.symm]
  have outside (j) (hr : j ≠ record) (ha : j ≠ archive) : F.R j = G.R j := by simp [F,R,hr,ha]
  refine ⟨v',F,_,G,save.seq ((Exec.call exec).seq (clear.seq back)),?_,last.trans (qu.trans (same.trans user)),
    out,fun j hr ha => ⟨rfl,outside j hr ha⟩,left,ret,rfl,Function.update_self ..⟩
  intro js distinct
  let other := js.filter (· ≠ record)
  have unique : (record :: other).Nodup := by simp [other,distinct.filter]
  have bill := paid (record :: other) unique
  change n+tapeCharge cleanupWeight (record :: other) G ≤ tapeCharge cleanupWeight (record :: other) parked+price at bill
  have pl (j) : parked.L j = S.L j := rfl
  have fl (j) : F.L j = G.L j := rfl
  have pa : parked.R archive = saved := Function.update_self ..
  have fa : F.R archive = S.R archive := Function.update_self ..
  have po j (hr : j ≠ record) (ha : j ≠ archive) : parked.R j = S.R j := by
    change Function.update (Function.update S.R record []) archive saved j = _
    simp [ha,hr]
  have balance (is : List (Fin T)) :
      tapeCharge cleanupWeight is F + tapeCharge cleanupWeight (is.filter (· ≠ record)) parked =
      tapeCharge cleanupWeight is S + tapeCharge cleanupWeight (is.filter (· ≠ record)) G := by
    induction is with
    | nil => rfl
    | cons j is ih =>
      by_cases hr : j = record
      · subst j
        simp [tapeCharge,cleanupWeight,ret,fl,left,stack] at ih ⊢
        omega
      · by_cases ha : j = archive
        · subst j
          simp [tapeCharge,cleanupWeight,fl,pl,fa,pa,hr,kept] at ih ⊢
          omega
        · simp [tapeCharge,cleanupWeight,fl,pl,outside j hr ha,po j hr ha,hr] at ih ⊢
          omega
  have eq := balance js
  have zero : parked.R record = [] := by simp [parked,rec,record,apart.symm]
  simp only [tapeCharge,List.map_cons,List.sum_cons,cleanupWeight,left,zero,List.length_nil] at bill
  simp only [xs,synStashCost,R,Function.update_self,stack] at saveCost backCost
  change _ + tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S + _
  dsimp only [other,tapeCharge] at bill eq ⊢
  have hl : parked.L record = S.L record := rfl
  rw [hl] at bill
  unfold cleanupWeight at eq ⊢
  omega

/-- Close the active MOVE record contract from a child running with its cutoff
tape cleared. Tape 24 carries the returned payload on the original bank. -/
theorem activeMoveWithRecord {P U : Type} {n T Q : ℕ} (body : P → Pr P T Q prime U)
    (entry : P) (ports : Fin (n+35) ↪ Fin T) (archive : Fin T)
    (away : ∀ i, ports i ≠ archive) :
    let bank := scheduledRecordPorts ports
    ∃ code : Pr P T Q prime U, ∀ (node child : Descriptor) (w W L cutoff price : ℕ)
      (position : Fin (volume prime child) ≃ Fin ((prime^(w+1))^16*W)),
      let header := binSyms (A := prime) L cutoff
      let stored := RecordReady (b := prime) (w := w) (d := 16) (W := W) bank
        (prime^(w+1)).size W.size header SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
      let clean := fun S : Stacks T prime => ∀ i : Fin (n+35), 35 ≤ i.val →
        S.L (ports i) = [] ∧ S.R (ports i) = []
      (child.width < node.width → ∀ (u : HS T Q prime U) S x, stored x S → clean S →
        let saved := blank :: header.reverse ++ blank :: S.R archive
        let parked := {S with R := Function.update (Function.update S.R (bank 34) []) archive saved}
        ∀ v : HS T Q prime U, v.user = u.user → ∃ z G t y,
        Exec body (body entry) (mk v parked) t (mk z G) ∧ CleanupBound parked G t price ∧
        z.user = v.user ∧ G.R archive = saved ∧ G.L (bank 34) = S.L (bank 34) ∧
        (∀ j, j ≠ bank 24 → j ≠ bank 34 → j ≠ archive → G.L j = S.L j ∧ G.R j = S.R j) ∧
        G.L archive = S.L archive ∧ RecordPayload (bank 24) (fun _ => blank) 0 y G ∧
        ∀ h, y (position h) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x ∘ position) h) →
      MoveOnBankExec node child w W ports header position body code (price+4*L+14) true := by
  intro bank
  have atBank (i : Fin 35) : bank i ≠ archive := away _
  obtain ⟨code,call⟩ := callWithInvocationRecord body entry bank archive (atBank 34).symm
  refine ⟨code,?_⟩
  intro node child w W L cutoff price position header stored clean childRun smaller _ _ _ u S x ready free
  have safe : blank ∉ header := by
    simp only [header,binSyms,List.mem_ofFn,not_exists]
    intro i
    cases h : cutoff.testBit i.val <;> simp [bitSymbol,blank]
  let result := fun G : Stacks T prime => (∀ j, j ≠ bank 24 → j ≠ bank 34 → j ≠ archive →
    G.L j = S.L j ∧ G.R j = S.R j) ∧ G.L archive = S.L archive ∧
    ∃ y, RecordPayload (bank 24) (fun _ => blank) 0 y G ∧
      ∀ h, y (position h) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x ∘ position) h
  obtain ⟨z,F,t,G,exec,paid,user,⟨kept,archiveLeft,y,payload,read⟩,off,left,right,archiveView,tail⟩ :=
    call header safe u S price result ready.archive (by
      intro v same
      obtain ⟨z,G,t,y,exec,paid,user,stock,left,kept,archiveLeft,payload,read⟩ :=
        childRun smaller u S x ready free v same
      exact ⟨z,G,t,exec,paid,user,stock,left,kept,archiveLeft,y,payload,read⟩)
  have frame (j) (hp : j ≠ bank 24) (hr : j ≠ bank 34) (ha : j ≠ archive) :=
    And.intro ((off j hr ha).1.trans (kept j hp hr ha).1) ((off j hr ha).2.trans (kept j hp hr ha).2)
  have restored (i : Fin 35) (hi : i ≠ 24) : F.L (bank i) = S.L (bank i) ∧ F.R (bank i) = S.R (bank i) := by
    by_cases h : i = 34
    · subst i; exact ⟨left,right.trans ready.archive.symm⟩
    · exact frame _ (bank.injective.ne hi) (bank.injective.ne h) (atBank i)
  have live := off (bank 24) (bank.injective.ne (by decide)) (atBank 24)
  refine ⟨z,F,t,y,exec,?_,user,ready.returnPayload restored (fun i => ?_),?_,left,?_,read⟩
  · change CleanupBound S F t _
    simpa only [header,binSyms,List.length_ofFn] using paid
  · rw [live.1,live.2]
    simpa only [List.map_ofFn] using (payload i).symm
  · intro i hi
    have ne (j : Fin 35) : ports i ≠ bank j := by
      intro eq
      have e := congrArg Fin.val (ports.injective eq)
      change i.val = j.val at e
      omega
    obtain ⟨a,b⟩ := frame _ (ne 24) (ne 34) (away i)
    exact ⟨a.trans (free i hi).1,b.trans (free i hi).2⟩
  · intro j outside
    by_cases h : j = archive
    · subst j
      exact ⟨archiveView.trans archiveLeft,tail⟩
    · exact frame _ (outside _).symm (outside _).symm h

end IntegerMultBounds.MathlibTM2.M6.BitNode
