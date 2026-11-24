module

public import IntegerMultBounds.MathlibTM2.M6.BitOwnerStash
public import IntegerMultBounds.MathlibTM2.M6.BitWorkerIntervalRecord
public import IntegerMultBounds.MathlibTM2.M6.BitWorkerDispatch

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Fast Cover.Fallback
open RecursiveInterchangeLayout
open Shared50ModularControl (prime)

private noncomputable def recordFrame (word tail : List (Fin (prime+4))) := blank :: word.reverse ++ blank :: tail

noncomputable def copyCutoff {P U : Type} {T Q : ℕ} (src archive tmp : Fin T) : Pr P T Q prime U :=
  let mark := synPush archive blank
  mark.seq ((Fast.copyR src archive tmp id).seq mark)

noncomputable def recordCall {P U : Type} {T Q : ℕ} (save call : Pr P T Q prime U)
    (record archive : Fin T) : Pr P T Q prime U :=
  save.seq (call.seq ((bclear record).seq (synUnstash archive blank [record])))

/-- Copy the cutoff into the archive without consuming the child's input. -/
private theorem saveCutoffCopy {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (src archive tmp : Fin T) (sa : src ≠ archive) (st : src ≠ tmp) (atmp : archive ≠ tmp) :
    ∀ (u : HS T Q prime U) (S : Stacks T prime), S.R tmp = [] →
      ∃ z, z.user = u.user ∧ Exec body (copyCutoff src archive tmp) (mk u S) (4*(S.R src).length+6)
        (mk z {S with R := Function.update S.R archive (recordFrame (S.R src) (S.R archive))}) := by
  let mark := synPush (P := P) (Q := Q) (U := U) archive (blank (a := prime))
  have push (v : HS T Q prime U) (D : Stacks T prime) :
      Exec body mark (mk v D) 1 (mk v {D with R := Function.update D.R archive (blank :: D.R archive)}) := by
    exact (Exec.act _ _).cast rfl (by simp [Action.run,update_rt,store_mk])
  intro u S empty
  let D := {S with R := Function.update S.R archive (blank :: S.R archive)}
  obtain ⟨z,user,copy⟩ := Fast.copyR_exec (body := body) src archive tmp sa st atmp id u D
    (by simpa [D,atmp.symm] using empty)
  refine ⟨z,user,((push u S).seq (copy.seq (push z _))).cast ?_ ?_⟩
  · simp [D,sa]; omega
  · simp [D,recordFrame,sa,Function.update_idem]

/-- A child may borrow the right stack of the record tape. Charge its execution
once and retain the caller’s arbitrary left stack and older archive frames. -/
private theorem withInvocationRecord {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (call : Pr P T Q prime U) (ports : Fin 35 ↪ Fin T) (archive : Fin T) (apart : archive ≠ ports 34)
    (saveCode : Pr P T Q prime U) (stock : Stacks T prime → Prop)
    (retained : List (Fin (prime+4)) → List (Fin (prime+4))) (fee : ℕ → ℕ)
    (saveWord : ∀ (u : HS T Q prime U) (S : Stacks T prime), stock S → ∃ (z : HS T Q prime U) (k : ℕ), z.user = u.user ∧ k ≤ fee (S.R (ports 34)).length ∧
      Exec body saveCode (mk u S) k (mk z {S with R := Function.update (Function.update S.R (ports 34) (retained (S.R (ports 34)))) archive (recordFrame (S.R (ports 34)) (S.R archive))})) :
    ∀ (word : List (Fin (prime+4))), blank ∉ word →
      let record := ports 34
      ∀ (u : HS T Q prime U) (S : Stacks T prime) (price : ℕ) (result : Stacks T prime → Prop),
      stock S → S.R record = word →
      let saved := blank :: word.reverse ++ blank :: S.R archive
      let parked := {S with R := Function.update (Function.update S.R record (retained word)) archive saved}
      (∀ v : HS T Q prime U, v.user = u.user → ∃ z F n,
        Exec body call (mk v parked) n (mk z F) ∧
        CleanupBound parked F n price ∧ z.user = v.user ∧
        F.R archive = saved ∧ F.L record = S.L record ∧ result F) →
      ∃ z F n G, Exec body (recordCall saveCode call record archive) (mk u S) n (mk z F) ∧ CleanupBound S F n (price+fee word.length+2*word.length+7+2*(retained word).length) ∧
        z.user = u.user ∧ result G ∧
        (∀ j, j ≠ record → j ≠ archive → F.L j = G.L j ∧ F.R j = G.R j) ∧
        F.L record = S.L record ∧ F.R record = word ∧ F.L archive = G.L archive ∧ F.R archive = S.R archive := by
  let record := ports 34
  let xs := [record]
  intro word safe rec u S price result initial stack saved parked run
  change S.R record = word at stack
  have nd : xs.Nodup := by simp [xs]
  have off : archive ∉ xs := by simpa [xs,record] using apart
  obtain ⟨v,k,user,saveCost,save⟩ := saveWord u S initial
  change S.R (ports 34) = word at stack
  rw [stack] at saveCost save
  change S.R record = word at stack
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
  refine ⟨v',F,_,G,save.seq (exec.seq (clear.seq back)),?_,last.trans (qu.trans (same.trans user)),
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
    change Function.update (Function.update S.R record (retained word)) archive saved j = _
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
  have zero : parked.R record = retained word := by simp [parked,rec,record,apart.symm]
  simp only [tapeCharge,List.map_cons,List.sum_cons,cleanupWeight,left,zero] at bill
  simp only [xs,synStashCost,R,Function.update_self] at backCost
  change _ + tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S + _
  dsimp only [other,tapeCharge] at bill eq ⊢
  have hl : parked.L record = S.L record := rfl
  rw [hl] at bill
  unfold cleanupWeight at eq ⊢
  omega

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
  let xs := [ports 34]
  have save (u : HS T Q prime U) (S : Stacks T prime) (_ : True) :=
    stashRight_exec body archive blank xs (by simp [xs]) (by simpa [xs] using apart) u S
  have run := withInvocationRecord body (.call entry) ports archive apart (synStash archive blank xs)
    (fun _ => True) (fun _ => []) (fun l => 2*l+5) (by
      intro u S ok
      obtain ⟨z,k,user,fee,exec⟩ := save u S ok
      refine ⟨z,k,user,?_,?_⟩
      · simpa [xs,synStashCost,Nat.add_assoc] using fee
      · have eq : synClr S.R xs = Function.update S.R (ports 34) [] := by
          funext j
          by_cases h : j = ports 34 <;> simp [xs,synClr,h]
        simpa [eq,xs,synStk,recordFrame] using exec)
  refine ⟨recordCall (synStash archive blank xs) (.call entry) (ports 34) archive,?_⟩
  intro word safe record u S price result input saved parked child
  obtain ⟨z,F,n,G,exec,paid,out⟩ := run word safe u S (price+2) result trivial input (by
    intro v same
    obtain ⟨z,G,n,exec,paid,post⟩ := child v same
    refine ⟨z,G,_,Exec.call exec,?_,post⟩
    intro js nd
    change n+2+tapeCharge _ js G ≤ tapeCharge _ js parked+(price+2)
    have := paid js nd
    omega)
  refine ⟨z,F,n,G,exec,?_,out⟩
  convert paid using 1
  simp
  omega

def moveScratch {n T : ℕ} (ports : Fin (n+35) ↪ Fin T) :=
  ((List.finRange (n+35)).filter fun i => 35 ≤ i.val ∨ i.val ∈ shearWork.map Fin.val).map ports

/-- The active procedure is fixed before the table of recursive calls is installed. -/
noncomputable def activeMoveProgram {P U : Type} {n T Q : ℕ} (entry : P)
    (ports : Fin (n+35) ↪ Fin T) (archive : Fin T) : Pr P T Q prime U :=
  let bank := scheduledRecordPorts ports
  recordCall (copyCutoff (bank 34) archive (bank 0)) ((Prog.call entry).seq (clearWorkTapes (moveScratch ports)))
    (bank 34) archive

/-- The recursive MOVE body can leave the caller's scratch dirty and overwrite the cutoff. -/
def MoveBodyExec {P U : Type} {n T Q : ℕ} (body : P → Pr P T Q prime U) (entry : P)
    (ports : Fin (n+35) ↪ Fin T) (node child : Descriptor) (w W : ℕ) (header : List (Fin (prime+4)))
    (position : Fin (volume prime child) ≃ Fin ((prime^(w+1))^16*W)) (price : ℕ) : Prop :=
    let bank := scheduledRecordPorts ports
    let work := moveScratch ports
    let stored := fun record => RecordReady (b := prime) (w := w) (d := 16) (W := W) bank
        (prime^(w+1)).size W.size record SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
    let clean := fun S : Stacks T prime => ∀ i : Fin (n+35), 35 ≤ i.val →
      S.L (ports i) = [] ∧ S.R (ports i) = []
    child.width < node.width → ∀ (v : HS T Q prime U) S x, stored header x S → clean S →
      ∃ z G t y, Exec body (body entry) (mk v S) t (mk z G) ∧ CleanupBound S G t price ∧
      z.user = v.user ∧ G.L (bank 34) = S.L (bank 34) ∧
      (∀ j, j ≠ bank 24 → j ≠ bank 34 → j ∉ work → G.L j = S.L j ∧ G.R j = S.R j) ∧
      RecordPayload (bank 24) (fun _ => blank) 0 y G ∧
      ∀ h, y (position h) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x ∘ position) h

/-- Close the active MOVE record contract from a child running with its cutoff
tape intact. Reclaim the shear and suffix workspace from the child’s
cleanup charge. Tape 24 carries the returned payload on the original bank. -/
theorem activeMoveWithRecord {P U : Type} {n T Q : ℕ} (body : P → Pr P T Q prime U)
    (entry : P) (ports : Fin (n+35) ↪ Fin T) (archive : Fin T)
    (away : ∀ i, ports i ≠ archive) :
    let work := moveScratch ports
    ∀ (node child : Descriptor) (w W L cutoff price : ℕ)
      (position : Fin (volume prime child) ≃ Fin ((prime^(w+1))^16*W)),
      let header := binSyms (A := prime) L cutoff
      MoveBodyExec body entry ports node child w W header position price →
      MoveOnBankExec node child w W ports header position body (activeMoveProgram entry ports archive) (price+4*work.length+8*L+16) true := by
  intro work
  let bank := scheduledRecordPorts ports
  have distinct : work.Nodup := ((List.nodup_finRange _).filter _).map ports.injective
  have members {j} (hj : j ∈ work) : ∃ i, (35 ≤ i.val ∨ i.val ∈ shearWork.map Fin.val) ∧ ports i = j := by
    obtain ⟨i,mem,rfl⟩ := List.mem_map.mp hj
    exact ⟨i,of_decide_eq_true (List.mem_filter.mp mem).2,rfl⟩
  have excludes (j : Fin 35) (live : j.val ∉ shearWork.map Fin.val) : bank j ∉ work := by
    intro h
    obtain ⟨i,hi,eq⟩ := members h
    have e := congrArg Fin.val (ports.injective eq)
    change i.val = j.val at e
    rw [e] at hi
    exact hi.elim (by omega) live
  have outsideArchive : archive ∉ work := fun h => by
    obtain ⟨i,_,eq⟩ := members h
    exact away i eq
  have atBank (i : Fin 35) : bank i ≠ archive := away _
  have save := saveCutoffCopy body (bank 34) archive (bank 0) (atBank 34)
    (bank.injective.ne (by decide)) (atBank 0).symm
  have call := withInvocationRecord body ((Prog.call entry).seq (clearWorkTapes work)) bank archive (atBank 34).symm
    (copyCutoff (bank 34) archive (bank 0)) (fun S => S.R (bank 0) = []) id (fun l => 4*l+6) (by
      intro u S empty
      obtain ⟨z,user,exec⟩ := save u S empty
      exact ⟨z,_,user,le_rfl,by simpa only [id_eq,Function.update_eq_self] using exec⟩)
  intro node child w W L cutoff price position header childRun smaller _ _ _ u S x ready free
  have safe : blank ∉ header := by
    simp only [header,binSyms,List.mem_ofFn,not_exists]
    intro i
    cases h : cutoff.testBit i.val <;> simp [bitSymbol,blank]
  let result := fun G : Stacks T prime => (∀ j, j ≠ bank 24 → j ≠ bank 34 → j ≠ archive →
    G.L j = S.L j ∧ G.R j = S.R j) ∧ G.L archive = S.L archive ∧
    ∃ y, RecordPayload (bank 24) (fun _ => blank) 0 y G ∧
      ∀ h, y (position h) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x ∘ position) h
  obtain ⟨z,F,t,G,exec,paid,user,⟨kept,archiveLeft,y,payload,read⟩,off,left,right,archiveView,tail⟩ :=
    call header safe u S (price+4*work.length+3) result (ready.scratch 0 (by decide)).2 ready.archive (by
      intro v same
      let parked := {S with R := Function.update (Function.update S.R (bank 34) (id header)) archive
                                  (blank :: header.reverse ++ blank :: S.R archive)}
      have field (i : Fin 35) (hi : i ≠ 34) : parked.R (bank i) = S.R (bank i) := by
        simp [parked,atBank i,bank.injective.ne hi]
      have prepared : RecordReady (b := prime) (w := w) (d := 16) (W := W) bank
          (prime^(w+1)).size W.size header SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 x parked := by
        refine ⟨(field 2 (by decide)).trans ready.modulus,(field 27 (by decide)).trans ready.width,
          (field 28 (by decide)).trans ready.one,(field 32 (by decide)).trans ready.padded,
          (congrArg List.length (field 33 (by decide))).trans ready.clock,?_,?_,?_,?_⟩
        · simp [parked,atBank 34]
        · intro i hi
          have ne : i ≠ 34 := fun eq => (by decide : (34 : Fin 35) ∉ shearWork) (eq ▸ hi)
          exact ⟨(ready.scratch i hi).1,(field i ne).trans (ready.scratch i hi).2⟩
        · intro j
          rw [field 24 (by decide)]
          exact ready.src j
        · intro j
          rw [field 25 (by decide)]
          exact ready.dst j
      have cleanEntry : ∀ i : Fin (n+35), 35 ≤ i.val → parked.L (ports i) = [] ∧ parked.R (ports i) = [] := by
        intro i hi
        have ne : ports i ≠ bank 34 := by
          intro eq
          have e := congrArg Fin.val (ports.injective eq)
          change i.val = 34 at e
          omega
        simpa [parked,away i,ne] using free i hi
      obtain ⟨z,G,t,y,exec,paid,user,left,frame,payload,read⟩ :=
        childRun smaller v parked x prepared cleanEntry
      have archiveFrame := frame archive (atBank 24).symm (atBank 34).symm outsideArchive
      have stock := archiveFrame.2.trans (Function.update_self ..)
      have archiveLeft : G.L archive = S.L archive := archiveFrame.1
      have kept j hp (hr : j ≠ bank 34) (ha : j ≠ archive) h : G.L j = S.L j ∧ G.R j = S.R j := And.intro (frame j hp hr h).1
        ((frame j hp hr h).2.trans (show parked.R j = S.R j by simp [parked,ha,hr]))
      obtain ⟨q,qu,clear⟩ := clearWorkTapes_exec body work distinct z G
      let F := {G with L := fun j => if j ∈ work then [] else G.L j,
                       R := fun j => if j ∈ work then [] else G.R j}
      have initial (j) (hj : j ∈ work) : S.L j = [] ∧ S.R j = [] := by
        obtain ⟨i,hi,rfl⟩ := members hj
        rcases hi with suffix | scratch
        · exact free i suffix
        · obtain ⟨j,hj,e⟩ := List.mem_map.mp scratch
          have eq : bank j = ports i := congrArg ports (Fin.ext e)
          exact eq ▸ ready.scratch j hj
      have empty (j) (hj : j ∈ work) : F.L j = [] ∧ F.R j = [] := by simp [F,hj]
      have keep (j) (hj : j ∉ work) : F.L j = G.L j ∧ F.R j = G.R j := by simp [F,hj]
      have charge := cleanupBound_clearBank work distinct paid (Nat.le_refl (tapeCharge cleanupWeight work G+1))
        empty (fun j => by by_cases h : j ∈ work <;> simp [F,h])
      have initialCharge : tapeCharge cleanupWeight work
          {S with R := Function.update (Function.update S.R (bank 34) (id header)) archive (blank :: header.reverse ++ blank :: S.R archive)} = 4*work.length := by
        unfold tapeCharge
        rw [List.map_congr_left (g := fun _ => 4) (fun j hj => by
          have ha : j ≠ archive := fun eq => outsideArchive (eq ▸ hj)
          have hr : j ≠ bank 34 := fun eq => excludes 34 (by decide) (eq ▸ hj)
          simp [cleanupWeight,ha,hr,(initial j hj).1,(initial j hj).2])]
        simp [List.map_const',Nat.mul_comm]
      refine ⟨q,F,_,(Exec.call exec).seq clear,?_,qu.trans user,(keep _ outsideArchive).2.trans stock,
        (keep _ (excludes 34 (by decide))).1.trans left,?_,(keep _ outsideArchive).1.trans archiveLeft,y,?_,read⟩
      · intro js nd
        have bill := charge js nd
        rw [initialCharge] at bill
        change _ + tapeCharge cleanupWeight js F ≤ _ at bill ⊢
        dsimp only [parked,tapeCharge,cleanupWeight] at bill ⊢
        omega
      · intro j hp hr ha
        by_cases h : j ∈ work
        · exact ⟨(empty j h).1.trans (initial j h).1.symm,(empty j h).2.trans (initial j h).2.symm⟩
        · exact ⟨(keep j h).1.trans (kept j hp hr ha h).1,(keep j h).2.trans (kept j hp hr ha h).2⟩
      · intro i
        unfold RecordPayload at payload
        rw [(keep _ (excludes 24 (by decide))).1,(keep _ (excludes 24 (by decide))).2]
        exact payload i)
  have frame (j) (hp : j ≠ bank 24) (hr : j ≠ bank 34) (ha : j ≠ archive) :=
    And.intro ((off j hr ha).1.trans (kept j hp hr ha).1) ((off j hr ha).2.trans (kept j hp hr ha).2)
  have restored (i : Fin 35) (hi : i ≠ 24) : F.L (bank i) = S.L (bank i) ∧ F.R (bank i) = S.R (bank i) := by
    by_cases h : i = 34
    · subst i; exact ⟨left,right.trans ready.archive.symm⟩
    · exact frame _ (bank.injective.ne hi) (bank.injective.ne h) (atBank i)
  have live := off (bank 24) (bank.injective.ne (by decide)) (atBank 24)
  refine ⟨z,F,t,y,exec,?_,user,ready.returnPayload restored (fun i => ?_),?_,left,?_,read⟩
  · change CleanupBound S F t _
    simp only [id_eq,header,binSyms,List.length_ofFn] at paid
    convert paid using 1
    omega
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

def moveWidthPorts : Fin 10 ↪ Fin 35 :=
  ⟨![33,34,0,1,3,4,5,6,7,8],by decide⟩

/-- The opened MOVE record supplies four unit fields and the spectator field of
the packed descriptor. Only the width word needs to be written. -/
theorem openedMoveDimensions {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin 35 ↪ Fin T) (spectator : Fin T) (apart : ∀ i, bank i ≠ spectator) (rank : ℕ) :
    let r := moveWidthPorts.trans bank
    let fields : Fin 6 → Fin T := ![bank 28,bank 28,bank 28,r 3,bank 28,spectator]
    ∀ (child : Descriptor) (w W L cutoff : ℕ) (u : HS T Q prime U) (S : Stacks T prime) x,
      child.width = (w+1)*rank →
      RecordReady (b := prime) (w := w) (d := 16) (W := W) bank (prime^(w+1)).size W.size
        (binSyms L cutoff) SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 x S →
      let n := CopyChildLayout.spectators child
      S.R spectator = binSyms n.size n →
      let word := binSyms (A := prime) child.width.size child.width
      let F := {S with R := Function.update S.R (r 3) word}
      ∃ z t, Exec body (moveWidthProgram r rank) (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (4*w+23*child.width+22+2*child.width.size) ∧
        ∀ i, F.R (fields i) = (M8.RevMachine.Routines.hdr (packedDescriptor child.width n) i).map bitSymbol := by
  intro r fields child w W L cutoff u S x width ready n spectatorWord word F
  have scratch (i : Fin 10) (hi : 2 ≤ i.val) : moveWidthPorts i ∈ shearWork :=
    (by decide : ∀ i : Fin 10, 2 ≤ i.val → moveWidthPorts i ∈ shearWork) i hi
  obtain ⟨z,t,user,paid,run⟩ := packedMoveWidth_exec body r rank w u S ready.clock
    (fun i hi => (ready.scratch _ (scratch i hi)).2)
  rw [← width] at paid run
  refine ⟨z,t,run,user,?_,?_⟩
  · intro js nd
    have growth := prependedWordCharge S (r 3) word js nd
    have empty : S.R (r 3) = [] := (ready.scratch _ (scratch 3 (by decide))).2
    simp only [empty,List.append_nil,word,length_binSyms] at growth
    change t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+(4*w+23*child.width+22+2*child.width.size)
    change tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+2*child.width.size at growth
    omega
  · have unit : F.R (bank 28) = binSyms 1 1 :=
      (Function.update_of_ne (bank.injective.ne (by decide : (28 : Fin 35) ≠ moveWidthPorts 3)) ..).trans ready.one
    have tail : F.R spectator = binSyms n.size n :=
      (Function.update_of_ne (apart (moveWidthPorts 3)).symm ..).trans spectatorWord
    have active : F.R (r 3) = word := Function.update_self ..
    intro i
    rw [M8.RevMachine.Routines.hdr,canonicalBits_symbols]
    have unitHeader : F.R (bank 28) = binSyms (1 : ℕ).size 1 := by
      rw [show (1 : ℕ).size = 1 by decide]
      exact unit
    fin_cases i <;> first | exact unitHeader | exact active | exact tail

/-- Materialize the packed child descriptor from the two-field scheduled
record. The cutoff remains on tape 34 and the payload stays on tape 24. -/
theorem packedMoveDimensions {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin 35 ↪ Fin T) (spectator : Fin T) (apart : ∀ i, bank i ≠ spectator) (rank : ℕ) :
    let r := moveWidthPorts.trans bank
    let fields : Fin 6 → Fin T := ![bank 28,bank 28,bank 28,r 3,bank 28,spectator]
    ∀ (child : Descriptor) (w W L cutoff : ℕ) (u : HS T Q prime U) (S : Stacks T prime) x,
      child.width = (w+1)*rank →
      let n := CopyChildLayout.spectators child
      let header := binSyms (A := prime) L cutoff
      let count := binSyms (A := prime) n.size n
      RecordReady (b := prime) (w := w) (d := 16) (W := W) bank (prime^(w+1)).size W.size
        (count ++ separator :: header) SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 x S →
      S.R spectator = [] →
      let D := {S with R := Function.update (Function.update S.R (bank 34) header) spectator count}
      let F := {D with R := Function.update D.R (r 3) (binSyms child.width.size child.width)}
      ∃ z t, Exec body ((DFT.takeField (bank 34) spectator (bank 0)).seq (moveWidthProgram r rank))
        (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (7*(4*n.size+5)+(4*w+23*child.width+22+2*child.width.size)) ∧
        ∀ i, F.R (fields i) = (M8.RevMachine.Routines.hdr (packedDescriptor child.width n) i).map bitSymbol := by
  intro r fields child w W L cutoff u S x width n header count ready empty D F
  obtain ⟨v,openRun,user,opened,field⟩ := unpackMoveArchive body bank spectator apart w W L cutoff n x u S ready empty
  obtain ⟨z,k,prepare,same,paid,dimensions⟩ :=
    openedMoveDimensions body bank spectator apart rank child w W L cutoff v D x width opened field
  have stock := nativeCleanupBound (c := 1) openRun (by
    unfold DFT.takeField
    repeat first | apply And.intro | (change _ ≤ (1 : ℕ); exact of_decide_eq_true rfl))
  exact ⟨z,_,openRun.seq prepare,same.trans user,stock.seq paid,dimensions⟩

/-- Dispatch a scheduled MOVE using the spectator tape as the frame archive.
Its existing spectator word is restored before the dispatcher resumes. -/
theorem scheduledFramedMove [M8.Machine.Net] {P U : Type} {T Q : ℕ}
    (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (capacity : columnCapacity ≤ Q)
    (rank : ℕ) (positive : 0 < rank) (bounded : rank ≤ 64) :
    let prefixBank := movePrefix.trans ports
    let spectator := ports moveSpectatorPort
    ∃ leafCode : Pr P T Q prime U, ∀ (body : P → Pr P T Q prime U) (entry large leaf recur : P),
    body leaf = leafCode → body large = activeMoveProgram recur prefixBank spectator →
    body entry = twoFieldDispatch prefixBank spectator rank (body large) (body leaf) →
    ∀ (node child : Descriptor) (w W L cutoff price : ℕ), child.width = (w+1)*rank →
    cutoff < 2^L → child.width.size ≤ L → ∀ position : Fin (volume prime child) ≃ Fin ((prime^(w+1))^16*W),
    (∀ i, (position i).val = (CopyChildLayout.packActive child i).val) → 0 < W →
    let core : ℝ := (M8.RevMachine.LeafCore.small+5 : ℕ)*|M8.RevMachine.LeafCore.C|+8+
      M8.RevMachine.LeafCore.small*(16+8*|M8.RevMachine.LeafCore.C|)
    ∀ rate : ℝ, 391*(163+core) ≤ rate →
    let n := CopyChildLayout.spectators child
    let header := binSyms (A := prime) L cutoff
    let time := if cutoff < child.width then price+4*(moveScratch prefixBank).length+8*L+16
      else ⌊(rate*(child.width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime child⌋₊
    (cutoff < child.width → MoveBodyExec body recur prefixBank node child w W header position price) →
    ScheduledChildExec node child w W ports (binSyms n.size n ++ separator :: header) position body entry
      (time+4*w+23*child.width+22*L+8*n.size+61) true := by
  intro prefixBank spectator
  obtain ⟨code,dispatch⟩ := scheduledTwoFieldMove (P := P) (U := U) ports capacity rank positive true (fun _ => bounded)
  refine ⟨code,?_⟩
  intro body entry large leaf recur stopped installed select node child w W L cutoff price width fits digits
    position coords pos core rate enough n header time childRun
  apply dispatch body entry large leaf stopped select node child w W L cutoff
    (price+4*(moveScratch prefixBank).length+8*L+16) width fits digits position coords pos rate enough
  intro active
  rw [installed]
  apply activeMoveWithRecord body recur prefixBank spectator _ node child w W L cutoff price position (childRun active)
  intro i
  exact ports.injective.ne (fun eq => i.isLt.ne (congrArg Fin.val eq))

end IntegerMultBounds.MathlibTM2.M6.BitNode
