module

public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleReturn
public import IntegerMultBounds.MathlibTM2.M6.BitActiveCopy
public import IntegerMultBounds.MathlibTM2.M6.BitWorkerDispatch
public import IntegerMultBounds.MathlibTM2.M6.BitInheritedReturnMerge
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderCompactRead

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover.Fallback Stack Host
open RecursiveInterchangeLayout M8.RevMachine
open Shared50ModularControl (prime)
open Certificates.PR589
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Read the scheduled payload in logical child coordinates. The physical tape
still contains the caller's word, including its blank exterior. -/
theorem activeRecordWord {T w W m : ℕ} (bank : Fin 35 ↪ Fin T)
    (record : List (Fin (prime+4))) (word : Fin ((prime^(w+1))^16*W) → ZMod 2)
    (S : Stacks T prime)
    (ready : RecordReady (b := prime) (w := w) (d := 16) (W := W) bank
      (prime^(w+1)).size W.size record SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 word S)
    (position : Fin m ≃ Fin ((prime^(w+1))^16*W)) :
    WordAtZero ((word ∘ position) ∘ position.symm) (S.L (bank 24)) (S.R (bank 24)) := by
  intro j
  rw [← encodedOwnerCell]
  simpa only [Function.comp_def,Equiv.apply_symm_apply,sub_zero,List.map_ofFn] using ready.src j

/-- Run the recursive interval directly from the scheduled record's payload.
The merged tape is a positioned record payload in the parent's packed order. -/
theorem activeIntervalFromRecord {P U : Type} {M N Q price a w W : ℕ} (lane : Descriptor)
    (width : lane.width = 64*a) (positive : 0 < volume prime lane)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    {body : P → Pr P N Q prime U} {code src dst seed}
    (child : PackedPieceHandoff (volume prime lane) (packedChildOutput a _) body code src dst seed price)
    (bank : Fin 35 ↪ Fin M) (tmp : Fin M) :
    let T := intervalSplitTapes
    let V := volume prime lane
    ∀ (span : V*142080 = (prime^(w+1))^16*W) (place : Fin (142082+T+N) ↪ Fin M),
    let caller := ((Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb N)).trans place
    [bank 24,tmp,caller 0].Nodup →
    ∃ (host : Empty ⊕ P → Pr (Empty ⊕ P) M Q prime U) (program : Pr (Empty ⊕ P) M Q prime U),
    ∀ record word u (S : Stacks M prime),
      RecordReady (b := prime) (w := w) (d := 16) (W := W) bank (prime^(w+1)).size W.size record
        SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 word S →
      S.L tmp = [] → S.R tmp = [] →
      (∀ i, S.L (caller i) = [] ∧ S.R (caller i) = []) →
      (∀ i : Fin 142082, let j := place ((i.castAdd T).castAdd N); S.L j = [] ∧ S.R j = []) →
      (∀ i : Fin N, let j := place (i.natAdd (142082+T)); S.L j = seed.L i ∧ S.R j = seed.R i) →
      let wide := {lane with afterD := lane.afterD*142080}
      let size : volume prime wide = V*142080 := by simp [wide,V,volume,Nat.mul_assoc]
      let position := packedChildPosition wide (size.trans span)
      ∃ z F n y, Exec host program (mk u S) n (mk z F) ∧ z.user = u.user ∧
        n ≤ (298*(T+5)+13)*(V*142080)+142081*(8*V+10)+price+41 ∧
        RecordPayload (caller 0) (fun _ => blank) 0 y F ∧
        (∀ k, y (position k) = Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) (word ∘ position) k) ∧
        ∀ j, (∀ i, place i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro T V span place caller apart
  obtain ⟨host,program,out,target,run⟩ := packedIntervalFromWord_exec lane width positive capacity child place (bank 24) tmp apart
  refine ⟨host,program,?_⟩
  intro record word u S ready tl tr clear fresh prepared wide size position
  let changed := Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) (word ∘ position)
  let y := changed ∘ position.symm
  have castRead {l m : ℕ} (eq : l=m) (x : Fin m → ZMod 2) (L R) :
      WordAtZero x L R → WordAtZero (fun k => x (k.cast eq)) L R := by subst m; exact id
  have read := castRead span _ _ _ (activeRecordWord bank record word S ready position)
  have coord (k : Fin (V*142080)) :
      position.symm (k.cast span) = (packedChildPosition wide size).symm k := rfl
  simp only [Function.comp_apply,coord] at read
  obtain ⟨z,F,n,exec,user,paid,rep,frame⟩ := run (word ∘ position) u S read tl tr clear fresh prepared
  refine ⟨z,F,n,y,exec,user,paid,?_,fun k => by simp [y,changed],frame⟩
  rw [← target]
  apply castPayload span
  apply mergedPayload out F _ _
  simpa only [finProdFinEquiv.apply_symm_apply,Equiv.apply_symm_apply,y,Function.comp_apply,coord] using rep

open Cover Node Mult.PhaseCellToeplitz in
/-- Execute the recursive transpose, write its merged word back to the scheduled
record, then clear the private bank at the cost determined by its exit stacks. -/
theorem activeIntervalWriteback {P U : Type} {M N Q price a w W : ℕ} (lane : Descriptor)
    (width : lane.width = 64*a) (positive : 0 < volume prime lane)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    {body : P → Pr P N Q prime U} {code src dst seed}
    (child : PackedPieceHandoff (volume prime lane) (packedChildOutput a _) body code src dst seed price)
    (bank : Fin 35 ↪ Fin M) (count saved tmp : Fin M) :
    let T := intervalSplitTapes
    let V := volume prime lane
    ∀ (span : V*142080 = (prime^(w+1))^16*W) (place : Fin (142082+T+N) ↪ Fin M),
    let caller := ((Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb N)).trans place
    let slots := (List.finRange (142082+T+N)).map place
    [count,caller 0,bank 24,saved,tmp].Nodup →
    (∀ i j, place i ≠ bank j) →
    (∀ i, place i ≠ count ∧ place i ≠ saved ∧ place i ≠ tmp) →
    ∃ (host : Empty ⊕ P → Pr (Empty ⊕ P) M Q prime U) (worker finish : Pr (Empty ⊕ P) M Q prime U),
    ∀ record word u (S : Stacks M prime),
      RecordReady (b := prime) (w := w) (d := 16) (W := W) bank (prime^(w+1)).size W.size record
        SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 word S →
      S.R count = [] → S.R saved = [] → S.L tmp = [] → S.R tmp = [] →
      (∀ i, S.L (caller i) = [] ∧ S.R (caller i) = []) →
      (∀ i : Fin 142082, let j := place ((i.castAdd T).castAdd N); S.L j = [] ∧ S.R j = []) →
      (∀ i : Fin N, let j := place (i.natAdd (142082+T)); S.L j = seed.L i ∧ S.R j = seed.R i) →
      let wide := {lane with afterD := lane.afterD*142080}
      let size : volume prime wide = V*142080 := by simp [wide,V,volume,Nat.mul_assoc]
      let position := packedChildPosition wide (size.trans span)
      ∃ z F n y v mergedState k, Exec host worker (mk u S) k (mk v mergedState) ∧
        Exec host (worker.seq finish) (mk u S) n (mk z F) ∧ z.user = u.user ∧
        n ≤ (298*(T+5)+33)*(V*142080)+142081*(8*V+10)+price+64 +
          (slots.map fun j => 4*(mergedState.L j).length+2*(mergedState.R j).length+4).sum ∧
        (∀ i, F.L (place i) = [] ∧ F.R (place i) = []) ∧
        RecordReady (b := prime) (w := w) (d := 16) (W := W) bank (prime^(w+1)).size W.size record
          SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 y F ∧
        (∀ k, y (position k) = Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) (word ∘ position) k) ∧
        ∀ j, j ≠ bank 24 → (∀ i, place i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro T V span place caller slots apart disjoint regs
  have sep := apart
  regs_ne sep
  have loadApart : [bank 24,tmp,caller 0].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,List.nodup_nil,and_true,not_false_eq_true]
    exact ⟨⟨‹bank 24 ≠ tmp›,(disjoint _ 24).symm⟩,(regs _).2.2.symm⟩
  obtain ⟨host,program,run⟩ := activeIntervalFromRecord lane width positive capacity child bank tmp span place loadApart
  let write : Pr (Empty ⊕ P) M Q prime U := (loadCompactWord (caller 0) tmp count).seq
    (((usub count (bank 24) tmp).seq (Mult.PhaseCellToeplitz.movePrefix count (caller 0) (bank 24) saved tmp)).seq (bclear count))
  refine ⟨host,program,write.seq (clearWorkTapes slots),?_⟩
  intro record word u S ready hc hs tl tr clear fresh prepared wide size position
  obtain ⟨z,F,n,y,exec,user,paid,merged,effect,frame⟩ := run record word u S ready tl tr clear fresh prepared
  have owner := frame (bank 24) (fun i => disjoint i 24)
  have old : RecordPayload (bank 24) (fun _ => blank) 0 word F := by
    intro k
    rw [owner.1,owner.2]
    simpa only [List.map_ofFn] using ready.src k
  have member (i) : place i ∈ slots := List.mem_map.mpr ⟨i,List.mem_finRange _,rfl⟩
  have outside {j} (away : ∀ i, place i ≠ j) : j ∉ slots := by
    intro h
    obtain ⟨i,_,eq⟩ := List.mem_map.mp h
    exact away i eq
  obtain ⟨v,D,t,back,cost,same,payload,empty,rest⟩ := returnIdleBank_exec host apart slots
    ((List.nodup_finRange _).map place.injective) (member _) (outside (fun i => disjoint i 24))
    word y z F old merged ((frame count (fun i => (regs i).1)).2.trans hc)
    ((frame saved (fun i => (regs i).2.1)).2.trans hs)
    ((frame tmp (fun i => (regs i).2.2)).1.trans tl) ((frame tmp (fun i => (regs i).2.2)).2.trans tr)
  have keep j (ne : j ≠ bank 24) (away : ∀ i, place i ≠ j) : D.L j = S.L j ∧ D.R j = S.R j :=
    ⟨(rest j ne (outside away)).1.trans (frame j away).1,(rest j ne (outside away)).2.trans (frame j away).2⟩
  refine ⟨v,D,_,y,z,F,n,exec,exec.seq back,same.trans user,?_,fun i => empty _ (member i),ready.returnPayload
    (fun i ne => keep _ (bank.injective.ne ne) (fun k => disjoint k i))
    (fun k => by simpa only [List.map_ofFn] using (payload k).symm),effect,keep⟩
  rw [← span] at cost
  dsimp only [T,V] at paid cost ⊢
  simp only [Nat.add_mul] at paid cost ⊢
  omega

/-- Copy the active record payload onto a fresh child input tape. Only the destination
right stack changes, and the source keeps its original tape position. -/
theorem loadActivePayload {P U : Type} {T Q w W : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin 35 ↪ Fin T) (tmp dst : Fin T) (apart : [bank 24,tmp,dst].Nodup)
    (record : List (Fin (prime+4))) (word : Fin ((prime^(w+1))^16*W) → ZMod 2)
    (u : HS T Q prime U) (S : Stacks T prime)
    (ready : RecordReady (b := prime) (w := w) (d := 16) (W := W) bank
      (prime^(w+1)).size W.size record SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 word S)
    (left : S.L tmp = []) (right : S.R tmp = []) (fresh : S.R dst = []) :
    ∃ z, z.user = u.user ∧ Exec body (loadCompactWord (bank 24) tmp dst) (mk u S)
      (8*((prime^(w+1))^16*W)+10) (mk z {S with R := Function.update S.R dst (List.ofFn fun i => SparseRoleCircuit.encode (word i))}) := by
  have read := activeRecordWord bank record word S ready (Equiv.refl _)
  simpa only [fresh,List.append_nil] using loadCompactWord_exec body (bank 24) tmp dst apart word u S read left right

/-- Load a positioned active payload and distribute its successive cells
cyclically among the 142080 child rows. -/
theorem splitActivePayload {P U : Type} {T Q w W m : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin 35 ↪ Fin T) (rows : Fin intervalSplitTapes ↪ Fin T) (tmp : Fin T)
    (apart : [bank 24,tmp,rows 0].Nodup)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (positive : 0 < m) (span : m*142080 = (prime^(w+1))^16*W)
    (record : List (Fin (prime+4))) (word : Fin ((prime^(w+1))^16*W) → ZMod 2)
    (u : HS T Q prime U) (S : Stacks T prime)
    (ready : RecordReady (b := prime) (w := w) (d := 16) (W := W) bank
      (prime^(w+1)).size W.size record SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 word S)
    (scratch : S.L tmp = [] ∧ S.R tmp = []) (free : ∀ j, S.L (rows j) = [] ∧ S.R (rows j) = []) :
    let input := fun k => word (Fin.cast span k)
    let split : Pr Empty intervalSplitTapes Q prime U := intervalPrepare.seq
      (foreign (liftQ (CyclicRowNormalized.splitProgram 142080 prime) capacity))
    ∃ z F t, Exec body ((loadCompactWord (bank 24) tmp (rows 0)).seq (embProg rows Empty.elim split))
      (mk u S) t (mk z F) ∧ z.user = u.user ∧
      t ≤ (149*(intervalSplitTapes+5)+13)*(m*142080)+34 ∧
      RepT (intervalOwnerBank (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ input)))
        (fun r i => input (finProdFinEquiv (i,r)))) (embStk rows F).L (embStk rows F).R ∧
      ∀ j, (∀ i, rows i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro input split
  obtain ⟨v,user,load⟩ := loadActivePayload body bank tmp (rows 0) apart record word u S ready
    scratch.1 scratch.2 (free 0).2
  let D := {S with R := Function.update S.R (rows 0) (List.ofFn fun i => SparseRoleCircuit.encode (word i))}
  have source : D.R (rows 0) = List.ofFn (SparseRoleCircuit.encode ∘ input) := by
    simp only [D,Function.update_self,input,Function.comp_def]
    have castWord {a b : ℕ} (h : a=b) (f : Fin b → Fin (prime+4)) :
        List.ofFn f = List.ofFn (fun k => f (k.cast h)) := by subst b; rfl
    exact castWord span _
  obtain ⟨z,F,t,run,same,paid,out,frame⟩ := splitEncoded_exec body rows capacity positive input v D source
    (fun j => (free j).1) (fun j ne => (Function.update_of_ne (rows.injective.ne ne) ..).trans (free j).2)
  refine ⟨z,F,_,Exec.seq load run,same.trans user,?_,out,?_⟩
  · rw [← span]
    simp only [Nat.add_mul] at paid ⊢
    omega
  · intro j off
    exact ⟨(frame j off).1,(frame j off).2.trans (Function.update_of_ne (off 0).symm ..)⟩

/-- The physical split and merge in `inheritedInterval_exec` require the
ordinary row transpose. On a packed MOVE row the child supplies it directly. -/
theorem packedMoveRows {P U : Type} {N Q price : ℕ} (atom W : ℕ)
    {body : P → Pr P N Q prime U} {code src dst seed} :
    let lane := packedDescriptor (64*atom) W
    PackedPieceHandoff (volume prime lane) (packedChildOutput atom _) body code src dst seed price →
    PackedPieceHandoff (volume prime lane) (fun x y => ∀ r : Fin 142080,
      y r.castSucc = Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (x r.castSucc))
      body code src dst seed price := by
  intro lane child x u S words privateTapes
  obtain ⟨z,F,t,y,run,paid,user,out,effect⟩ := child x u S words privateTapes
  refine ⟨z,F,t,y,run,paid,user,out,?_⟩
  have position : packedChildPosition lane rfl = Equiv.refl _ := by
    ext i
    exact packActive_packed (64*atom) W i
  intro r
  simpa only [position,Equiv.refl_apply,Function.comp_def] using effect r lane rfl rfl

/-- Recover the physical MOVE row worker directly from the recursive
descriptor contract. Dividing the spectator field by the owner count leaves
the two transposed fields intact. -/
theorem activeMoveRowWorker {U : Type} {Q time : ℕ} (child : Descriptor)
    (split : 142080 ∣ child.rows) (run : PackedDescriptorHandoff U Q child time) :
    let W := CopyChildLayout.spectators child / 142080
    let lane := packedDescriptor child.width W
    W*142080 = CopyChildLayout.spectators child ∧
      PackedWindowHandoff U Q (volume prime lane) (fun x y => ∀ r : Fin 142080,
        y r.castSucc = Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (x r.castSucc)) time := by
  intro W lane
  obtain ⟨groups,rows⟩ := split
  have spectator : CopyChildLayout.spectators child =
      (child.beforeRows*groups*child.beforeH*child.between*child.afterD)*142080 := by
    rw [CopyChildLayout.spectators,rows]
    ring
  have suffix : W = child.beforeRows*groups*child.beforeH*child.between*child.afterD := by
    dsimp only [W]
    rw [spectator,Nat.mul_div_cancel _ (by decide)]
  refine ⟨by rw [suffix,spectator],?_⟩
  have size : volume prime child / 142080 = volume prime lane := by
    have total : volume prime child = volume prime lane * 142080 := by
      dsimp only [lane,volume,packedDescriptor]
      rw [suffix,rows]
      ring
    rw [total,Nat.mul_div_cancel _ (by decide)]
  obtain ⟨⟨atom,width⟩,call⟩ := run
  change PackedWindowHandoff U Q (volume prime child / 142080) (packedChildOutput (child.width/64) _) time at call
  rw [size,show child.width/64 = atom by rw [width,Nat.mul_div_cancel_left _ (by decide)]] at call
  dsimp only [lane] at call ⊢
  rw [width] at call ⊢
  obtain ⟨P,T,body,code,src,dst,seed,worker⟩ := call
  exact ⟨P,T,body,code,src,dst,seed,packedMoveRows atom W worker⟩

/-- Split a packed MOVE, execute its recursive row worker and merge. The
merged word realizes the scheduled transpose in the caller's packed order. -/
theorem activeMoveInterval {U : Type} {Q time : ℕ} (child : Descriptor)
    (split : 142080 ∣ child.rows) (run : PackedDescriptorHandoff U Q child time)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    let W := CopyChildLayout.spectators child / 142080
    let lane := packedDescriptor child.width W
    let wide := {lane with afterD := lane.afterD*142080}
    0 < volume prime lane →
    ∃ (P : Type) (N : ℕ) (seed : Stacks N prime),
      IntervalRun (P := P) (U := U) (Q := Q) seed time lane (fun x y =>
        ∀ (position : Fin (volume prime child) ≃ Fin (volume prime wide)),
          (∀ k, (position k).val = (CopyChildLayout.packActive child k).val) →
          ∀ k, y (position k) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x ∘ position) k) := by
  intro W lane wide positive
  obtain ⟨_,P,N,body,code,src,dst,seed,worker⟩ := activeMoveRowWorker child split run
  refine ⟨P,N,seed,intervalRun_of_transpose lane positive capacity worker _ ?_⟩
  intro x position packed
  have coords : InheritedIntervalPositions child wide rfl position := fun k =>
    (packed k).symm.trans (packActive_packed child.width (W*142080) (position k)).symm
  exact (coords.transpose_iff rfl x _).2 rfl

/-- The prepared MOVE worker pays linear overhead on the full word. Its
split and merge preserve the already packed layout at every atom width. -/
theorem activeMoveWorker {U : Type} {Q price : ℕ} (child : Descriptor)
    (split : 142080 ∣ child.rows) (recursive : PackedDescriptorHandoff U Q child price)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    let lane := packedDescriptor child.width (CopyChildLayout.spectators child / 142080)
    let wide := {lane with afterD := lane.afterD*142080}
    let m := volume prime wide
    0 < volume prime lane →
    ∃ (P : Type) (H : ℕ) (slot : Fin H) (host : P → Pr P H Q prime U)
      (code : Pr P H Q prime U) (stock : Stacks H prime),
    ∀ (x : Fin m → ZMod 2) u (S : Stacks H prime), S.L slot = [] →
      S.R slot = List.ofFn (fun k => SparseRoleCircuit.encode (x k)) →
      (∀ j, j ≠ slot → S.L j = stock.L j ∧ S.R j = stock.R j) →
      ∃ z F n y, Exec host code (mk u S) n (mk z F) ∧
        n ≤ price+(298*(intervalSplitTapes+5)+25)*m ∧ z.user = u.user ∧
        RecordPayload slot (fun _ => blank) 0 y F ∧
        ∀ (position : Fin (volume prime child) ≃ Fin m),
          (∀ k, (position k).val = (CopyChildLayout.packActive child k).val) →
          ∀ k, y (position k) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x ∘ position) k := by
  intro lane wide m positive
  obtain ⟨P,N,seed,run⟩ := activeMoveInterval child split recursive capacity positive
  obtain ⟨host,code,stock,execute⟩ := inheritedSeededWorker_exec lane run
  refine ⟨Empty ⊕ P,_,((0 : Fin intervalSplitTapes).natAdd 142082).castAdd N,host,code,stock,?_⟩
  intro x u S left right fresh
  obtain ⟨z,F,n,y,exec,paid,user,payload,reads⟩ := execute x u S left right fresh
  refine ⟨z,F,n,y,exec,?_,user,payload,reads⟩
  have size : m = volume prime lane*142080 := by simp [m,wide,volume,Nat.mul_assoc]
  rw [size]
  change n ≤ (149*(intervalSplitTapes+5)+5)*(volume prime lane*142080)+24+
    ((142081*(8*volume prime lane+10)+1+price)+(149*(volume prime lane*142080)*(intervalSplitTapes+5)+6)) at paid
  norm_num [intervalSplitTapes] at paid ⊢
  omega

/-- A worker acting on the positioned payload can resume the caller directly
when it restores every other tape. This also restores the saved stack. -/
theorem bankTransposeOfPayload {P U : Type} {n T Q w W : ℕ} {node child : Descriptor}
    (ports : Fin (n+35) ↪ Fin T) (record : List (Fin (prime+4)))
    (position : Fin (volume prime child) ≃ Fin ((prime^(w+1))^16*W))
    (body : P → Pr P T Q prime U) (code : Pr P T Q prime U) (budget : ℕ) :
    let bank := scheduledRecordPorts ports
    let stored := RecordReady (b := prime) (w := w) (d := 16) (W := W) bank (prime^(w+1)).size W.size record
      SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
    (child.width < node.width → ∀ u S word, stored word S →
      (∀ i : Fin (n+35), 35 ≤ i.val → S.L (ports i) = [] ∧ S.R (ports i) = []) →
      ∃ z F t y, Exec body code (mk u S) t (mk z F) ∧ t ≤ budget ∧ z.user = u.user ∧
        (∀ k, readAt blank (F.L (bank 24)) (F.R (bank 24)) (k-0) =
          RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ y)) k)) ∧
        (∀ j, j ≠ bank 24 → F.L j = S.L j ∧ F.R j = S.R j) ∧
        ∀ h, y (position h) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) h) →
      MoveOnBankExec node child w W ports record position body code budget := by
  intro bank stored worker smaller _ _ _ u S word ready clean
  obtain ⟨z,F,t,y,run,paid,user,out,rest,reads⟩ := worker smaller u S word ready clean
  refine ⟨z,F,t,y,run,paid,user,ready.returnPayload (fun i ne => rest _ (bank.injective.ne ne))
    (fun k => (out k).symm),?_,(rest _ (bank.injective.ne (by decide : (34 : Fin 35) ≠ 24))).1,?_,reads⟩
  · intro i high
    have ne : ports i ≠ bank 24 := by
      intro eq
      have h := congrArg Fin.val (ports.injective eq)
      change i.val = 24 at h
      omega
    exact ⟨(rest _ ne).1.trans (clean i high).1,(rest _ ne).2.trans (clean i high).2⟩
  · intro j away
    exact rest _ (away _).symm

/-- A transpose worker that returns its saved stack also supplies a COPY call
on the full row-swap bank. Both calls use the same child budget. -/
theorem copyOfBankTranspose [M8.Machine.Net] {P U : Type} {T Q : ℕ} {node child : Descriptor}
    {w W : ℕ} {ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T} {record : List (Fin (prime+4))}
    {position : Fin (volume prime child) ≃ Fin ((prime^(w+1))^16*W)}
    {body : P → Pr P T Q prime U} {f : P} {budget : ℕ}
    (worker : MoveOnBankExec node child w W ports record position body (body f) budget) :
    ScheduledChildExec node child w W ports record position body f budget := by
  intro smaller u S word ready clean
  obtain ⟨z,F,t,y,run,paid,user,out,workspace,_,off,reads⟩ := worker smaller u S word ready clean
  exact ⟨z,F,t,y,run,paid,user,out,workspace,off,reads⟩

/-- When the dispatch header fits in the active parent width, each scheduled
call needs exactly its ordinary budget as an upper bound. -/
theorem activePackedSweep [M8.Machine.Net] (n : Fin 9) :
    ∃ (mt : StageRun → MoveIndex → ℕ) (ct : StageRun → CopyIndex → ℕ)
      (mr : ∀ p i, Fin (rowSwapBlock.tapes+35) ↪ Fin (mt p i))
      (cr : ∀ p j, Fin (rowSwapBlock.tapes+35) ↪ Fin (ct p j)) (states : ℕ) (leafRate : ℝ),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q →
    ∀ (ml : ∀ p i, P → Pr (WorkerLabel P) (mt p i) Q prime U) (mf : StageRun → MoveIndex → P)
      (cl : ∀ p j, P → Pr (WorkerLabel P) (ct p j) Q prime U) (cf : StageRun → CopyIndex → P),
    ∃ (mb : ∀ p i, WorkerLabel P → Pr (WorkerLabel P) (mt p i) Q prime U)
      (cb : ∀ p j, WorkerLabel P → Pr (WorkerLabel P) (ct p j) Q prime U) (coeff : StageRun → ℝ),
      (∀ p i f, mb p i (.active f) = ml p i f) ∧ (∀ p j f, cb p j (.active f) = cl p j f) ∧
      ∀ (node : Descriptor) (w B rows cutoff : ℕ), node.width = 64*(w+1) → node.rows = 142080*rows →
      node.beforeH = B*prime^(64*((w+1)*64)) →
      let K := node.beforeRows*rows*node.between*node.afterD
      let W := ((prime^(w+1))^112*B)*prime^(64*((w+1)*64))*K
      0 < W → ∀ rate : ℝ, leafRate ≤ rate →
      let mi := fun (p : StageRun) (i : MoveIndex) => phaseChildPositions.choose (n,p,i)
      let ci := fun (p : StageRun) (j : CopyIndex) => copyChildPosition (n,p,j)
      let child := scheduledChild prime node
      ∀ (budget : Fin nodeChildren5.length → ℕ),
      ∀ (root : Descriptor) (path : List (Fin nodeChildren5.length)),
      node = path.foldl (scheduledChild prime) root → root.width.size ≤ cutoff → cutoff < node.width →
      let L := root.width.size
      let price := fun i => if cutoff < (child i).width then budget i else
        ⌊(rate*((child i).width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime (child i)⌋₊
      ∃ (mp : ∀ p i, Fin (volume prime (child (mi p i))) ≃ Fin ((prime^(w+1))^16*W))
        (cp : ∀ p j, Fin (volume prime (child (ci p j))) ≃ Fin ((prime^(w+1))^16*W)),
      (∀ p i h, (mp p i h).val = (CopyChildLayout.packActive (child (mi p i)) h).val) ∧
      (∀ p j, CopyIntervalPositions (child (ci p j)) (w+1) W (cp p j)) ∧
        ((∀ p i, let k := mi p i; cutoff < (child k).width → (child k).width < node.width →
            MoveOnBankExec node (child k) w W (movePrefix.trans (mr p i)) (binSyms L cutoff) (mp p i) (mb p i) (mb p i (.active (mf p i))) (budget k)) →
          (∀ p j, let k := ci p j; cutoff < (child k).width → (child k).width < node.width →
            MoveOnBankExec node (child k) w W (cr p j) (binSyms L cutoff) (cp p j) (cb p j) (cb p j (.active (cf p j))) (budget k)) →
      ∃ (Label : Type) (tapes : StageRun → ℕ) (body : ∀ p, Label → Pr Label (tapes p) Q prime U),
        PackedStageExecution (w := w+1) (B := B) (K := K) n tapes body coeff (fun time => ∀ k : Fin nodeChildren5.length, price k ≤ time k.val)) := by
  obtain ⟨mt,ct,mr,cr,states,leafRate,build⟩ := mixedPackedSweep n
  refine ⟨mt,ct,mr,cr,states,leafRate,?_⟩
  intro P U Q room ml mf cl cf
  obtain ⟨mb,cb,coeff,move,copy,stage⟩ := build room ml mf cl cf
  refine ⟨mb,cb,coeff,move,copy,?_⟩
  intro node w B rows cutoff width split label K W live rate enough mi ci child budget root path atPath header active L price
  have shrink := scheduledPath_width_le prime root path
  rw [← atPath] at shrink
  have powers : 42^path.length ≤ 64^path.length := Nat.pow_le_pow_left (by decide) _
  have le : node.width ≤ root.width := Nat.le_of_mul_le_mul_right
    (shrink.trans (Nat.mul_le_mul_left _ powers)) (pow_pos (by decide : 0 < 64) _)
  have fits : cutoff < 2^L := (active.trans_le le).trans (Nat.lt_size_self root.width)
  have bits : node.width.size ≤ L := Nat.size_le_size le
  have short : L ≤ node.width := header.trans active.le
  obtain ⟨mp,cp,mpPos,cpPos,Label,tapes,body,run⟩ :=
    stage node w B rows cutoff width split label live rate enough budget L fits bits
  refine ⟨mp,cp,mpPos,cpPos,?_⟩
  intro moves copies
  obtain ⟨T,fan,bank,execute⟩ := run
  refine ⟨Label,tapes,body,T,fan,bank,?_⟩
  intro scratch owner worker host blocks V time paid
  exact execute time ⟨by simpa only [Nat.sub_eq_zero_of_le short,Nat.mul_zero,Nat.add_zero] using paid,
    moves,fun p j above smaller => copyOfBankTranspose (copies p j above smaller)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
