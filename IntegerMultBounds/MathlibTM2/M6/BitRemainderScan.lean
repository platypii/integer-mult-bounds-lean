module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderRun
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGeneratedGoodRecord

/-! Instantiate the generated cover scan with the physical PR589 idle child. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume role)
open IntegerMultBounds.MathlibTM2.Cover
open IntegerMultBounds.MathlibTM2.Cover.Fallback M8.RevMachine

/-- Loading or draining a row on caller tape 24 preserves all pending
directory entries, headers, pivot schedules and private work tapes. -/
theorem directoryReady_updatePayload {m K w W H J : ℕ} {v : Descriptor}
    {proj : Matrix (Fin m) (Fin m) ℚ} {parent : Fin m → ZMod (prime^(w+1))}
    {prefixes : ℕ → List (Fin (prime+4))} {archiveTail : List (Fin (prime+4))}
    {schedules : List ℕ → List (Fin (prime+4))} {S : Host.Stacks (66+K) prime} {pending : List ℕ}
    (ready : DirectoryReady v proj w W H J parent prefixes archiveTail schedules S pending)
    (xs : List (Fin (prime+4))) :
    DirectoryReady v proj w W H J parent prefixes archiveTail schedules
      {S with R := Function.update S.R ((24 : Fin 66).castAdd K) xs} pending := by
  let caller := Fin.castAddEmb (n := 66) K
  have keep (i : Fin 66) (h : i ≠ 24) := Function.update_of_ne (caller.injective.ne h) xs S.R
  obtain ⟨dir,width,privateFree,scratch,⟨suffix,matrix⟩,base,unit,trailing,headers,one,clock,parents,pivots⟩ := ready
  refine ⟨(keep 46 (by decide)).trans dir,fun j hj => (congrArg List.length (keep 47 (by decide))).trans (width j hj),
    ?_,(keep 49 (by decide)).trans scratch,⟨suffix,(keep 48 (by decide)).trans matrix⟩,
    (keep 2 (by decide)).trans base,(keep 28 (by decide)).trans unit,(keep 53 (by decide)).trans trailing,
    ?_,(keep 44 (by decide)).trans one,(congrArg List.length (keep 45 (by decide))).trans clock,
    (keep 55 (by decide)).trans parents,(keep 54 (by decide)).trans pivots⟩
  · intro i hi
    have off : i ≠ (24 : Fin 66).castAdd K := by intro eq; subst i; change 58 ≤ 24 at hi; omega
    exact ⟨(privateFree i hi).1,(Function.update_of_ne off xs S.R).trans (privateFree i hi).2⟩
  · intro i
    apply (keep _ ?_).trans (headers i)
    intro eq
    have h := congrArg Fin.val eq
    change 33+i.val = 24 at h
    omega

/-- The same payload write on the full archive machine also preserves the
matrix stream and the live and exceptional selectors. -/
theorem archiveReady_updatePayload [M8.Machine.Net] {m K d w W H J : ℕ} {v : Descriptor}
    {proj : Matrix (Fin m) (Fin m) ℚ} {parent : Fin m → ZMod (prime^(w+1))}
    {prefixes : ℕ → List (Fin (prime+4))} {archiveTail : List (Fin (prime+4))}
    {schedules : List ℕ → List (Fin (prime+4))} {S : Host.Stacks (66+(K+1)) prime} {pending : List ℕ}
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K+1)
    (xs : List (Fin (prime+4))) :
    let bank := directoryOrdinaryBank room
    let caller := Fin.castAddEmb (n := 66) (K+1)
    let F := {S with R := Function.update S.R (caller 24) xs}
    DirectoryReady v proj w W H J parent prefixes archiveTail schedules (Host.embStk bank S) pending →
    DirectoryReady v proj w W H J parent prefixes archiveTail schedules (Host.embStk bank F) pending ∧
      F.R (directoryMatrixTape room) = S.R (directoryMatrixTape room) ∧
      F.R (caller 57) = S.R (caller 57) ∧ F.R (caller 56) = S.R (caller 56) := by
  intro bank caller F ready
  have cell : bank ((24 : Fin 66).castAdd K) = caller 24 := directoryOrdinaryBank_caller room 24
  have off : directoryMatrixTape room ≠ caller 24 := by
    intro eq
    have h := directoryMatrixTape_private room
    rw [eq] at h
    change 66 ≤ 24 at h
    omega
  refine ⟨?_,Function.update_of_ne off xs S.R,Function.update_of_ne (caller.injective.ne (by decide : (57 : Fin 66) ≠ 24)) xs S.R,
    Function.update_of_ne (caller.injective.ne (by decide : (56 : Fin 66) ≠ 24)) xs S.R⟩
  have same : Host.embStk bank F = {Host.embStk bank S with R := (Function.update (Host.embStk bank S).R
      ((24 : Fin 66).castAdd K) xs)} := by
    unfold Host.embStk F
    congr 1
    funext i
    by_cases h : i = (24 : Fin 66).castAdd K <;>
      simp [Function.comp_def,← cell,bank.injective.eq_iff,h,Function.update_of_ne]
  rw [same]
  exact directoryReady_updatePayload ready xs

/-- A record keeps the middle and trailing spectators. The prefix (including
the cover label) selects the record, so it contributes to its count exactly once. -/
theorem remainderRecord_volume (v : Descriptor) (w rows : ℕ) (e : ℕ × ℕ)
    (he : e ∈ BitHosting.remainderIntervals) (width : v.width = 64*(w+1))
    (split : v.rows = 142080*rows) :
    let directory := role v 142080
    let child := phaseIntervalChild e.1 e.2 (w+1) (v.between*v.afterD) 64
    LabelMask.records directory * volume prime child * 142080 = volume prime v := by
  intro directory child
  obtain ⟨ordered,upper,_⟩ := BitHosting.remainder_counts e he
  rw [intervalChild_volume ordered (show e.2 ≤ 64 by omega)]
  simp only [LabelMask.records,directory,role,volume,width,split,
    Nat.mul_div_cancel_left _ (by decide : 0 < 142080),show 64*(w+1) = (w+1)*64 by omega,
    pow_mul,pow_add]
  ac_rfl

open IntegerMultBounds.MathlibTM2.Stack Host Mult.PhaseCellToeplitz

/-- Dispatch one loaded owner record, consuming both selector bits even for
padding. The enclosing owner loop supplies the iteration test. -/
noncomputable def ownerDispatch {P U : Type} {T Q : ℕ} (mask mode : Fin T) (good exceptional padding : Pr P T Q prime U) :
    Pr P T Q prime U :=
  (.act (nextPivotBit mask) : Pr P T Q prime U).seq (.cond (·.flag)
    ((.act (nextPivotBit mode) : Pr P T Q prime U).seq (.cond (·.flag) exceptional good))
    ((.act (nextPivotBit mode) : Pr P T Q prime U).seq padding))

theorem ownerDispatch_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (mask mode : Fin T) (apart : mask ≠ mode) (good exceptional padding : Pr P T Q prime U)
    (live bad : Bool) (u : HS T Q prime U) (S : Stacks T prime) (ls bs : List (Fin (prime+4)))
    (liveBits : S.R mask = bitSymbol live :: ls) (badBits : S.R mode = bitSymbol bad :: bs) :
    let B := {S with R := Function.update S.R mask ls}
    let E := {B with R := Function.update B.R mode bs}
    ∀ {z F n}, Exec body (if live then (if bad then exceptional else good) else padding)
      (mk {u with flag := bad} E) n (mk z F) →
      Exec body (ownerDispatch mask mode good exceptional padding) (mk u S)
        (n + (if live then 4 else 3)) (mk z F) := by
  intro B E z F n run
  have firstBit : Exec body (.act (nextPivotBit mask)) (mk u S) 1 (mk {u with flag := live} B) := by
    simpa [nextPivotBit,Action.run,liveBits,update_rt,B] using Exec.act (body := body) (nextPivotBit mask) (mk u S)
  have bits : B.R mode = bitSymbol bad :: bs := (Function.update_of_ne apart.symm ls S.R).trans badBits
  have secondBit : Exec body (.act (nextPivotBit mode)) (mk {u with flag := live} B) 1 (mk {u with flag := bad} E) := by
    simpa [nextPivotBit,Action.run,bits,update_rt,E] using
      Exec.act (body := body) (nextPivotBit mode) (mk {u with flag := live} B)
  cases live with
  | false =>
    exact Exec.cast (Exec.seq firstBit (.cond_false rfl (Exec.seq secondBit run))) (by simp; omega) rfl
  | true =>
    cases bad with
    | false => exact Exec.cast (Exec.seq firstBit (.cond_true rfl (Exec.seq secondBit (.cond_false rfl run)))) (by simp; omega) rfl
    | true => exact Exec.cast (Exec.seq firstBit (.cond_true rfl (Exec.seq secondBit (.cond_true rfl run)))) (by simp; omega) rfl

private theorem ownerSelectors_frame [M8.Machine.Net] {m d K w W H J N : ℕ} {v : Descriptor}
    {proj : Matrix (Fin m) (Fin m) ℚ} {parent : Fin m → ZMod (prime^(w+1))}
    {prefixes : ℕ → List (Fin (prime+4))} {archiveTail : List (Fin (prime+4))}
    {schedule : List ℕ → List (Fin (prime+4))} {pending : List ℕ}
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K+1) (S : Stacks (66+(K+1)) prime)
    (ls bs : List (Fin (prime+4))) (original : Fin N → ZMod 2) :
    let placement := directoryOrdinaryBank room
    let caller := Fin.castAddEmb (n := 66) (K+1)
    let ready := DirectoryReady v proj w W H J parent prefixes archiveTail schedule
    let payload := fun (word : Fin N → ZMod 2) D =>
      RecordPayload ((24 : Fin 66).castAdd K) (fun _ => blank) 0 word (embStk placement D)
    let B := {S with R := Function.update S.R (caller 57) ls}
    let E := {B with R := Function.update B.R (caller 56) bs}
    ready (embStk placement S) pending → payload original S →
      ready (embStk placement E) pending ∧ payload original E ∧ E.R (directoryMatrixTape room) = S.R (directoryMatrixTape room) := by
  intro placement caller ready payload B E start input
  have update (D : Stacks (66+(K+1)) prime) (i : Fin 66) (xs : List (Fin (prime+4))) :
      embStk placement {D with R := Function.update D.R (caller i) xs} =
        {embStk placement D with R := Function.update (embStk placement D).R (i.castAdd K) xs} := by
    have cell : placement (i.castAdd K) = caller i := directoryOrdinaryBank_caller room i
    unfold embStk
    congr 1
    funext k
    by_cases h : k = i.castAdd K <;> simp [Function.comp_def,← cell,placement.injective.eq_iff,h,Function.update_of_ne]
  have readyE : ready (embStk placement E) pending := by
    unfold E B
    rw [update,update]
    exact DirectoryReady.updateSelector 56 (by decide) (by decide) _ (DirectoryReady.updateSelector 57 (by decide) (by decide) _ start)
  have off (i : Fin 66) : directoryMatrixTape room ≠ caller i := by
    intro eq
    have h := directoryMatrixTape_private room
    rw [eq] at h
    exact i.isLt.not_ge h
  have inputE : payload original E := by
    unfold payload E B
    rw [update,update]
    simpa [payload,RecordPayload,Function.update_of_ne] using input
  exact ⟨readyE,inputE,by simp [E,B,off,Function.update_of_ne]⟩

local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

open IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.Swap.Modular Matrix in
/-- Dispatch a live exceptional owner row through its physical projector and
retain the archive frame needed after draining the transformed payload. -/
theorem ownerExceptional_exec [M8.Machine.Net] {m d K w W J N : ℕ} {P U : Type}
    (dimension : m+m = d+1) (v : Descriptor) (proj : Matrix (Fin m) (Fin m) ℚ)
    (idem : proj*proj = proj) (adm : Admissible prime proj)
    (parent inv : Fin m → ZMod (prime^(w+1))) (reciprocal : ∀ i, parent i * inv i = 1)
    (data : ScanData m d w W) (hm : prime^(w+1) < 2^data.H) (hw : W < 2^J) (positive : 0 < W)
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K+1)
    (capacity : (anchorProgram d true).1+(anchorProgram d false).1+1 ≤ columnCapacity)
    (body : P → Pr P (66+(K+1)) columnCapacity prime U) (c : ℕ) (bodyBound : ∀ f, mnProgPush (body f) ≤ c)
    (prefixes : ℕ → List (Fin (prime+4))) (archiveTail : List (Fin (prime+4)))
    (bad : ℕ → Bool) (j : ℕ) (inside : j < data.records)
    (live : LabelStock.live m (w+1) 1 j = true) (exceptional : bad j = true)
    (length : N = (prime^(w+1))^m*((prime^(w+1))^m*W)) (original : Fin N → ZMod 2)
    (u : HS (66+(K+1)) columnCapacity prime U) (S : Stacks (66+(K+1)) prime) :
    let e := finSumFinEquiv.trans (finCongr dimension)
    let physical := data.physical e proj parent inv
    let φ := LabelRing.res prime (w+1) (by omega)
    let code := fun k => residualSchedule (A := prime) (projectorResidual finSumFinEquiv (reduce prime proj)
      (φ ∘ parent) (φ ∘ inv) (LabelStock.residue m (w+1) 1 k))
    let schedule := fun (xs : List ℕ) => xs.flatMap fun k => if bad k then code k else []
    let ready := DirectoryReady v proj w W data.H J parent prefixes archiveTail schedule
    let placement := directoryOrdinaryBank room
    let caller := Fin.castAddEmb (n := 66) (K+1)
    let payload := fun (word : Fin N → ZMod 2) D =>
      RecordPayload ((24 : Fin 66).castAdd K) (fun _ => blank) 0 word (embStk placement D)
    let labels := (List.range data.records).drop (j+1)
    ready (embStk placement S) ((List.range data.records).drop j) → S.R (directoryMatrixTape room) = physical.matrices j →
    (good padding : Pr P (66+(K+1)) columnCapacity prime U) →
    (ls bs : List (Fin (prime+4))) →
    S.R (caller 57) = bitSymbol true :: ls → S.R (caller 56) = bitSymbol true :: bs →
    payload original S →
    let C := physical.table (LabelStock.residue m (w+1) 1 j)
    let rows := classPivots C
    let privateTapes := (List.finRange (66+(K+1))).filter fun i => decide (58 ≤ i.val ∧ i ≠ directoryMatrixTape room)
    ∃ z D n next, z.user = u.user ∧ n ≤ exceptionalRecordTime U rows (negativeAnchor rows C) m w W data.H J
      privateTapes.length (max (mnProgPush (directoryExceptionalCore (P := P) (U := U) d room capacity)) c) (prefixes j).length + 4 ∧
      Exec body (ownerDispatch (caller 57) (caller 56) good (directoryExceptionalProgram m d room capacity) padding) (mk u S) n (mk z D) ∧
      ready (embStk placement D) labels ∧ D.R (directoryMatrixTape room) = physical.matrices (j+1) ∧
      (∀ x k, next ((FlatCoordinateLayout.index ((projectorResidual e (reduce (prime^(w+1)) proj) parent inv
        (physicalLabel m (w+1) j)).mulVec x) k).cast (directoryPayloadLength e length)) = original ((FlatCoordinateLayout.index x k).cast (directoryPayloadLength e length))) ∧
      payload next D ∧
      let drained := {D with R := Function.update D.R (caller 24) ((D.R (caller 24)).drop N)}
      ready (embStk placement drained) labels ∧ drained.R (directoryMatrixTape room) = physical.matrices (j+1) ∧
      drained.R (caller 57) = ls ∧ drained.R (caller 56) = bs := by
  intro e physical φ code schedule ready placement caller payload labels start matrix good padding ls bs liveBits badBits input C rows privateTapes
  let B := {S with R := Function.update S.R (caller 57) ls}
  let E := {B with R := Function.update B.R (caller 56) bs}
  obtain ⟨readyE,inputE,archiveE⟩ := ownerSelectors_frame room S ls bs original start input
  obtain ⟨z,D,n,next,user,time,run,done,tail,action,out,mask,mode⟩ :=
    DirectoryReady.runExceptional dimension v proj idem adm parent inv reciprocal data hm hw positive room capacity
      body c bodyBound prefixes archiveTail bad j inside live exceptional (fun _ => blank) 0 length original
      {u with flag := true} E readyE (archiveE.trans matrix) inputE
  have dispatch := ownerDispatch_exec body (caller 57) (caller 56) (caller.injective.ne (by decide : (57 : Fin 66) ≠ 56))
    good (directoryExceptionalProgram m d room capacity) padding true true u S ls bs liveBits badBits run
  obtain ⟨restored,archive,keepLive,keepBad⟩ := archiveReady_updatePayload room ((D.R (caller 24)).drop N) done
  refine ⟨z,D,_,next,user,Nat.add_le_add_right time 4,dispatch,done,tail,action,out,restored,archive.trans tail,?_,?_⟩
  · exact keepLive.trans (mask.trans (by simp [E,B,caller,Function.update_of_ne]))
  · exact keepBad.trans (mode.trans (Function.update_self (caller 56) bs B.R))

/-- Good and padding calls consume the same archive entry. The placed
ordinary executor includes the matrix advance in its budget. -/
theorem ownerOrdinary_exec [M8.Machine.Net] {m d K w W H J N Q : ℕ} {P U : Type}
    (v : Descriptor) (proj : Matrix (Fin m) (Fin m) ℚ) (parent : Fin m → ZMod (prime^(w+1)))
    (prefixes : ℕ → List (Fin (prime+4))) (archiveTail : List (Fin (prime+4)))
    (schedule : List ℕ → List (Fin (prime+4))) (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K+1)
    (body : P → Pr P (66+(K+1)) Q prime U) (good exceptional padding : Pr P (66+(K+1)) Q prime U)
    (live bad : Bool) (ordinary : ¬ (live = true ∧ bad = true)) (budget j : ℕ) (labels : List ℕ)
    (matrices : ℕ → List (Fin (prime+4))) (original : Fin N → ZMod 2) (effect : (Fin N → ZMod 2) → Prop)
    (u : HS (66+(K+1)) Q prime U) (S : Stacks (66+(K+1)) prime) (ls bs : List (Fin (prime+4))) :
    let placement := directoryOrdinaryBank room
    let caller := Fin.castAddEmb (n := 66) (K+1)
    let ready := DirectoryReady v proj w W H J parent prefixes archiveTail schedule
    let payload := fun (word : Fin N → ZMod 2) D =>
      RecordPayload ((24 : Fin 66).castAdd K) (fun _ => blank) 0 word (embStk placement D)
    ready (embStk placement S) (j::labels) → S.R (directoryMatrixTape room) = matrices j →
    S.R (caller 57) = bitSymbol live :: ls → S.R (caller 56) = bitSymbol bad :: bs → payload original S →
    (∀ y A, ready (embStk placement A) (j::labels) → payload original A → A.R (directoryMatrixTape room) = matrices j →
      ∃ z D n next, z.user = y.user ∧ n ≤ budget ∧ Exec body (if live then good else padding) (mk y A) n (mk z D) ∧
        ready (embStk placement D) labels ∧ effect next ∧ payload next D ∧ D.R (directoryMatrixTape room) = matrices (j+1) ∧
        D.R (caller 57) = A.R (caller 57) ∧ D.R (caller 56) = A.R (caller 56)) →
    ∃ z D n next, z.user = u.user ∧ n ≤ budget+(if live then 4 else 3) ∧
      Exec body (ownerDispatch (caller 57) (caller 56) good exceptional padding) (mk u S) n (mk z D) ∧
      effect next ∧ payload next D ∧
      let drained := {D with R := Function.update D.R (caller 24) ((D.R (caller 24)).drop N)}
      ready (embStk placement drained) labels ∧ drained.R (directoryMatrixTape room) = matrices (j+1) ∧
      drained.R (caller 57) = ls ∧ drained.R (caller 56) = bs := by
  intro placement caller ready payload start matrix liveBits badBits input call
  let B := {S with R := Function.update S.R (caller 57) ls}
  let E := {B with R := Function.update B.R (caller 56) bs}
  obtain ⟨readyE,inputE,archiveE⟩ := ownerSelectors_frame room S ls bs original start input
  obtain ⟨z,D,n,next,user,time,run,done,action,out,tail,mask,mode⟩ := call {u with flag := bad} E readyE inputE
    (archiveE.trans matrix)
  have branch : (if live then (if bad then exceptional else good) else padding) = (if live then good else padding) := by
    cases live <;> cases bad <;> first | rfl | exact (ordinary ⟨rfl,rfl⟩).elim
  have dispatch := ownerDispatch_exec body (caller 57) (caller 56) (caller.injective.ne (by decide : (57 : Fin 66) ≠ 56))
    good exceptional padding live bad u S ls bs liveBits badBits (branch ▸ run)
  obtain ⟨restored,archive,keepLive,keepBad⟩ := archiveReady_updatePayload room ((D.R (caller 24)).drop N) done
  exact ⟨z,D,_,next,user,Nat.add_le_add_right time _,dispatch,action,out,restored,archive.trans tail,
    keepLive.trans (mask.trans (by simp [E,B,caller,Function.update_of_ne])),
    keepBad.trans (mode.trans (Function.update_self (caller 56) bs B.R))⟩

/-- The packed owner word is the concatenation of the payloads in physical
directory order. Each record occupies one contiguous range on the queue. -/
theorem ownerPayload_records {R N : ℕ} (word : Fin (R*N) → ZMod 2) :
    payloadWord (SparseRoleCircuit.encode ∘ word) =
      (List.finRange R).flatMap (fun r => payloadWord (fun i : Fin N =>
        SparseRoleCircuit.encode (word (finProdFinEquiv (r,i))))) := by
  let packed := fun i => (SparseRoleCircuit.encode (word i) : Fin 4)
  have rows : List.ofFn packed = (List.ofFn fun r : Fin R => List.ofFn fun i : Fin N =>
      packed (finProdFinEquiv (r,i))).flatten := by
    simpa only [finProdFinEquiv,Equiv.coe_fn_mk,Nat.add_comm,Nat.mul_comm] using List.ofFn_mul packed
  change (List.ofFn packed).map _ = _
  rw [rows,List.map_flatten,List.ofFn_eq_map]
  simp [List.flatMap_def,List.map_map,Function.comp_def,payloadWord,packed]

/-- Load the next record of a packed owner word onto the scan's binary payload
tape. The source is left at the following record; the destination satisfies the
generated program's exact head-zero payload predicate. -/
theorem loadOwnerRecord_exec {R N T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    {count src dst saved tmp : Fin T} (layout : [count,src,dst,saved,tmp].Nodup)
    (word : Fin (R*N) → ZMod 2) (r : Fin R) (u : HS T Q prime U) (S : Stacks T prime) :
    let row := fun (j : Fin R) (i : Fin N) => word (finProdFinEquiv (j,i))
    let queue := fun n => ((List.finRange R).drop n).flatMap fun j => payloadWord (SparseRoleCircuit.encode ∘ row j)
    S.R src = queue r.val → (S.R count).length = N →
    (∀ z, readAt blank (S.L dst) (S.R dst) z = blank) → S.R saved = [] → S.R tmp = [] →
    ∃ z F, z.user = u.user ∧ Exec body (movePrefix count src dst saved tmp) (mk u S) (6*N+6) (mk z F) ∧
      F = {S with R := (Function.update (Function.update S.R src (queue (r.val+1))) dst
        (payloadWord (SparseRoleCircuit.encode ∘ row r) ++ S.R dst))} ∧
      RecordPayload dst (fun _ => blank) 0 (row r) F := by
  intro row queue input width empty hs ht
  have split : queue r.val = payloadWord (SparseRoleCircuit.encode ∘ row r) ++ queue (r.val+1) := by
    unfold queue
    rw [List.drop_eq_getElem_cons (show r.val < (List.finRange R).length by simpa using r.isLt)]
    simp
  obtain ⟨z,F,user,run,frame,read⟩ := loadPayload_exec body layout (SparseRoleCircuit.encode ∘ row r)
    (queue (r.val+1)) u S (input.trans split) width empty hs ht
  refine ⟨z,F,user,run,frame,?_⟩
  intro i
  simpa only [sub_zero,M8.AtomBank.arrTape,List.map_ofFn,Function.comp_def] using (read i).symm

/-- Drain a finished record to the output stack. The payload port reads blank
again, including when the record program has left explicit blank cells on it. -/
theorem storeOwnerRecord_exec {N T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    {count src dst tmp : Fin T} (layout : [count,src,dst,tmp].Nodup)
    (word : Fin N → ZMod 2) (u : HS T Q prime U) (S : Stacks T prime)
    (done : RecordPayload src (fun _ => blank) 0 word S) (width : (S.R count).length = N)
    (ht : S.R tmp = []) (processed : List (Fin (prime+4)))
    (stack : S.R dst = processed.reverse) :
    let bits := payloadWord (SparseRoleCircuit.encode ∘ word)
    let F := {S with R := Function.update (Function.update S.R src ((S.R src).drop N)) dst (processed ++ bits).reverse}
    ∃ z, z.user = u.user ∧ Exec body (Mult.ShortConv.transfer count src dst tmp) (mk u S) (4*N+4) (mk z F) ∧
      ∀ j, readAt blank (F.L src) (F.R src) j = blank := by
  intro bits F
  have front :=  payload_prefix_of_read word _ _ _ _ done
  have len : bits.length = N := by simp [bits,payloadWord]
  obtain ⟨z,user,run⟩ := Mult.ShortConv.transfer_exec (body := body) layout u S bits _ front (width.trans len.symm) ht
  refine ⟨z,user,by simpa only [F,List.reverse_append,← stack,len] using run,?_⟩
  have apart : src ≠ dst := by
    have off := (List.nodup_cons.mp layout.tail).1
    intro eq
    exact off (by simp [eq])
  intro j
  simp only [F,Function.update_of_ne apart,Function.update_self]
  rcases int_cases j with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · have outside := done ((N+i : ℕ) : ℤ)
    rw [sub_zero,readAt_nonneg,putWord_outside _ _ _ _ (.inr (by simp))] at outside
    rw [readAt_nonneg,List.getElem?_drop]
    exact outside
  · have outside := done (-(i+1 : ℕ))
    rw [sub_zero,readAt_neg,putWord_outside _ _ _ _ (.inl (by omega))] at outside
    rw [readAt_neg]
    exact outside

/-- Surround a payload call by one physical owner read and one reversed write.
The call may choose its output and running time from the loaded record. -/
theorem ownerRecord_exec {N T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (port : Fin T) (record : Pr P T Q prime U) (input : Fin N → ZMod 2)
    (effect : (Fin N → ZMod 2) → Prop) (ready : Stacks T prime → Prop)
    (tail processed : List (Fin (prime+4))) (budget : ℕ)
    (u : HS (T+5) Q prime U) (S : Stacks (T+5) prime) :
    let bank := fun i : Fin T => i.castAdd 5
    let reg := fun j : Fin 5 => Fin.natAdd T j
    let outer := fun f => embProg bank id (body f)
    let bits := payloadWord (SparseRoleCircuit.encode ∘ input)
    let loaded := {embStk bank S with R := Function.update (embStk bank S).R port (bits ++ S.R (bank port))}
    S.R (reg 0) = bits ++ tail → S.R (reg 1) = processed.reverse → (S.R (reg 2)).length = N →
    S.R (reg 3) = [] → S.R (reg 4) = [] → (∀ j, readAt blank (S.L (bank port)) (S.R (bank port)) j = blank) →
    (∀ y : HS T Q prime U, y.user = u.user → RecordPayload port (fun _ => blank) 0 input loaded →
      ∃ z B n word, z.user = y.user ∧ n ≤ budget ∧ Exec body record (mk y loaded) n (mk z B) ∧
        effect word ∧ RecordPayload port (fun _ => blank) 0 word B ∧
        ready {B with R := Function.update B.R port ((B.R port).drop N)}) →
    ∃ z F n word, z.user = u.user ∧ n ≤ 6*N+6+budget+(4*N+4) ∧
      Exec outer (((movePrefix (reg 2) (reg 0) (bank port) (reg 3) (reg 4)).seq (embProg bank id record)).seq
        (Mult.ShortConv.transfer (reg 2) (bank port) (reg 1) (reg 4))) (mk u S) n (mk z F) ∧
      effect word ∧ ready (embStk bank F) ∧ F.R (reg 0) = tail ∧
      F.R (reg 1) = (processed ++ payloadWord (SparseRoleCircuit.encode ∘ word)).reverse ∧
      (∀ j, (2 : Fin 5) ≤ j → F.R (reg j) = S.R (reg j)) ∧
      ∀ j, readAt blank (F.L (bank port)) (F.R (bank port)) j = blank := by
  intro bank reg outer bits loaded queue stack width hs ht empty call
  have off (i : Fin T) (j : Fin 5) : bank i ≠ reg j := by
    intro eq
    have h := congrArg Fin.val eq
    change i.val = T + j.val at h
    omega
  have inj : Function.Injective bank := Fin.castAdd_injective ..
  have regs : Function.Injective reg := Fin.natAdd_injective ..
  have load : [reg 2,reg 0,bank port,reg 3,reg 4].Nodup := by
    simp [off,Ne.symm (off port 2),Ne.symm (off port 0),regs.eq_iff]
  have store : [reg 2,bank port,reg 1,reg 4].Nodup := by
    simp [off,Ne.symm (off port 2),regs.eq_iff]
  obtain ⟨y,A,uy,read,frame,payload⟩ := loadPayload_exec outer load _ tail u S queue width empty hs ht
  have project (R : Fin (T+5) → List (Fin (prime+4))) (xs ys : List (Fin (prime+4))) (j : Fin 5) :
      (Function.update (Function.update R (reg j) xs) (bank port) ys) ∘ bank =
        Function.update (R ∘ bank) port ys := by
    funext i
    by_cases h : i = port <;> simp [h,Function.comp_def,inj.eq_iff,Function.update_of_ne,off]
  have same : embStk bank A = loaded := by
    rw [frame]
    unfold loaded embStk
    congr 1
    apply project
  obtain ⟨v,B,n,word,user,time,run,correct,done,next⟩ := call (embDn bank y) uy (by
    rw [← same]
    intro j
    simpa only [embStk,sub_zero,M8.AtomBank.arrTape,List.map_ofFn,Function.comp_def] using (payload j).symm)
  obtain ⟨z,D,placed,_,uz,eq,stay⟩ := exec_emb inj (body' := outer) (fun _ => rfl) run y rfl _ same
  have keep (j : Fin 5) := (stay (reg j) (fun i => off i j)).2
  simp only [frame] at keep
  have keepR (j : Fin 5) : D.R (reg j) = Function.update S.R (reg 0) tail (reg j) := by
    simpa only [Function.update_of_ne (Ne.symm (off port j))] using keep j
  have dp : RecordPayload (bank port) (fun _ => blank) 0 word D := by
    rw [← eq] at done
    exact done
  obtain ⟨v',uv,write,clean⟩ := storeOwnerRecord_exec outer store word z D dp
    (by simpa [keepR,regs.eq_iff,Function.update_of_ne] using width)
    (by simpa [keepR,regs.eq_iff,Function.update_of_ne] using ht) processed
    (by simpa [keepR,regs.eq_iff,Function.update_of_ne] using stack)
  refine ⟨v',_,_,word,uv.trans (uz.trans (user.trans uy)),by omega,Exec.seq (Exec.seq read placed) write,
    correct,?_,?_,by simp,?_,clean⟩
  · rw [← eq] at next
    convert next using 1
    unfold embStk
    congr 1
    funext i
    by_cases h : i = port <;> simp [h,Function.comp_def,inj.eq_iff,off,Function.update_of_ne]
  · simp [keepR,Function.update_of_ne,regs.eq_iff,Ne.symm (off port 0)]
  · intro j hj
    have h0 : j ≠ 0 := by omega
    have h1 : j ≠ 1 := by omega
    simp [keepR,Function.update_of_ne,regs.eq_iff,h0,h1,Ne.symm (off port j)]

/-- Restore all processed payloads in directory order ahead of the owner suffix. -/
theorem restoreOwnerRecords_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    {src owner : Fin T} (apart : src ≠ owner) (u : HS T Q prime U) (S : Stacks T prime)
    (processed : List (Fin (prime+4))) (stack : S.R src = processed.reverse) :
    ∃ z, z.user = u.user ∧ Exec body (Host.moveR src owner id) (mk u S) (2*processed.length+2)
      (mk z {S with R := Function.update (Function.update S.R src []) owner (processed ++ S.R owner)}) := by
  simpa [Host.movedR,stack] using Host.moveR_exec body src owner apart id u S

/-- Traverse distinct owner records with a fixed machine program. The invariant
tracks the remaining directory and the symbols produced so far, in forward order.
Each iteration peeks at the owner again after the record program returns. -/
theorem ownerDirectory_exec {ι P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (owner : Fin T) (record : Pr P T Q prime U) (cost : ι → ℕ)
    (effect : ι → List (Fin (prime+4)) → Prop)
    (ready : List ι → List (Fin (prime+4)) → Stacks T prime → Prop)
    (queued : ∀ rs acc S, ready rs acc S → (S.R owner).head?.isSome = rs.head?.isSome)
    (step : ∀ r rs acc (u : HS T Q prime U) S, ready (r::rs) acc S →
      ∃ z F n bits, z.user = u.user ∧ n ≤ cost r ∧ Exec body record (mk u S) n (mk z F) ∧
        effect r bits ∧ ready rs (acc ++ bits) F)
    (rs : List ι) (acc : List (Fin (prime+4))) (u : HS T Q prime U) (S : Stacks T prime)
    (initial : ready rs acc S) :
    let inspect : Pr P T Q prime U := .act (peekR owner)
    ∃ z F n rows, z.user = u.user ∧ n ≤ (rs.map cost).sum + 2*rs.length + 2 ∧
      Exec body (.seq inspect (.loop (·.flag) (.seq record inspect))) (mk u S) n (mk z F) ∧
      List.Forall₂ effect rs rows ∧ ready [] (acc ++ rows.flatten) F := by
  intro inspect
  have loop (xs : List ι) (processed : List (Fin (prime+4))) (v : HS T Q prime U) (A : Stacks T prime)
      (h : ready xs processed A) (flag : v.flag = xs.head?.isSome) :
      ∃ z F n rows, z.user = v.user ∧ n ≤ (xs.map cost).sum + 2*xs.length + 1 ∧
        Exec body (.loop (·.flag) (.seq record inspect)) (mk v A) n (mk z F) ∧
        List.Forall₂ effect xs rows ∧ ready [] (processed ++ rows.flatten) F := by
    induction xs generalizing processed v A with
    | nil => exact ⟨v,A,1,[],rfl,by simp,.loop_false flag,.nil,by simpa using h⟩
    | cons r xs ih =>
      obtain ⟨y,B,m,bits,user,bound,run,out,next⟩ := step r xs processed v A h
      obtain ⟨z,F,n,rows,uz,time,rest,correct,done⟩ := ih _ {y with flag := (B.R owner).head?.isSome}
        B next (queued _ _ _ next)
      have peek := peekR_run owner y B ▸ Exec.act (body := body) (peekR owner) (mk y B)
      exact ⟨z,F,m+1+n+1,bits::rows,uz.trans user,by simp; omega,
        Exec.loop_true (f := (·.flag)) flag (Exec.seq run peek) rest,.cons out correct,
        by simpa [List.append_assoc] using done⟩
  obtain ⟨z,F,n,rows,user,time,run,correct,done⟩ := loop rs acc {u with flag := (S.R owner).head?.isSome}
    S initial (queued _ _ _ initial)
  exact ⟨z,F,1+n,rows,user,by omega,Exec.seq (peekR_run owner u S ▸
    Exec.act (body := body) (peekR owner) (mk u S)) run,correct,done⟩

/-- Charge loading and storing every record to its payload volume while
retaining the scan's inverse-prime discount on exceptional work. -/
theorem remainderRecord_charge (v : Descriptor) (w rows : ℕ) (e : ℕ × ℕ)
    (he : e ∈ BitHosting.remainderIntervals) (width : v.width = 64*(w+1))
    (split : v.rows = 142080*rows) (elapsed overhead : ℕ) (baseline rate ordinary : ℝ) :
    let records := LabelMask.records (role v 142080)
    let N := volume prime (phaseIntervalChild e.1 e.2 (w+1) (v.between*v.afterD) 64)
    let degree := ∑ k ∈ Finset.range (e.2-e.1), (k+1)*65
    0 < N → baseline+6 ≤ ordinary*N →
    (elapsed : ℝ) ≤ overhead + records*(baseline+6) + 2 + ((degree : ℝ)/prime)*rate*(records*N) →
    (elapsed : ℝ) + records*((6*(N : ℝ)+6)+(4*N+4)) + (2*records+2) + (2*(records*N)+2) ≤ overhead + 6 +
      (ordinary+24+((degree : ℝ)/prime)*rate)*volume prime v/142080 := by
  intro records N degree positive base scan
  have size : ((records : ℝ)*N)*142080 = volume prime v := by
    exact_mod_cast remainderRecord_volume v w rows e he width split
  have one : (1 : ℝ) ≤ N := by exact_mod_cast positive
  have io : (6*(N : ℝ)+6)+(4*N+4)+2+2*N ≤ 24*N := by linarith
  calc
    _ ≤ overhead + records*(ordinary*N) + 2 + ((degree : ℝ)/prime)*rate*(records*N) + records*(24*N) + 4 := by
      grw [scan,base]
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) records) (sub_nonneg.mpr io)]
    _ = _ := by rw [← size]; ring

/-- The idle descriptor has the width, volume, and rational pivot certificate
required by the generated record program, with the actual binary header sizes. -/
theorem remainderRecord_scan [M8.Machine.Net] {T work Q : ℕ} {F U : Type}
    (e : ℕ × ℕ) (he : e ∈ BitHosting.remainderIntervals) (w W : ℕ) (hW : 0 < W)
    (parent parentInv : Fin 64 → ZMod (prime^(w+1))) (inv : ∀ i, parent i * parentInv i = 1)
    (io : Fin T) (arity : ℕ) (source : ℤ → Fin 4) (head : ℤ)
    (capacity : 217 ≤ Q) (fits : LeafCore.small ≤ work) (cap : (LeafCore.core io).states ≤ Q) (single : Bool := false) :
    let M := prime^(w+1)
    let child := phaseIntervalChild e.1 e.2 (w+1) W 64
    let D : Matrix (Fin 64) (Fin 64) ℚ := Matrix.diagonal fun i =>
      if e.1 ≤ i.val ∧ i.val < e.2 then 1 else 0
    ∃ (positive : child.Positive) (width : child.width = D.rank*(w+1))
      (rankFits : D.rank ≤ 64) (length : volume prime child = M^64*(M^64*W)),
      GeneratedRecordSpec (F := F) (U := U) child positive w D width (intervalDiagonal_idem 64 e.1 e.2)
        (intervalFactor 64 e.1 e.2) (intervalFactor_denominators 64 e.1 e.2) rankFits parent parentInv inv
        io arity (Nat.size_le.mp (le_refl M.size)) (Nat.size_le.mp (le_refl W.size)) hW length capacity
        source head fits cap single := by
  intro M child D
  obtain ⟨ordered,upper,_⟩ := BitHosting.remainder_counts e he
  have bounded : e.2 ≤ 64 := by omega
  have rank : D.rank = e.2-e.1 := intervalDiagonal_rank bounded
  have rankFits : D.rank ≤ 64 := by omega
  have width : child.width = D.rank*(w+1) := by rw [rank]; rfl
  have pos : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
  have positive : child.Positive :=
    ⟨Nat.zero_lt_one,Nat.zero_lt_one,pow_pos pos _,pow_pos pos _,Nat.mul_pos (pow_pos pos _) hW⟩
  have length : volume prime child = M^64*(M^64*W) := by
    rw [intervalChild_volume ordered bounded, pow_add, Nat.mul_assoc]
  refine ⟨positive,width,rankFits,length,?_⟩
  cases single with
  | false =>
    exact generatedRecordScan_exec child positive w D width
      (intervalDiagonal_idem 64 e.1 e.2) (intervalFactor 64 e.1 e.2)
      (intervalFactor_denominators 64 e.1 e.2) rankFits parent parentInv inv io arity _ _ hW
      length capacity source head fits cap
  | true =>
    exact generatedOrdinaryRecord_exec child positive w D width
      (intervalDiagonal_idem 64 e.1 e.2) (intervalFactor 64 e.1 e.2)
      (intervalFactor_denominators 64 e.1 e.2) rankFits parent parentInv inv io arity _ _ hW
      length capacity source head fits cap

end IntegerMultBounds.MathlibTM2.M6.BitNode
