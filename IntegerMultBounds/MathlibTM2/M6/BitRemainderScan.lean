module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderRecordLayout
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderDirectory
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderRun
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodChildPrepare
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGeneratedGoodRecord
import IntegerMultBounds.Machine.RowPaddingConstructedAlphabet
import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Instantiate the generated cover scan with the physical PR589 idle child. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume role)
open IntegerMultBounds.MathlibTM2.Cover
open IntegerMultBounds.MathlibTM2.Cover.Fallback M8.RevMachine

private theorem encodedOwnerCell {N : ℕ} (word : Fin N → ZMod 2) (j : ℤ) :
    (RadixToBinary.binaryEncoding (q := prime)).encode
      (putWord (fun _ => blank) 0 ((List.ofFn word).map SparseRoleCircuit.encode) j) =
    putWord (fun _ => blank) 0 (List.ofFn fun i => SparseRoleCircuit.encode (a := prime) (word i)) j := by
  rw [List.map_ofFn]
  have mapped := congrFun (RowPaddingConstructedAlphabet.map_array_word (a := prime)
    (fun _ => blank) 0 (SparseRoleCircuit.encode ∘ word)) j
  have bits : RowPaddingConstructedAlphabet.mapArray (a := prime) (SparseRoleCircuit.encode ∘ word) =
      fun i => SparseRoleCircuit.encode (a := prime) (word i) := by
    funext i
    by_cases h : word i = 1 <;> simp [RowPaddingConstructedAlphabet.mapArray,RowPaddingConstructedAlphabet.encoding,
      CountedLoopReuseAlphabet.encoding,SparseRoleCircuit.encode,bitSymbol,h]
  rw [bits] at mapped
  exact mapped

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
    let child := remainderRecordChild e.1 e.2 (w+1) (v.between*v.afterD)
    LabelMask.records directory * volume prime child * 142080 = volume prime v := by
  intro directory child
  obtain ⟨ordered,upper,_⟩ := BitHosting.remainder_counts e he
  rw [remainderRecordChild_volume _ _ _ _ (by omega)]
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

open IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.Swap.Modular Matrix in
/-- Dispatch a directory row at its classified price. Exceptional rows run the physical
projector. Ordinary rows use the generated good or padding executor. -/
theorem ownerClassified_exec [M8.Machine.Net] {m d K w W J N : ℕ} {P U : Type}
    (dimension : m+m = d+1) (v : Descriptor) (proj : Matrix (Fin m) (Fin m) ℚ)
    (idem : proj*proj = proj) (adm : Admissible prime proj)
    (parent inv : Fin m → ZMod (prime^(w+1))) (reciprocal : ∀ i, parent i * inv i = 1)
    (data : ScanData m d w W) (hm : prime^(w+1) < 2^data.H) (hw : W < 2^J) (positive : 0 < W)
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K+1)
    (capacity : (anchorProgram d true).1+(anchorProgram d false).1+1 ≤ columnCapacity)
    (body : P → Pr P (66+(K+1)) columnCapacity prime U) (c : ℕ) (bodyBound : ∀ f, mnProgPush (body f) ≤ c)
    (prefixes : ℕ → List (Fin (prime+4))) (archiveTail : List (Fin (prime+4)))
    (bad : ℕ → Bool) (j : ℕ) (inside : j < data.records)
    (budget : ℕ) (ordinaryEffect : (Fin N → ZMod 2) → Prop)
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
    let live := LabelStock.live m (w+1) 1 j
    let labels := (List.range data.records).drop (j+1)
    ready (embStk placement S) ((List.range data.records).drop j) → S.R (directoryMatrixTape room) = physical.matrices j →
    (good padding : Pr P (66+(K+1)) columnCapacity prime U) →
    (ls bs : List (Fin (prime+4))) →
    S.R (caller 57) = bitSymbol live :: ls → S.R (caller 56) = bitSymbol (bad j) :: bs →
    let port := caller 24
    let loaded := {S with R := Function.update S.R port (payloadWord (SparseRoleCircuit.encode ∘ original) ++ S.R port)}
    RecordPayload port (fun _ => blank) 0 original loaded →
    (¬ (live = true ∧ bad j = true) → ∀ y A, ready (embStk placement A) (j::labels) → payload original A → A.R (directoryMatrixTape room) = physical.matrices j →
      ∃ z D n next, z.user = y.user ∧ n ≤ budget ∧ Exec body (if live then good else padding) (mk y A) n (mk z D) ∧
        ready (embStk placement D) labels ∧ ordinaryEffect next ∧ payload next D ∧ D.R (directoryMatrixTape room) = physical.matrices (j+1) ∧
        D.R (caller 57) = A.R (caller 57) ∧ D.R (caller 56) = A.R (caller 56)) →
    let C := physical.table (LabelStock.residue m (w+1) 1 j)
    let rows := classPivots C
    let privateTapes := (List.finRange (66+(K+1))).filter fun i => decide (58 ≤ i.val ∧ i ≠ directoryMatrixTape room)
    ∃ z D n next, z.user = u.user ∧ n ≤ (if live && bad j then exceptionalRecordTime U rows (negativeAnchor rows C) m w W data.H J
      privateTapes.length (max (mnProgPush (directoryExceptionalCore (P := P) (U := U) d room capacity)) c) (prefixes j).length else budget) + (if live then 4 else 3) ∧
      Exec body (ownerDispatch (caller 57) (caller 56) good (directoryExceptionalProgram m d room capacity) padding) (mk u loaded) n (mk z D) ∧
      (if live && bad j then (∀ x k, next ((FlatCoordinateLayout.index ((projectorResidual e (reduce (prime^(w+1)) proj) parent inv
        (physicalLabel m (w+1) j)).mulVec x) k).cast (directoryPayloadLength e length)) = original ((FlatCoordinateLayout.index x k).cast (directoryPayloadLength e length))) else ordinaryEffect next) ∧
      payload next D ∧
      let drained := {D with R := Function.update D.R (caller 24) ((D.R (caller 24)).drop N)}
      ready (embStk placement drained) labels ∧ drained.R (directoryMatrixTape room) = physical.matrices (j+1) ∧
      drained.R (caller 57) = ls ∧ drained.R (caller 56) = bs := by
  intro e physical φ code schedule ready placement caller payload live labels start matrix good padding ls bs liveBits badBits port loaded input ordinary C rows privateTapes
  obtain ⟨loadedReady,archiveLoad,liveLoad,badLoad⟩ := archiveReady_updatePayload room
    (payloadWord (SparseRoleCircuit.encode ∘ original) ++ S.R port) start
  have loadedPayload : payload original loaded := by
    simpa only [payload,RecordPayload,embStk,Function.comp_apply,placement,directoryOrdinaryBank_caller,port,caller,Fin.castAddEmb_apply] using input
  by_cases both : live = true ∧ bad j = true
  · obtain ⟨liveJ,badJ⟩ := both
    let B := {loaded with R := Function.update loaded.R (caller 57) ls}
    let E := {B with R := Function.update B.R (caller 56) bs}
    obtain ⟨readyE,inputE,archiveE⟩ := ownerSelectors_frame room loaded ls bs original loadedReady loadedPayload
    obtain ⟨z,D,n,next,user,time,run,done,tail,action,out,mask,mode⟩ :=
      DirectoryReady.runExceptional dimension v proj idem adm parent inv reciprocal data hm hw positive room capacity
        body c bodyBound prefixes archiveTail bad j inside liveJ badJ (fun _ => blank) 0 length original
        {u with flag := true} E readyE (archiveE.trans (archiveLoad.trans matrix)) inputE
    have dispatch := ownerDispatch_exec body (caller 57) (caller 56) (caller.injective.ne (by decide : (57 : Fin 66) ≠ 56))
      good (directoryExceptionalProgram m d room capacity) padding true true u loaded ls bs (liveJ ▸ (liveLoad.trans liveBits)) (badJ ▸ (badLoad.trans badBits)) run
    obtain ⟨restored,archive,keepLive,keepBad⟩ := archiveReady_updatePayload room ((D.R (caller 24)).drop N) done
    simp only [liveJ,badJ,Bool.and_self,ite_true]
    refine ⟨z,D,_,next,user,Nat.add_le_add_right time 4,dispatch,action,out,restored,archive.trans tail,?_,?_⟩
    · exact keepLive.trans (mask.trans (by simp [E,B,caller,Function.update_of_ne]))
    · exact keepBad.trans (mode.trans (Function.update_self (caller 56) bs B.R))

  · have suffix : (List.range data.records).drop j = j :: labels := by
      have h : j < (List.range data.records).length := by simpa using inside
      simpa [labels] using (List.getElem_cons_drop h).symm
    have run := ownerOrdinary_exec v proj parent prefixes archiveTail schedule room body good
      (directoryExceptionalProgram m d room capacity) padding live (bad j) both budget j labels
      physical.matrices original ordinaryEffect u loaded ls bs (suffix ▸ loadedReady) (archiveLoad.trans matrix) (liveLoad.trans liveBits) (badLoad.trans badBits) loadedPayload (ordinary both)
    simpa only [Bool.and_eq_true,both,ite_false] using run

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

/-- The row at a directory index reads its contiguous slice of the role tape. -/
def ownerRow {R N V : ℕ} (size : R*N = V) (word : Fin V → ZMod 2) (j : ℕ) (i : Fin N) : ZMod 2 :=
  if h : j < R then word ((finProdFinEquiv (⟨j,h⟩,i)).cast size) else 0

/-- Read a live output of the packed owner scanner at the incoming
port projector's address, including the two inherited weight vectors. -/
theorem ownerRow_projected {R N V w W : ℕ} (size : R*N = V)
    (length : (prime^(w+1))^128*W = N) (input output : Fin V → ZMod 2)
    (c : IntegerMultBounds.Networks.Certificates.PR589.Nine.PortCertificate) (checked : c.Checked)
    (lo hi : ℕ) (fits : hi ≤ 63) (block : ℕ) (g : LabelPadding.Label 64 (w+1)) (live : IsUnit g)
    (α α' : Fin 64 → ZMod (prime^(w+1))) :
    let M := prime^(w+1)
    let H := IntegerMultBounds.Swap.Modular.reduce M (c.fullChart.submatrix stageAxis.symm remainderAxis)
    let P := IntegerMultBounds.Swap.Modular.reduce M ((c.span lo hi).submatrix stageAxis.symm stageAxis.symm)
    let D : Matrix (Fin 64) (Fin 64) ℚ := Matrix.diagonal fun i => if lo ≤ i.val ∧ i.val < hi then 1 else 0
    let j := block*M^(64*64)+(LabelAddress.address (g*H)).val
    (if LabelStock.live 64 (w+1) 1 j then
      ∀ x k, ownerRow size output j ((FlatCoordinateLayout.index ((projectorResidual finSumFinEquiv
        (IntegerMultBounds.Swap.Modular.reduce M D) α α' (physicalLabel 64 (w+1) j)).mulVec x) k).cast length) =
        ownerRow size input j ((FlatCoordinateLayout.index x k).cast length)
      else ownerRow size input j = ownerRow size output j) →
    ∀ x k, ownerRow size output j ((FlatCoordinateLayout.index ((projectorResidual finSumFinEquiv P α α' g).mulVec x) k).cast length) =
      ownerRow size input j ((FlatCoordinateLayout.index x k).cast length) := by
  intro M H P D j effect
  obtain ⟨bit,archive⟩ := remainderArchive_at c checked lo hi (w+1) (by omega) fits block g live α α'
  change LabelStock.live 64 (w+1) 1 j = true at bit
  change projectorResidual finSumFinEquiv (IntegerMultBounds.Swap.Modular.reduce M D) α α'
    (physicalLabel 64 (w+1) j) = projectorResidual finSumFinEquiv P α α' g at archive
  simpa only [bit,ite_true,archive] using effect

theorem ownerRow_queue {R N V : ℕ} (size : R*N = V) (word : Fin V → ZMod 2) :
    payloadWord (SparseRoleCircuit.encode ∘ word) =
      (List.range R).flatMap (fun j => payloadWord (SparseRoleCircuit.encode ∘ ownerRow size word j)) := by
  subst V
  rw [ownerPayload_records (R := R) (N := N), ← List.map_coe_finRange_eq_range,List.flatMap_map]
  simp [ownerRow,Function.comp_def]

theorem ownerRows_pack {R N V : ℕ} (size : R*N = V)
    {action : ℕ → (Fin N → ZMod 2) → Prop} {rows : List (List (Fin (prime+4)))}
    (correct : List.Forall₂ (fun j out => ∃ word, action j word ∧
      out = payloadWord (SparseRoleCircuit.encode ∘ word)) (List.range R) rows) :
    ∃ output : Fin V → ZMod 2, (∀ j : Fin R, action j (ownerRow size output j)) ∧
      rows.flatten = payloadWord (SparseRoleCircuit.encode ∘ output) := by
  classical
  subst V
  have len : R = rows.length := by simpa using correct.length_eq
  have row (j : Fin R) := correct.get (i := j.val) (by simp) (len ▸ j.isLt)
  simp only [List.get_eq_getElem,List.getElem_range] at row
  choose values effect encoded using row
  let output := fun k : Fin (R*N) => values (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  have atRow (j : Fin R) (i : Fin N) : output (finProdFinEquiv (j,i)) = values j i := by
    simp only [output,Equiv.symm_apply_apply]
  refine ⟨output,fun j => ?_,?_⟩
  · have read : ownerRow (R := R) (N := N) rfl output j = values j := by
      funext i
      rw [ownerRow,dite_eq_left j.isLt]
      exact atRow j i
    exact read ▸ effect j
  · have repr : rows = List.ofFn (fun j : Fin R => payloadWord (SparseRoleCircuit.encode ∘ values j)) := by
      apply List.ext_getElem
      · simpa using len.symm
      · intro i hi hj
        simpa using encoded ⟨i,len.symm ▸ hi⟩
    rw [repr,ownerPayload_records (R := R) (N := N),List.ofFn_eq_map]
    simp [List.flatMap_def,atRow,Function.comp_def]

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
      effect word ∧ ready (embStk bank F) ∧ F.L (reg 0) = S.L (reg 0) ∧ F.R (reg 0) = tail ∧
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
    correct,?_,?_,?_,by simp,?_,clean⟩
  · rw [← eq] at next
    convert next using 1
    unfold embStk
    congr 1
    funext i
    by_cases h : i = port <;> simp [h,Function.comp_def,inj.eq_iff,off,Function.update_of_ne]
  · have left := (stay (reg 0) (fun i => off i 0)).1
    simpa only [frame] using left
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

/-- Fixed program for an owner directory with five external registers. -/
noncomputable def packedOwner {T Q : ℕ} {P U : Type} (port selector : Fin T) (record : Pr P T Q prime U) :
    Pr P (T+5) Q prime U :=
  let reg := fun j : Fin 5 => Fin.natAdd T j
  let bank := fun i : Fin T => i.castAdd 5
  let row := (((movePrefix (reg 2) (reg 0) (bank port) (reg 3) (reg 4)).seq (embProg bank id record)).seq
    (Mult.ShortConv.transfer (reg 2) (bank port) (reg 1) (reg 4)))
  let inspect : Pr P (T+5) Q prime U := .act (peekR (bank selector))
  (inspect.seq (.loop (·.flag) (row.seq inspect))).seq (Host.moveR (reg 1) (reg 0) id)

/-- Process a packed queue of distinct rows, and put their checked results back
on the owner tape. Only the inner call has to know the directory format. -/
theorem packedOwner_exec {ι P U : Type} {N T Q : ℕ} (tail : List (Fin (prime+4)))
    (body : P → Pr P T Q prime U) (port selector : Fin T) (record : Pr P T Q prime U)
    (input : ι → Fin N → ZMod 2) (effect : ι → (Fin N → ZMod 2) → Prop)
    (cost : ι → ℕ) (ready : List ι → Stacks T prime → Prop)
    (rs : List ι) (u : HS (T+5) Q prime U) (S : Stacks (T+5) prime) :
    let bits := fun word : Fin N → ZMod 2 => payloadWord (SparseRoleCircuit.encode ∘ word)
    let bank := fun i : Fin T => i.castAdd 5
    let reg := fun j : Fin 5 => Fin.natAdd T j
    let outer := fun f => embProg bank id (body f)
    let inv := fun (xs : List ι) (acc : List (Fin (prime+4))) (D : Stacks (T+5) prime) =>
      ready xs (embStk bank D) ∧ D.L (reg 0) = S.L (reg 0) ∧ D.R (reg 0) = xs.flatMap (bits ∘ input) ++ tail ∧ D.R (reg 1) = acc.reverse ∧
      (D.R (reg 2)).length = N ∧ D.R (reg 3) = [] ∧ D.R (reg 4) = [] ∧
      ∀ j, readAt blank (D.L (bank port)) (D.R (bank port)) j = blank
    (∀ xs A, ready xs A → (A.R selector).head?.isSome = xs.head?.isSome) →
    inv rs [] S →
    (∀ r xs (A : Stacks T prime) (y : HS T Q prime U), ready (r::xs) A →
      let loaded := {A with R := Function.update A.R port (bits (input r) ++ A.R port)}
      RecordPayload port (fun _ => blank) 0 (input r) loaded →
      ∃ z B n word, z.user = y.user ∧ n ≤ cost r ∧ Exec body record (mk y loaded) n (mk z B) ∧
        effect r word ∧ RecordPayload port (fun _ => blank) 0 word B ∧
        ready xs {B with R := Function.update B.R port ((B.R port).drop N)}) →
    ∃ z F n rows, z.user = u.user ∧
      n ≤ (rs.map (fun r => 6*N+6+cost r+(4*N+4))).sum + 2*rs.length+2 + (2*(rs.length*N)+2) ∧
      Exec outer (packedOwner port selector record) (mk u S) n (mk z F) ∧
      List.Forall₂ (fun r out => ∃ word, effect r word ∧ out = bits word) rs rows ∧
      F.L (reg 0) = S.L (reg 0) ∧ F.R (reg 0) = rows.flatten ++ tail ∧ F.R (reg 1) = [] ∧ ready [] (embStk bank F) := by
  intro bits bank reg outer inv flags start call
  let row := (((movePrefix (reg 2) (reg 0) (bank port) (reg 3) (reg 4)).seq (embProg bank id record)).seq
    (Mult.ShortConv.transfer (reg 2) (bank port) (reg 1) (reg 4)))
  have queued xs acc D (h : inv xs acc D) : (D.R (bank selector)).head?.isSome = xs.head?.isSome :=
    flags _ _ h.1
  obtain ⟨z,D,n,rows,user,time,run,correct,done⟩ := ownerDirectory_exec outer (bank selector) row
    (fun r => 6*N+6+cost r+(4*N+4)) (fun r out => ∃ word, effect r word ∧ out = bits word) inv queued (by
      intro r xs acc v A h
      obtain ⟨state,ownerLeft,queue,stack,width,saved,tmp,empty⟩ := h
      obtain ⟨y,B,t,word,uy,bound,exec,act,next,left,tail,accum,keep,clear⟩ :=
        ownerRecord_exec body port record (input r) (effect r) (ready xs) _ acc (cost r) v A
          (by simpa only [List.flatMap_cons,List.append_assoc,Function.comp_apply] using queue) stack width saved tmp empty (fun y _ p => call r xs _ y state p)
      exact ⟨y,B,t,bits word,uy,bound,exec,⟨word,act,rfl⟩,next,left.trans ownerLeft,tail,accum,
        (congrArg List.length (keep 2 (by decide))).trans width,(keep 3 (by decide)).trans saved,
        (keep 4 (by decide)).trans tmp,clear⟩) rs [] u S start
  obtain ⟨state,left,tail,stack,_⟩ := done
  have apart : reg 1 ≠ reg 0 := (Fin.natAdd_injective ..).ne (by decide : (1 : Fin 5) ≠ 0)
  obtain ⟨v,uv,restore⟩ := restoreOwnerRecords_exec outer apart z D rows.flatten (by simpa using stack)
  have extent {xs : List ι} {ys} (h : List.Forall₂ (fun r out => ∃ word, effect r word ∧ out = bits word) xs ys) :
      ys.flatten.length = xs.length*N := by
    induction h with
    | nil => simp
    | cons out _ ih =>
      obtain ⟨word,_,rfl⟩ := out
      simp [bits,payloadWord,ih,Nat.succ_mul,Nat.add_comm]
  refine ⟨v,_,_,rows,uv.trans user,by rw [← extent correct]; exact Nat.add_le_add_right time _,Exec.seq run restore,correct,left,
    by simp [tail,Function.update_self],by simp [Function.update_of_ne apart],?_⟩
  convert state using 1
  unfold embStk
  congr 1
  funext k
  have off (j : Fin 5) : bank k ≠ reg j := by
    intro eq
    have h := congrArg Fin.val eq
    change k.val = T+j.val at h
    omega
  simp [Function.update_of_ne,off]

/-- Run the generated selectors before the matrix writer, preserving the empty
archive and all five external owner registers. -/
theorem ownerSelectorSetup_exec [M8.Machine.Net] {K d Q : ℕ} {P U : Type}
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K+1)
    (localBody : P → Pr P (66+K) Q prime U) (body : P → Pr P (66+(K+1)) Q prime U)
    (calls : ∀ f, body f = embProg (directoryOrdinaryBank room) id (localBody f))
    (prepare : Pr P (66+K) Q prime U)
    (u : HS ((66+(K+1))+5) Q prime U) (S : Stacks ((66+(K+1))+5) prime) :
    let placement := directoryOrdinaryBank room
    let bank := fun i : Fin (66+(K+1)) => i.castAdd 5
    ∀ y D t, Exec localBody prepare (mk (embDn placement (embDn bank u)) (embStk placement (embStk bank S))) t (mk y D) →
      ∃ z F, z.user = y.user ∧ embStk placement (embStk bank F) = D ∧
        (embStk bank F).R (directoryMatrixTape room) = (embStk bank S).R (directoryMatrixTape room) ∧
        (∀ j : Fin 5, F.L (Fin.natAdd (66+(K+1)) j) = S.L (Fin.natAdd (66+(K+1)) j) ∧ F.R (Fin.natAdd (66+(K+1)) j) = S.R (Fin.natAdd (66+(K+1)) j)) ∧
        Exec (fun f => embProg bank id (body f)) (embProg bank id (embProg placement id prepare)) (mk u S) t (mk z F) := by
  intro placement bank y D t run
  obtain ⟨v,A,placed,_,uv,localEq,frame⟩ := exec_emb placement.injective calls run (embDn bank u) rfl (embStk bank S) rfl
  obtain ⟨z,F,exec,_,uz,archiveEq,keep⟩ := exec_emb (ι := id) (body' := fun f => embProg bank id (body f))
    (Fin.castAdd_injective ..) (fun _ => rfl) placed u rfl S rfl
  refine ⟨z,F,uz.trans uv,by rw [archiveEq,localEq],?_,?_,exec⟩
  · rw [archiveEq]
    exact (frame _ (Fin.succAbove_ne _)).2
  · intro j
    apply keep
    intro i eq
    have h := congrArg Fin.val eq
    change i.val = (66+(K+1))+j.val at h
    omega

open RingFormula IntegerMultBounds.MathlibTM2.Fast.Main in
/-- Build the matrix archive from the directory headers while the owner
registers are outside the writer's tape bank. -/
theorem ownerArchiveSetup_exec [M8.Machine.Net] {m K d w W J Q : ℕ} {P U : Type}
    (v : Descriptor) (proj : Matrix (Fin m) (Fin m) ℚ) (parent inv : Fin m → ZMod (prime^(w+1)))
    (reciprocal : ∀ i, parent i * inv i = 1) (e : (Fin m ⊕ Fin m) ≃ Fin (d+1))
    (data : ScanData m d w W) (hm : prime^(w+1) < 2^data.H)
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K+1)
    (fits : (36+2*m+1+(conjugationDepth m+1)*13)+3 ≤ K+1)
    (body : P → Pr P (66+(K+1)) Q prime U) (prefixes : ℕ → List (Fin (prime+4)))
    (archiveTail : List (Fin (prime+4))) (schedule : List ℕ → List (Fin (prime+4)))
    (u : HS ((66+(K+1))+5) Q prime U) (S : Stacks ((66+(K+1))+5) prime) :
    let placement := directoryOrdinaryBank room
    let bank := fun i : Fin (66+(K+1)) => i.castAdd 5
    let start := embStk bank S
    let caller := Fin.castAddEmb (n := 66) (K+1)
    let rs := List.range data.records
    let ready := DirectoryReady v proj w W data.H J parent prefixes archiveTail schedule
    let work := (List.finRange (66+(K+1))).filter fun i => decide (58 ≤ i.val ∧ i ≠ directoryMatrixTape room)
    let initTime := directoryQueueInitTime m d w data.H data.records start
    let queueTime := directoryMatrixQueueTime m d w data.H data.records (start.R (caller 47)).length
    ready (embStk placement start) rs → start.R (directoryMatrixTape room) = [] →
    start.R (caller 57) = rs.map (fun j => bitSymbol (LabelStock.live m (w+1) 1 j)) →
    ∃ prepare z F t, z.user = u.user ∧
      Exec (fun f => embProg bank id (body f)) (embProg bank id prepare) (mk u S) t (mk z F) ∧
      ready (embStk placement (embStk bank F)) rs ∧
      (embStk bank F).R (directoryMatrixTape room) = (data.physical e proj parent inv).matrices 0 ∧
      (∀ j : Fin 66, j.val < 58 → (embStk bank F).L (caller j) = start.L (caller j) ∧
        (embStk bank F).R (caller j) = start.R (caller j)) ∧
      (∀ j : Fin 5, F.L (Fin.natAdd (66+(K+1)) j) = S.L (Fin.natAdd (66+(K+1)) j) ∧ F.R (Fin.natAdd (66+(K+1)) j) = S.R (Fin.natAdd (66+(K+1)) j)) ∧
      ∀ p, mnProgPush (directoryQueueInitProgram (P := P) (U := U) (Q := Q) room fits) ≤ p → (∀ f, mnProgPush (body f) ≤ p) →
        t ≤ initTime + queueTime + (4*work.length+1+work.length*(6*(p*initTime))) := by
  intro placement bank start caller rs ready work initTime queueTime initial empty liveBits
  have input := initial
  obtain ⟨directory,widths,privateBlank,_,projector,modulus,_,_,_,unit,clock,weights,_⟩ := input
  have port (j : Fin 66) := directoryOrdinaryBank_caller room j
  simp only [embStk,Function.comp_apply,placement,Fin.castAddEmb_apply,port] at directory widths projector modulus unit clock weights
  have free (i) : start.R (directoryQueueBank room fits i) = [] := by
    by_cases eq : directoryQueueBank room fits i = directoryMatrixTape room
    · rw [eq]; exact empty
    · apply ((directoryOrdinaryBank_clear_iff room start).1 privateBlank _ ?_ eq).2
      by_contra! low
      let j : Fin 66 := ⟨(directoryQueueBank room fits i).val,by omega⟩
      exact directoryQueueBank_caller room fits i j (Fin.ext rfl)
  obtain ⟨_,_,init,_,initBound,_,_,_,_,_,_,_,_,_,_,_,_,_,generate,_⟩ :=
    directoryQueueSetup_exec room fits body parent inv reciprocal hm (embDn bank u) start liveBits free weights modulus unit clock
  obtain ⟨writer,runWriter⟩ := generate e
  obtain ⟨y,t,userY,_,time,write,archive,keep,clear⟩ := runWriter proj prefixes archiveTail projector
    (fun j hj => widths j (List.mem_range.mpr hj)) directory
  obtain ⟨z,F,exec,_,user,projEq,stay⟩ := exec_emb (ι := id) (body' := fun f => embProg bank id (body f)) (Fin.castAdd_injective ..) (fun _ => rfl) write u rfl S rfl
  refine ⟨_,z,F,t,user.trans userY,exec,?_,?_,?_,?_,?_⟩
  · rw [← projEq] at keep clear
    have preserved (i : Fin (66+K)) : (embStk placement (embStk bank F)).R i = (embStk placement start).R i := by
      by_cases hi : 58 ≤ i.val
      · exact (((directoryOrdinaryBank_clear_iff room _).2 clear i hi).2).trans (privateBlank i hi).2.symm
      · let j : Fin 66 := ⟨i.val,by omega⟩
        have eq : i = j.castAdd K := Fin.ext rfl
        rw [eq]
        simp only [embStk,Function.comp_apply,placement,directoryOrdinaryBank_caller]
        exact (keep j (by change i.val < 58; omega)).2
    obtain ⟨a,b,_,c,d,h,f,g,l,vv,k,q,p⟩ := initial
    unfold ready DirectoryReady
    rw [funext preserved]
    exact ⟨a,b,fun i hi => ⟨((directoryOrdinaryBank_clear_iff room _).2 clear i hi).1,(privateBlank i hi).2⟩,c,d,h,f,g,l,vv,k,q,p⟩
  · rw [projEq]; exact archive.trans (data.physical_archive e proj parent inv).symm
  · rw [projEq]; exact keep
  · intro j
    apply stay
    intro i eq
    have h := congrArg Fin.val eq
    change i.val = (66+(K+1))+j.val at h
    omega
  · intro p hp calls
    have raw := time p hp calls
    have each (i) (hi : i ∈ work) : 4*(start.L i).length+2*(start.R i).length+4 = 4 := by
      have mem : 58 ≤ i.val ∧ i ≠ directoryMatrixTape room := by simpa [work] using hi
      obtain ⟨hl,hr⟩ := (directoryOrdinaryBank_clear_iff room start).1 privateBlank i mem.1 mem.2
      simp [hl,hr]
    have base : (work.map fun i => 4*(start.L i).length+2*(start.R i).length+4).sum = 4*work.length := by
      rw [List.map_congr_left each]; simp [Nat.mul_comm]
    change t ≤ init + queueTime + ((work.map fun i => 4*(start.L i).length+2*(start.R i).length+4).sum+1+work.length*(6*(p*init))) at raw
    rw [base] at raw
    exact raw.trans (Nat.add_le_add (Nat.add_le_add_right initBound _) (Nat.add_le_add_left
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left p initBound))) _))

open IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.Swap.Modular Matrix in
/-- Execute the classified archive over the entire packed owner directory. -/
theorem classifiedDirectory_exec [M8.Machine.Net] {m d K w W J N : ℕ} {P U : Type}
    (dimension : m+m = d+1) (v : Descriptor) (proj : Matrix (Fin m) (Fin m) ℚ)
    (idem : proj*proj = proj) (adm : Admissible prime proj)
    (parent inv : Fin m → ZMod (prime^(w+1))) (reciprocal : ∀ i, parent i * inv i = 1)
    (data : ScanData m d w W) (hm : prime^(w+1) < 2^data.H) (hw : W < 2^J) (positive : 0 < W)
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K+1)
    (fits : (36+2*m+1+(RingFormula.conjugationDepth m+1)*13)+3 ≤ K+1)
    (capacity : (anchorProgram d true).1+(anchorProgram d false).1+1 ≤ columnCapacity)
    (body : P → Pr P (66+(K+1)) columnCapacity prime U) (c : ℕ) (bodyBound : ∀ f, mnProgPush (body f) ≤ c)
    (prefixes : ℕ → List (Fin (prime+4))) (archiveTail : List (Fin (prime+4)))
    (bad : ℕ → Bool) (budget : ℕ → ℕ) (ordinaryEffect : ℕ → (Fin N → ZMod 2) → Prop)
    (length : N = (prime^(w+1))^m*((prime^(w+1))^m*W)) (input : ℕ → Fin N → ZMod 2)
    (localBody : P → Pr P (66+K) columnCapacity prime U)
    (calls : ∀ f, body f = embProg (directoryOrdinaryBank room) id (localBody f))
    (selectors goodRow skipRow : Pr P (66+K) columnCapacity prime U) (selectorBudget : ℕ) (ownerTail : List (Fin (prime+4)))
    (u : HS ((66+(K+1))+5) columnCapacity prime U) (S : Stacks ((66+(K+1))+5) prime) :
    let e := finSumFinEquiv.trans (finCongr dimension)
    let physical := data.physical e proj parent inv
    let φ := LabelRing.res prime (w+1) (by omega)
    let code := fun k => residualSchedule (A := prime) (projectorResidual finSumFinEquiv (reduce prime proj)
      (φ ∘ parent) (φ ∘ inv) (LabelStock.residue m (w+1) 1 k))
    let schedule := fun (xs : List ℕ) => xs.flatMap fun k => if bad k then code k else []
    let ready := DirectoryReady v proj w W data.H J parent prefixes archiveTail schedule
    let placement := directoryOrdinaryBank room
    let caller := Fin.castAddEmb (n := 66) (K+1)
    let live := LabelStock.live m (w+1) 1
    let rs := List.range data.records
    let pending := fun j => rs.drop j
    let bits := fun word : Fin N → ZMod 2 => payloadWord (SparseRoleCircuit.encode ∘ word)
    let bank := fun i : Fin (66+(K+1)) => i.castAdd 5
    let reg := fun j : Fin 5 => Fin.natAdd (66+(K+1)) j
    let start := embStk bank S
    let inner := Fin.castAddEmb (n := 66) K
    let advance := dropWords (placement (inner 2)) (directoryMatrixTape room) (placement (inner 59)) ((d+1)*(d+1))
    let good := (embProg placement id goodRow).seq advance
    let padding := (embProg placement id skipRow).seq advance
    let ordinaryTime := fun j => budget j + ((d+1)*(d+1)*(4*data.H+4)+1)
    let cost := fun j =>
      let C := physical.table (LabelStock.residue m (w+1) 1 j)
      let rows := classPivots C
      let scratch := (List.finRange (66+(K+1))).filter fun i => decide (58 ≤ i.val ∧ i ≠ directoryMatrixTape room)
      (if live j && bad j then exceptionalRecordTime U rows (negativeAnchor rows C) m w W data.H J scratch.length
        (max (mnProgPush (directoryExceptionalCore (P := P) (U := U) d room capacity)) c) (prefixes j).length else ordinaryTime j) +
        (if live j then 4 else 3)
    let effect := fun j (next : Fin N → ZMod 2) => if live j && bad j then
      ∀ x k, next ((FlatCoordinateLayout.index ((projectorResidual e (reduce (prime^(w+1)) proj) parent inv
        (physicalLabel m (w+1) j)).mulVec x) k).cast (directoryPayloadLength e length)) =
        input j ((FlatCoordinateLayout.index x k).cast (directoryPayloadLength e length))
      else ordinaryEffect j next
    start.R (directoryMatrixTape room) = [] →
    (∃ y D t, y.user = u.user ∧ t ≤ selectorBudget ∧
      Exec localBody selectors (mk (embDn placement (embDn bank u)) (embStk placement start)) t (mk y D) ∧
      ready D rs ∧ D.L (inner 24) = (embStk placement start).L (inner 24) ∧
      D.R (inner 24) = (embStk placement start).R (inner 24) ∧
      D.R (inner 48) = (embStk placement start).R (inner 48) ∧
      D.R (inner 57) = rs.map (fun j => bitSymbol (live j)) ∧ D.R (inner 56) = rs.map (fun j => bitSymbol (bad j))) →
    S.R (reg 0) = rs.flatMap (bits ∘ input) ++ ownerTail → S.R (reg 1) = [] → (S.R (reg 2)).length = N →
    S.R (reg 3) = [] → S.R (reg 4) = [] → (∀ j, readAt blank (start.L (caller 24)) (start.R (caller 24)) j = blank) →
    (∀ j, j < data.records → ¬ (live j = true ∧ bad j = true) → ∀ y A, ready A (j::pending (j+1)) →
      RecordPayload (inner 24) (fun _ => blank) 0 (input j) A →
      ∃ z D n next, z.user = y.user ∧ n ≤ budget j ∧ Exec localBody (if live j then goodRow else skipRow) (mk y A) n (mk z D) ∧
        ready D (pending (j+1)) ∧ ordinaryEffect j next ∧ RecordPayload (inner 24) (fun _ => blank) 0 next D ∧
        D.R (inner 57) = A.R (inner 57) ∧ D.R (inner 56) = A.R (inner 56)) →
    let program := packedOwner (caller 24) (caller 57) (ownerDispatch (caller 57) (caller 56) good
      (directoryExceptionalProgram m d room capacity) padding)
    let work := (List.finRange (66+(K+1))).filter fun i => decide (58 ≤ i.val ∧ i ≠ directoryMatrixTape room)
    let controls := embProg bank id (embProg placement id selectors)
    ∃ prepare z F t n rows s midUser mid, z.user = u.user ∧ s ≤ selectorBudget ∧
      Exec (fun f => embProg bank id (body f)) controls (mk u S) s (mk midUser mid) ∧
      ready (embStk placement (embStk bank mid)) rs ∧
      (embStk bank mid).R (caller 48) = (embStk placement start).R (inner 48) ∧
      let initTime := directoryQueueInitTime m d w data.H data.records (embStk bank mid)
      let queueTime := directoryMatrixQueueTime m d w data.H data.records ((embStk bank mid).R (caller 47)).length

      (∀ p, mnProgPush (directoryQueueInitProgram (P := P) (U := U) (Q := columnCapacity) room fits) ≤ p → (∀ f, mnProgPush (body f) ≤ p) →
        t ≤ initTime + queueTime + (4*work.length+1+work.length*(6*(p*initTime)))) ∧
      n ≤ (rs.map (fun j => 6*N+6+cost j+(4*N+4))).sum + 2*rs.length+2 + (2*(rs.length*N)+2) ∧
      Exec (fun f => embProg bank id (body f)) (controls.seq ((embProg bank id prepare).seq program)) (mk u S) (s+(t+n)) (mk z F) ∧
      List.Forall₂ (fun j out => ∃ word, effect j word ∧ out = bits word) rs rows ∧
      F.L (reg 0) = S.L (reg 0) ∧ F.R (reg 0) = rows.flatten ++ ownerTail ∧ F.R (reg 1) = [] ∧ ready (embStk placement (embStk bank F)) [] ∧
      (embStk bank F).R (directoryMatrixTape room) = [] ∧
      (embStk bank F).R (caller 57) = [] ∧ (embStk bank F).R (caller 56) = [] := by
  intro e physical φ code schedule ready placement caller live rs pending bits bank reg start inner advance good padding ordinaryTime cost effect
    matrix generated owner accumulator width saved tmp empty ordinary program work controls
  obtain ⟨sy,D,s,su,subtotal,selectorRun,directory,portL,portR,projectorKept,mask,mode⟩ := generated
  obtain ⟨midUser,mid,um,project,archiveKept,extRegs,runControls⟩ :=
    ownerSelectorSetup_exec room localBody body calls selectors u S sy D s selectorRun
  have cellEq (j : Fin 66) : (embStk bank mid).R (caller j) = D.R (inner j) := by
    have h := congrArg (fun A => Stacks.R A (inner j)) project
    simpa only [embStk,Function.comp_apply,placement,inner,caller,Fin.castAddEmb_apply,directoryOrdinaryBank_caller] using h
  have midBlank : ∀ j, readAt blank ((embStk bank mid).L (caller 24)) ((embStk bank mid).R (caller 24)) j = blank := by
    have h := congrArg (fun A => Stacks.L A (inner 24)) project
    simp only [embStk,Function.comp_apply,placement,inner,Fin.castAddEmb_apply,directoryOrdinaryBank_caller] at h portL portR
    rw [cellEq,show (embStk bank mid).L (caller 24) = D.L (inner 24) from h]
    change ∀ j, readAt blank (D.L ((24 : Fin 66).castAdd K)) (D.R ((24 : Fin 66).castAdd K)) j = blank
    rw [portL,portR]
    exact empty
  obtain ⟨prepare,y,B,t,uy,write,prepared,archive,keep,regs,setupTime⟩ := ownerArchiveSetup_exec
    v proj parent inv reciprocal e data hm room fits body prefixes archiveTail schedule midUser mid (by rw [project]; exact directory) (archiveKept.trans matrix) ((cellEq 57).trans mask)
  have cell (j : Fin 66) (hj : j.val < 58) := keep j hj
  let frame := fun (xs : List ℕ) (A : Stacks (66+(K+1)) prime) =>
    ∃ k ≤ data.records, pending k = xs ∧ ready (embStk placement A) xs ∧
      A.R (directoryMatrixTape room) = physical.matrices k ∧
      A.R (caller 57) = xs.map (fun j => bitSymbol (live j)) ∧ A.R (caller 56) = xs.map (fun j => bitSymbol (bad j))
  let dispatch := ownerDispatch (caller 57) (caller 56) good (directoryExceptionalProgram m d room capacity) padding
  obtain ⟨z,F,n,rows,user,time,run,correct,left,output,free,k,hk,remaining,done,archiveEnd,maskEnd,modeEnd⟩ :=
    packedOwner_exec ownerTail body (caller 24) (caller 57) dispatch input effect cost frame rs y B (by
        intro xs A h
        obtain ⟨_,_,_,_,_,mask,_⟩ := h
        rw [mask]
        cases xs <;> rfl)
      ⟨⟨0,Nat.zero_le _,rfl,prepared,archive,((cell 57 (by decide)).2.trans ((cellEq 57).trans mask)),((cell 56 (by decide)).2.trans ((cellEq 56).trans mode))⟩,
        rfl,(regs 0).2.trans ((extRegs 0).2.trans owner),(regs 1).2.trans ((extRegs 1).2.trans accumulator),(congrArg List.length ((regs 2).2.trans (extRegs 2).2)).trans width,
        (regs 3).2.trans ((extRegs 3).2.trans saved),(regs 4).2.trans ((extRegs 4).2.trans tmp),by
          change ∀ j, readAt blank ((embStk bank B).L (caller 24)) ((embStk bank B).R (caller 24)) j = blank
          rw [(cell 24 (by decide)).1,(cell 24 (by decide)).2]; exact midBlank⟩ (by
      intro j xs A y current loaded inputWord
      obtain ⟨k,hk,suffix,dir,archive,ls,bs⟩ := current
      have inside : k < data.records := by
        have h := congrArg List.length suffix
        simp [pending,rs] at h
        omega
      have eq : pending k = k :: pending (k+1) := by
        have h : k < (List.range data.records).length := by simpa using inside
        simpa [pending,rs] using (List.getElem_cons_drop h).symm
      obtain ⟨rfl,rfl⟩ := List.cons.inj (eq.symm.trans suffix)
      obtain ⟨v,B,t,word,uv,bound,exec,action,output,next,tail,maskTail,modeTail⟩ :=
        ownerClassified_exec dimension v proj idem adm parent inv reciprocal data hm hw positive room capacity body c bodyBound
          prefixes archiveTail bad k inside (ordinaryTime k) (ordinaryEffect k) length (input k) y A
          (show ready (embStk placement A) (pending k) by rw [eq]; exact dir) archive good padding _ _ ls bs inputWord (by
            intro no userState archiveState startRow inputRow archiveRow
            obtain ⟨v,D,t,next,userEq,time,run,done,act,out,mask,mode⟩ :=
              ordinary k inside no (embDn placement userState) (embStk placement archiveState) startRow inputRow
            have clock : (D.R (inner 2)).length = physical.H := by
              rw [done.2.2.2.2.2.1,length_binSyms]; rfl
            obtain ⟨z,B,hz,bankEq,tail,_,exec⟩ := physical.advanceEmbeddedRecord_exec k inside placement
              (directoryMatrixTape room) (Fin.succAbove_ne _) (inner 2) (inner 59)
              (inner.injective.ne (by decide : (2 : Fin 66) ≠ 59)) id localBody body calls _ userState archiveState
              v D t run clock (done.2.2.1 _ (by decide : 58 ≤ 59)).2 archiveRow
            have cell (i : Fin 66) : B.R (caller i) = D.R (inner i) := by
              change B.R (i.castAdd (K+1)) = _
              rw [← directoryOrdinaryBank_caller room i]
              exact congrArg (fun A => Stacks.R A (inner i)) bankEq
            refine ⟨z,B,_,next,hz.trans userEq,Nat.add_le_add_right time _,?_,by rw [bankEq]; exact done,act,
              ?_,tail,?_,?_⟩
            · change Exec body (if live k then good else padding) _ _ _
              cases h : live k <;> simpa only [h,Bool.false_eq_true,ite_false,ite_true,good,padding,advance,physical,ScanData.physical] using exec
            · change RecordPayload (inner 24) _ _ next (embStk placement B)
              rw [bankEq]
              exact out
            · simpa [embStk,placement,inner,caller,directoryOrdinaryBank_caller] using (cell 57).trans mask
            · simpa [embStk,placement,inner,caller,directoryOrdinaryBank_caller] using (cell 56).trans mode)
      refine ⟨v,B,t,word,uv,bound,exec,action,?_,k+1,by omega,rfl,next,tail,maskTail,modeTail⟩
      simpa only [RecordPayload,embStk,Function.comp_apply,placement,directoryOrdinaryBank_caller,caller,Fin.castAddEmb_apply] using output)
  have last : k = data.records := by
    have h := congrArg List.length remaining
    simp [pending,rs] at h
    omega
  refine ⟨prepare,z,F,t,n,rows,s,midUser,mid,user.trans (uy.trans (um.trans su)),subtotal,runControls,(by rw [project]; exact directory),(cellEq 48).trans projectorKept,setupTime,time,Exec.seq runControls (Exec.seq write run),correct,left.trans ((regs 0).1.trans (extRegs 0).1),output,free,done,archiveEnd.trans ?_,maskEnd,modeEnd⟩
  simp [last,ScanData.matrices,physical,ScanData.physical,List.drop_of_length_le (List.length_range.le)]

/-- Normalize the complete execution by the payload volume owned by its rows. -/
private theorem packedOwner_charge (elapsed overhead records N baseline degree rate : ℕ)
    (share : ℝ) (size : (records : ℝ)*N = share) (positive : 0 < N)
    (bill : elapsed ≤ overhead + (records*(baseline+12*N+16) + (degree*records/prime)*(rate*N)+4)) :
    (elapsed : ℝ) ≤ overhead + 4 + (((baseline : ℝ)+16)/N + 12 + (degree : ℝ)/prime*rate)*share := by
  have pos : (0 : ℝ) < prime := by exact_mod_cast Shared50ModularControl.prime_prime.pos
  have frequency : ((degree*records/prime : ℕ) : ℝ) ≤ (degree : ℝ)*records/prime := by
    apply (le_div_iff₀ pos).mpr
    exact_mod_cast Nat.div_mul_le_self (degree*records) prime
  have total : (elapsed : ℝ) ≤ overhead + (records*((baseline : ℝ)+12*N+16) +
      ((degree*records/prime : ℕ) : ℝ)*(rate*N)+4) := by exact_mod_cast bill
  calc
    _ ≤ overhead + (records*((baseline : ℝ)+12*N+16) + ((degree : ℝ)*records/prime)*(rate*N)+4) := by
      grw [total,frequency]
    _ = _ := by
      rw [← size]
      have nonzero : (N : ℝ) ≠ 0 := by exact_mod_cast positive.ne'
      field_simp
      ring

open Matrix Finset IntegerMultBounds.Swap.LowerTriangular IntegerMultBounds.Swap.Modular in
/-- Charge the physical transfers and loop tests once per row, and charge the
exceptional surcharge only on the labels counted by the projector witness. -/
theorem packedClassifiedTime_le {m w N B : ℕ} {P : Matrix (Fin m) (Fin m) ℚ}
    (idem : P*P = P) (factor : Factorization univ univ P)
    (small : ∀ k ∈ factorizationDenominators factor, k < prime) (rankFits : P.rank ≤ m)
    (directory : Descriptor) (shape : directory.beforeH = B*prime^(m*((w+1)*m)))
    (usual rare : ℕ → ℕ) (baseline extra : ℕ) :
    let labels := List.range (LabelMask.records directory)
    let live := LabelStock.live m (w+1) 1
    let bad := fun j => fallbackBit rankFits (reduce (prime^(w+1)) P) (physicalLabel m (w+1) j)
    let core := fun j => if live j && bad j then rare j else usual j
    let cost := fun j => core j + (if live j then 4 else 3)
    (∀ j ∈ labels, usual j ≤ baseline) → (∀ j ∈ labels, rare j ≤ baseline+extra) →
    (labels.map (fun j => 6*N+6+cost j+(4*N+4))).sum + 2*labels.length+2 + (2*(labels.length*N)+2) ≤
      labels.length*(baseline+12*N+16) + (((∑ k ∈ range P.rank, (k+1)*(m+1))*labels.length)/prime)*extra+4 := by
  intro labels live bad core cost usualBound rareBound
  obtain ⟨g₀,unit,generic⟩ := LabelProjector.residue_witness (w := w+1) (by omega) P idem factor small rankFits
  have size : LabelMask.records directory = (directory.beforeRows*directory.rows*B)*(prime^(w+1))^(m*m) := by
    rw [LabelMask.records,shape,← pow_mul]; ring
  have bill := classifiedRecordTime_le w P.rank _ rankFits (reduce (prime^(w+1)) P) _ size g₀ unit generic
    core baseline extra
    (fun j hj l b => by change live j = true at l; change bad j = false at b; simpa [core,l,b] using usualBound j (List.mem_range.mpr hj))
    (fun j hj l => by change live j = false at l; simpa [core,l] using usualBound j (List.mem_range.mpr hj))
    (fun j hj l b => by change live j = true at l; change bad j = true at b; simpa [core,l,b] using rareBound j (List.mem_range.mpr hj))
  have io (xs : List ℕ) : (xs.map (fun j => 6*N+6+cost j+(4*N+4))).sum + 2*xs.length ≤
      (xs.map fun j => core j+2+4).sum + xs.length*(10*N+10) := by
    induction xs with
    | nil => simp
    | cons j xs ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      rw [Nat.add_mul xs.length 1,one_mul]
      have dispatch : cost j ≤ core j+4 := by dsimp only [cost]; split <;> omega
      omega
  change (labels.map fun j => core j+2+4).sum+2 ≤ _ at bill
  rw [← show labels.length = LabelMask.records directory from List.length_range] at bill
  have bound := io labels
  simp only [Nat.mul_add] at bill bound ⊢
  nlinarith

private theorem directoryEntryStates_fit [M8.Machine.Net] (t : ℕ) :
    (Blocks.seqB (LeafRoutines.offsets (t := t)) (Blocks.seqB Blocks.push LeafRoutines.view)).states ≤ columnCapacity := by
  apply le_trans _ remainderStates_fit
  change (Blocks.seqB (LeafRoutines.offsets (t := 0)) (Blocks.seqB Blocks.push LeafRoutines.view)).states ≤ 11192
  decide +kernel

private theorem directoryExitStates_fit [M8.Machine.Net] (t : ℕ) :
    (Blocks.seqB (Blocks.restore (t := t)) LeafRoutines.advance).states ≤ columnCapacity := by
  apply le_trans _ remainderStates_fit
  change (Blocks.seqB (Blocks.restore (t := 0)) LeafRoutines.advance).states ≤ 11192
  decide +kernel

open RingFormula in
/-- Tape requirements for one directory pass. Each phase reuses the work bank. -/
structure DirectorySpace [M8.Machine.Net] (T m dim : ℕ) where
  work : ℕ
  leaf : LeafCore.small ≤ work
  entry : (Blocks.seqB (LeafRoutines.offsets (t := T)) (Blocks.seqB Blocks.push LeafRoutines.view)).tapes ≤ CommonBank.count T+work
  exit : (Blocks.seqB (Blocks.restore (t := T)) LeafRoutines.advance).tapes ≤ CommonBank.count T+work
  archive : Record.size dim+(rowSwapBlock.tapes+35+2) ≤ CommonBank.count T+24+31+work+1
  writer : (36+2*m+1+(conjugationDepth m+1)*13)+3 ≤ CommonBank.count T+24+31+work+1
  pool : (conjugationDepth m+1)*13 ≤ work
  matrix : m*m+m*m ≤ CommonBank.count T+24+31+work

theorem directoryTapeBounds (leaf pool entry leave archive writer matrix common host : ℕ) :
    let work := max (max leaf pool) (max (max (entry-common) (leave-common))
      (max (archive-(host+1)) (max (writer-(host+1)) (matrix-host))))
    leaf ≤ work ∧ entry ≤ common+work ∧ leave ≤ common+work ∧ archive ≤ host+work+1 ∧
      writer ≤ host+work+1 ∧ pool ≤ work ∧ matrix ≤ host+work := by
  dsimp only
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

open RingFormula in
/-- Only the largest deficit beyond the permanent tapes needs to be allocated. -/
noncomputable def directorySpace [M8.Machine.Net] (T m dim : ℕ) : DirectorySpace T m dim := by
  let common := CommonBank.count T
  let host := common+24+31
  let entry := (Blocks.seqB (LeafRoutines.offsets (t := T)) (Blocks.seqB Blocks.push LeafRoutines.view)).tapes
  let leave := (Blocks.seqB (Blocks.restore (t := T)) LeafRoutines.advance).tapes
  let archive := Record.size dim+(rowSwapBlock.tapes+35+2)
  let pool := (conjugationDepth m+1)*13
  let writer := (36+2*m+1+pool)+3
  let matrix := m*m+m*m
  let work := max (max LeafCore.small pool) (max (max (entry-common) (leave-common))
    (max (archive-(host+1)) (max (writer-(host+1)) (matrix-host))))
  have h := directoryTapeBounds LeafCore.small pool entry leave archive writer matrix common host
  exact ⟨work, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem directoryReady_of_inputs {K m w W H J : ℕ} {v : Descriptor} {proj : Matrix (Fin m) (Fin m) ℚ}
    {parent : Fin m → ZMod (prime^(w+1))} {prefixes : ℕ → List (Fin (prime+4))} {tail : List (Fin (prime+4))}
    (schedules : List ℕ → List (Fin (prime+4))) (labels : List ℕ) (S : Stacks (66+K) prime) :
    let caller := Fin.castAddEmb (n := 66) K
    let privateTapes := (List.finRange (66+K)).filter fun i => decide (58 ≤ i.val)
    let clean := {S with L := fun i => if i ∈ privateTapes then [] else S.L i,
                         R := fun i => if i ∈ privateTapes then [] else Function.update S.R (caller 54) (schedules labels) i}
    S.R (caller 46) = labels.flatMap (LabelDirectory.entry prefixes m (w+1)) ++ tail →
    (∀ j ∈ labels, (S.R (caller 47)).length = (prefixes j).length) →
    DirectoryHeaders v proj w W H J parent (fun i => S.R (caller (i.castAdd 8))) →
    DirectoryReady v proj w W H J parent prefixes tail schedules clean labels := by
  intro caller privateTapes clean archive widths headers
  have shared (i : Fin 66) (small : i.val < 58) : caller i ∉ privateTapes := by
    simp [privateTapes,caller, Nat.not_le_of_gt small]
  have keep (i : Fin 66) (small : i.val < 58) (ne : i ≠ 54) :
      clean.R (caller i) = S.R (caller i) := by
    simp only [clean,ite_eq_right (shared i small),Function.update_of_ne (caller.injective.ne ne)]
  obtain ⟨scratch,⟨suffix,projector⟩,base,unit,trailing,hdr,one,clock,parents⟩ := headers
  refine ⟨(keep 46 (by decide) (by decide)).trans archive,fun j hj =>
    (congrArg List.length (keep 47 (by decide) (by decide))).trans (widths j hj),?_,
    (keep 49 (by decide) (by decide)).trans scratch,⟨suffix,(keep 48 (by decide) (by decide)).trans projector⟩,
    (keep 2 (by decide) (by decide)).trans base,(keep 28 (by decide) (by decide)).trans unit,
    (keep 53 (by decide) (by decide)).trans trailing,?_,(keep 44 (by decide) (by decide)).trans one,
    (congrArg List.length (keep 45 (by decide) (by decide))).trans clock,(keep 55 (by decide) (by decide)).trans parents,?_⟩
  · intro i hi
    have mem : i ∈ privateTapes := by simp [privateTapes,hi]
    simp [clean,mem]
  · intro i
    apply (keep _ ?_ ?_).trans (hdr i)
    · change 33+i.val < 58; omega
    · intro eq; have h := congrArg Fin.val eq; change 33+i.val = 54 at h; omega
  · change (if caller 54 ∈ privateTapes then [] else Function.update S.R (caller 54) (schedules labels) (caller 54)) = _
    rw [ite_eq_right (shared 54 (by decide)),Function.update_self]

/-- An owner scan records the physical execution and the word read at its endpoint. -/
structure OwnerScan {T Q N : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (program : Pr P T Q prime U) (slot : Fin T) (word : Fin N → ZMod 2)
    (u : HS T Q prime U) (S : Stacks T prime) (n : ℕ) (v : HS T Q prime U) (D : Stacks T prime) : Prop where
  run : Exec body program (mk u S) n (mk v D)
  reads : ∀ j, readAt blank (D.L slot) (D.R slot) j =
    putWord (fun _ => blank) 0 (List.ofFn fun i => SparseRoleCircuit.encode (a := prime) (word i)) j

/-- Sharing the scan slot with a permanent owner updates that word at the same step count. -/
theorem OwnerScan.place {T Q N k : ℕ} {P U : Type} {body : P → Pr P T Q prime U}
    {program : Pr P T Q prime U} {slot : Fin T} {word : Fin N → ZMod 2}
    {u v : HS T Q prime U} {S D : Stacks T prime} {n : ℕ}
    (scan : OwnerScan body program slot word u S n v D)
    (data : Fin k → Fin N → ZMod 2) (src : Fin k) (initial : HS (T+k) Q prime U) (raw : Stacks (T+k) prime) :
    let bank := payloadPlacement slot src
    embDn bank initial = u → embStk bank raw = S →
    (∀ (i : Fin k) j, readAt blank (raw.L (i.natAdd T)) (raw.R (i.natAdd T)) j = (phaseOwners data).tape i j) →
    ∃ z final, Exec (fun f => embProg bank id (body f)) (embProg bank id program) (Host.mk initial raw) n (Host.mk z final) ∧
      embStk bank final = D ∧ z.user = v.user ∧
      (∀ (i : Fin k) j, readAt blank (final.L (i.natAdd T)) (final.R (i.natAdd T)) j =
        (phaseOwners (Function.update data src word)).tape i j) ∧
      ∀ (i : Fin k), i ≠ src → final.L (i.natAdd T) = raw.L (i.natAdd T) ∧ final.R (i.natAdd T) = raw.R (i.natAdd T) := by
  intro bank user projected before
  obtain ⟨z,final,run,_,hu,eq,off⟩ := exec_emb (ι := id) (body' := fun f => embProg bank id (body f)) bank.injective (fun _ => rfl) scan.run initial user raw projected
  have keep (i : Fin k) (hi : i ≠ src) := off _ (payloadPlacement_off slot src i hi)
  refine ⟨z,final,run,eq,hu,?_,keep⟩
  intro i j
  by_cases hi : i = src
  · subst i
    have h := congrArg (fun X : Stacks T prime => readAt blank (X.L slot) (X.R slot) j) eq
    change readAt blank (final.L (bank slot)) (final.R (bank slot)) j = _ at h
    rw [show bank slot = src.natAdd T from payloadPlacement_shared ..] at h
    simpa only [phaseOwners,Function.update_self] using h.trans (scan.reads j)
  · rw [(keep i hi).1,(keep i hi).2]
    simpa only [phaseOwners,Function.update_of_ne hi] using before i j

open RingFormula LabelTraversal IntegerMultBounds.MathlibTM2.Fast.Main RecursiveInterchangeLayout Matrix Finset
  IntegerMultBounds.Swap.LowerTriangular IntegerMultBounds.Swap.Modular in
/-- Execute the generated selector, matrix writer and classified row programs on
the packed PR589 remainder interval, retaining the action and price of each row. -/
def OwnerDirectoryPass [M8.Machine.Net] {T m dim J W : ℕ} {F U : Type}
    (directory v : Descriptor) (w : ℕ) (proj : Matrix (Fin m) (Fin m) ℚ) (rankFits : proj.rank ≤ m)
    (parent parentInv : Fin m → ZMod (prime^(w+1))) (reciprocal : ∀ i, parent i * parentInv i = 1) (io : Fin T)
    (dimension : m+m = dim+1) (H : ℕ)
    (length : volume prime v = (prime^(w+1))^m*((prime^(w+1))^m*W))
    (roleLength : LabelMask.records directory * volume prime v = volume prime directory)
    (anchor : (anchorProgram dim true).1+(anchorProgram dim false).1+1 ≤ columnCapacity) :=
    let d := proj.rank
    let space := directorySpace T m dim
    let work := space.work
    let common := CommonBank.count T
    let K := common+24+31+work
    let M := prime^(w+1)
    let N := volume prime v
    let entry : Graph.Block common prime := Blocks.seqB LeafRoutines.offsets (Blocks.seqB Blocks.push LeafRoutines.view)
    let leave : Graph.Block common prime := Blocks.seqB Blocks.restore LeafRoutines.advance
    let archiveRoom : Record.size dim+(rowSwapBlock.tapes+35+2) ≤ K+1 := space.archive
    fun (body : F → Pr F (66+K) columnCapacity prime U)
      (ownerState : Stacks ((66+(K+1))+5) prime)
      (word : Fin (volume prime directory) → ZMod 2)
      (prefixes : ℕ → List (Fin (prime+4))) (archiveTail ownerTail : List (Fin (prime+4))) (c : ℕ)
      (setupProgram : Pr F ((66+(K+1))+5) columnCapacity prime U)
      (rawUser : HS ((66+(K+1))+5) columnCapacity prime U) (rawState : Stacks ((66+(K+1))+5) prime) (q setupBound : ℕ) (share : ℝ) =>
    let input := ownerRow roleLength word
    let placement := directoryOrdinaryBank archiveRoom
    let outer := fun f => embProg placement id (body f)
    let bank := fun i : Fin (66+(K+1)) => i.castAdd 5
    let reg := fun j : Fin 5 => Fin.natAdd (66+(K+1)) j
    let start := embStk bank ownerState
    let whole := embStk placement start
    let caller := Fin.castAddEmb (n := 66) K
    let labels := List.range (LabelMask.records directory)
    let live := LabelStock.live m (w+1) 1
    let g := physicalLabel m (w+1)
    let bad := fun j => fallbackBit rankFits (reduce M proj) (g j)
    let φ := LabelRing.res prime (w+1) (by omega)
    let table := projectorResidual finSumFinEquiv (reduce prime proj) (φ ∘ parent) (φ ∘ parentInv)
    let schedules := fun js : List ℕ => js.flatMap fun j => if bad j then
      residualSchedule (A := prime) (table (LabelStock.residue m (w+1) 1 j)) else []
    let ready := DirectoryReady v proj w W H J parent prefixes archiveTail schedules
    let privateTapes := (List.finRange (66+K)).filter fun i => decide (58 ≤ i.val)
    let logical := {v with width := d}
    let addr := fun a row pre mid post (x : IntegerMultBounds.Swap.Shear.State (Fin d) (ZMod M)) =>
      index M logical a row pre (FlatCoordinateLayout.rank x.1).val mid (FlatCoordinateLayout.rank x.2).val post
    let G := fun j => g j*reduce M proj*(g j)⁻¹
    let effect := fun label (word next : Fin N → ZMod 2) =>
        ∃ minor : ∀ k (hk : k < d), IsUnit (GoodForm.lead (k+1) (lt_of_lt_of_le hk rankFits) (G label)).det,
        let stage := GoodForm.stageAt (G label) d rankFits minor d le_rfl
        let pivot := fun i : Fin d => stage.M (i.castLE rankFits) (i.castLE rankFits)
        let weights := pivotWeights rankFits parent parentInv reciprocal pivot (fun i => stage.unit _ i.isLt)
        ∀ a < v.beforeRows, ∀ row < v.rows, ∀ pre < v.beforeH, ∀ mid < v.between, ∀ post < v.afterD, ∀ x,
            ext next (addr a row pre mid post (Weighted.child d (fun i => (weights i : ZMod M)) (fun i => (weights i).inv) x)) = ext word (addr a row pre mid post x)
    let coords := packedCoordinatesTime d N w (LeafCore.core io).tapes
      (packedLeafPush (F := Empty) (U := U) io Empty.elim) entry.tapes leave.tapes
    let pivotCost := pivotSetupTime m d w M.size + coords
    let big := Fin.castAddEmb (n := 66) (K+1)
    ∃ (selectors core skip : Pr F (66+K) columnCapacity prime U),
    let e := finSumFinEquiv.trans (finCongr dimension)
    let advance := dropWords (placement (caller 2)) (directoryMatrixTape archiveRoom) (placement (caller 59)) ((dim+1)*(dim+1))
    let good := (embProg placement id (core.seq (clearWorkTapes privateTapes))).seq advance
    let padding := (embProg placement id skip).seq advance
    let program := packedOwner (big 24) (big 57) (ownerDispatch (big 57) (big 56) good (directoryExceptionalProgram m dim archiveRoom anchor) padding)
    let work := (List.finRange (66+(K+1))).filter fun i => decide (58 ≤ i.val ∧ i ≠ directoryMatrixTape archiveRoom)
    let counter := payloadCountProgram (ownerCountPorts (K+1)) (dim+1)
    let controls := embProg bank id (embProg placement id selectors)
    let action := fun j (next : Fin N → ZMod 2) => if live j && bad j then
      ∀ x k, next ((FlatCoordinateLayout.index ((projectorResidual e (reduce M proj) parent parentInv
        (g j)).mulVec x) k).cast (directoryPayloadLength e length)) =
        input j ((FlatCoordinateLayout.index x k).cast (directoryPayloadLength e length))
      else (if live j then effect j else Eq) (input j) next
    ∃ prepare z final t n, ∃ (output : Fin (volume prime directory) → ZMod 2), ∃ k s, z.user = rawUser.user ∧
      OwnerScan (fun f => embProg bank id (outer f)) (setupProgram.seq (counter.seq (controls.seq ((embProg bank id prepare).seq program)))) (reg 0) output rawUser rawState (q+(k+(s+(t+n)))) z final ∧
      (∀ j : Fin (LabelMask.records directory), action j (ownerRow roleLength output j)) ∧
      final.R (reg 0) = payloadWord (SparseRoleCircuit.encode ∘ output) ++ ownerTail ∧ final.R (reg 1) = [] ∧ ready (embStk placement (embStk bank final)) [] ∧
      (embStk bank final).R (directoryMatrixTape archiveRoom) = [] ∧
      (embStk bank final).R (big 57) = [] ∧ (embStk bank final).R (big 56) = [] ∧
      (
        let counterBound := dimensionTime H J (dim+1)+6*N+13*((dim+1)*H+J)+8
        let selectorBound := (privateTapes.map fun i => 4*(whole.L i).length).sum +
          (140+30*(m*m)+6*privateTapes.length)*(volume prime directory)
        let V := volume prime directory
        let suffix := (whole.R (caller 48)).drop (m*m*H)
        let base := directoryQueueInitRate m dim*((1+m*m)*V+archiveTail.length+suffix.length)
        let p := max (mnProgPush (directoryQueueInitProgram (P := F) (U := U) (Q := columnCapacity) archiveRoom space.writer)) c
        let prepareBound := base + ((12*m*m+4+directoryMatrixRate m dim)*V+4) +
          (4*work.length+1+work.length*(6*(p*base)))
        let advanceTime := (dim+1)*(dim+1)*(4*H+4)+1
        let childCost := pivotCost+recordRoundTripRate m*N
        let ordinaryCost := childCost+(12*m*m+4+generatedRecordRate m)*N
        let baseline := max (4*(prefixes 0).length)
          ((max (ordinaryCost+((privateTapes.length*4+1)+6*(max (mnProgPush core) c*ordinaryCost)))
            (1+(4*(prefixes 0).length+4+(m*m*(4*(w+1)+4)+1)+1))) + advanceTime)
        let rate := exceptionalVolumeRate U dim m work.length
          (max (mnProgPush (directoryExceptionalCore (P := F) (U := U) dim archiveRoom anchor)) c) w
        let degree := ∑ k ∈ range d, (k+1)*(m+1)
        ((q+(k+(s+(t+n))) : ℕ) : ℝ) ≤ ((setupBound+counterBound+selectorBound+prepareBound : ℕ) : ℝ) + 4 +
          (((baseline : ℝ)+16)/N + 12 + (degree : ℝ)/prime*rate)*share)

open RingFormula LabelTraversal IntegerMultBounds.MathlibTM2.Fast.Main RecursiveInterchangeLayout Matrix Finset
  IntegerMultBounds.Swap.LowerTriangular IntegerMultBounds.Swap.Modular in
/-- Execute the generated selector, matrix writer and classified row programs on
the packed PR589 remainder interval, retaining the action and price of each row. -/
def OwnerDirectoryRun [M8.Machine.Net] {T m dim J W : ℕ} {F U : Type}
    (directory v : Descriptor) (w : ℕ) (proj : Matrix (Fin m) (Fin m) ℚ) (rankFits : proj.rank ≤ m)
    (parent parentInv : Fin m → ZMod (prime^(w+1))) (reciprocal : ∀ i, parent i * parentInv i = 1) (io : Fin T)
    (dimension : m+m = dim+1) (data : ScanData m dim w W)
    (length : volume prime v = (prime^(w+1))^m*((prime^(w+1))^m*W))
    (roleLength : LabelMask.records directory * volume prime v = volume prime directory)
    (anchor : (anchorProgram dim true).1+(anchorProgram dim false).1+1 ≤ columnCapacity) : Prop :=
    let space := directorySpace T m dim
    let work := space.work
    let common := CommonBank.count T
    let K := common+24+31+work
    let archiveRoom : Record.size dim+(rowSwapBlock.tapes+35+2) ≤ K+1 := space.archive
    ∀ (body : F → Pr F (66+K) columnCapacity prime U)
      (ownerUser : HS ((66+(K+1))+5) columnCapacity prime U) (ownerState : Stacks ((66+(K+1))+5) prime)
      (word : Fin (volume prime directory) → ZMod 2)
      (prefixes : ℕ → List (Fin (prime+4))) (archiveTail ownerTail : List (Fin (prime+4))) (c : ℕ) (bounded : ∀ f, mnProgPush (body f) ≤ c),
    let placement := directoryOrdinaryBank archiveRoom
    let outer := fun f => embProg placement id (body f)
    let bank := fun i : Fin (66+(K+1)) => i.castAdd 5
    let reg := fun j : Fin 5 => Fin.natAdd (66+(K+1)) j
    let start := embStk bank ownerState
    let whole := embStk placement start
    let caller := Fin.castAddEmb (n := 66) K
    let labels := List.range (LabelMask.records directory)
    (∀ i, 58 ≤ i.val → whole.R i = []) →
    (whole.R (caller 29)).length = directory.beforeRows →
    (whole.R (caller 30)).length = directory.rows → (whole.R (caller 31)).length = directory.beforeH →
    whole.R (caller 50) = [] → whole.R (caller 57) = [] → whole.R (caller 56) = [] → whole.R (caller 54) = [] →
    DirectoryScanInput v proj w W data.H J parent prefixes archiveTail labels (fun i => ownerState.R (i.castLE (by omega))) →
    let big := Fin.castAddEmb (n := 66) (K+1)
    data.records = LabelMask.records directory → (prefixes 0).length ≤ volume prime v → start.R (directoryMatrixTape archiveRoom) = [] →
    ownerState.R (reg 0) = payloadWord (SparseRoleCircuit.encode ∘ word) ++ ownerTail →
    (∀ j, readAt blank (ownerState.L (reg 0)) (ownerState.R (reg 0)) j = RadixToBinary.binaryEncoding.encode
      (putWord (fun _ => blank) 0 ((List.ofFn word).map SparseRoleCircuit.encode) j)) → ownerState.R (reg 1) = [] →
    ownerState.R (reg 2) = [] → ownerState.R (reg 3) = [] → ownerState.R (reg 4) = [] →
    (∀ j, readAt blank (start.L (big 24)) (start.R (big 24)) j = blank) →
    ∀ (setupProgram : Pr F ((66+(K+1))+5) columnCapacity prime U)
      (rawUser : HS ((66+(K+1))+5) columnCapacity prime U) (rawState : Stacks ((66+(K+1))+5) prime) (q setupBound : ℕ) (share : ℝ),
      (volume prime directory : ℝ) = share → q ≤ setupBound → ownerUser.user = rawUser.user →
      Exec (fun f => embProg bank id (outer f)) setupProgram (mk rawUser rawState) q (mk ownerUser ownerState) →
      OwnerDirectoryPass (J := J) directory v w proj rankFits parent parentInv reciprocal io dimension data.H length roleLength anchor
        body ownerState word prefixes archiveTail ownerTail c setupProgram rawUser rawState q setupBound share

theorem ownerWord_reads {N : ℕ} (word output : Fin N → ZMod 2) (tail : List (Fin (prime+4)))
    {left right finalLeft finalRight : List (Fin (prime+4))}
    (input : right = payloadWord (SparseRoleCircuit.encode ∘ word) ++ tail)
    (reads : ∀ j, readAt blank left right j = RadixToBinary.binaryEncoding.encode
      (putWord (fun _ => blank) 0 ((List.ofFn word).map SparseRoleCircuit.encode) j))
    (saved : finalLeft = left) (result : finalRight = payloadWord (SparseRoleCircuit.encode ∘ output) ++ tail) :
    ∀ j, readAt blank finalLeft finalRight j = RadixToBinary.binaryEncoding.encode
      (putWord (fun _ => blank) 0 ((List.ofFn output).map SparseRoleCircuit.encode) j) := by
  subst right finalLeft finalRight
  intro j
  have h := returnedPayload_reads (SparseRoleCircuit.encode ∘ output) (fun _ => blank) 0 left
    (payloadWord (SparseRoleCircuit.encode ∘ word)) tail (by simp [payloadWord]) (by
      intro k outside
      have old := reads k
      rw [putWord_outside _ _ _ _ (by simpa using outside)] at old
      simpa only [sub_zero] using old.symm) j
  simpa only [List.map_ofFn,Function.comp_def,sub_zero] using h.symm

open RingFormula LabelTraversal IntegerMultBounds.MathlibTM2.Fast.Main RecursiveInterchangeLayout Matrix Finset
  IntegerMultBounds.Swap.LowerTriangular IntegerMultBounds.Swap.Modular in
private theorem generatedOwnerDirectory_exec [M8.Machine.Net] {T m dim J W : ℕ} {F U : Type}
    (directory : Descriptor) (B : ℕ) (positiveDir : directory.Positive)
    (v : Descriptor) (positive : v.Positive) (w : ℕ)
    (shape : directory.beforeH = B*prime^(m*((w+1)*m))) (proj : Matrix (Fin m) (Fin m) ℚ)
    (width : v.width = proj.rank*(w+1)) (idem : proj*proj = proj)
    (factor : Factorization univ univ proj) (hd : ∀ a ∈ factorizationDenominators factor, a < prime)
    (active : 0 < proj.rank) (rankFits : proj.rank ≤ m) (parent parentInv : Fin m → ZMod (prime^(w+1)))
    (reciprocal : ∀ i, parent i * parentInv i = 1) (io : Fin T) (arity : ℕ)
    (dimension : m+m = dim+1) (data : ScanData m dim w W) (binary : data.H = (prime^(w+1)).size) (digits : J = W.size) (hW : 0 < W)
    (length : volume prime v = (prime^(w+1))^m*((prime^(w+1))^m*W))
    (roleLength : LabelMask.records directory * volume prime v = volume prime directory)
    (anchor : (anchorProgram dim true).1+(anchorProgram dim false).1+1 ≤ columnCapacity) :
    OwnerDirectoryRun (F := F) (U := U) (J := J) directory v w proj rankFits parent parentInv reciprocal io dimension data length roleLength anchor := by
  have hm : prime^(w+1) < 2^data.H := binary ▸ Nat.size_le.mp (le_refl _)
  have hw : W < 2^J := digits ▸ Nat.size_le.mp (le_refl _)
  unfold OwnerDirectoryRun
  intro space work common K archiveRoom body ownerUser ownerState word prefixes archiveTail ownerTail c bounded
    placement outer bank reg start whole caller labels free brSize rowsSize beforeSize parents mask mode queue scanInput
    big count prefixFits empty owner ownerRead accumulator size saved tmp blankPort setupProgram rawUser rawState q setupBound share shareEq setupPaid prefixUser prefixRun
  unfold OwnerDirectoryPass
  let d := proj.rank
  let M := prime^(w+1)
  let N := volume prime v
  let entry : Graph.Block common prime := Blocks.seqB LeafRoutines.offsets (Blocks.seqB Blocks.push LeafRoutines.view)
  let leave : Graph.Block common prime := Blocks.seqB Blocks.restore LeafRoutines.advance
  intro input _ _ _ _ _ _ _ postLabels live g bad φ table schedules ready privateTapes logical addr G effect coords pivotCost _
  let raw := ((dimensionTime data.H 1 m+(4*(m*data.H+1)+6)+(10*J+12)+(6*(M^m).size+6)) +
    (recordWeightLoadTime m w data.H M.size+(recordMatrixLoadTime m data.H M.size+(pivotCost+2*((218*N+1)*13+6)+3))))
  let trip := if 0 < d ∧ data.H = M.size ∧ J = W.size then min raw (pivotCost+recordRoundTripRate m*N) else raw
  let runCost := fun j => generatedRecordTime m w data.H (prefixes j).length (descriptorHeaderCost v) trip
  let price := fun (core : Pr F (66+K) columnCapacity prime U) j => if live j then
    runCost j + ((privateTapes.length*4+1) + 6*(max (mnProgPush core) c * runCost j))
    else 1+(4*(prefixes j).length+4+(m*m*(4*(w+1)+4)+1)+1)
  let payload := RecordPayload (N := N) (caller 24) (fun _ => blank) 0
  let selectorBudget := (26*prime^w+4) + ((44*labels.length+13*(w+1)+16) + 3*((6+10*(m*m))*labels.length+4) +
        (2*(directory.beforeRows*directory.rows*B)+2)) +
        ((privateTapes.map fun i => 4*(whole.L i).length).sum + privateTapes.length*(2*prime^w+4)+1)
  have shared : (fun i : Fin 58 => whole.R (caller (i.castAdd 8))) =
      fun i => ownerState.R (i.castLE (by omega)) := by
    funext i
    change ownerState.R ((placement ((i.castAdd 8).castAdd K)).castAdd 5) = _
    rw [show placement ((i.castAdd 8).castAdd K) = (i.castAdd 8).castAdd (K+1) from directoryOrdinaryBank_caller archiveRoom _]
    rfl
  have vol := directoryPayloadLength (finSumFinEquiv.trans (finCongr dimension)) length
  obtain ⟨_,_,base,_,trailing,_⟩ := scanInput.headers
  obtain ⟨prepared,filled,k,sameUser,paidCounter,counterRun,view,filledSize,countLeft,stays⟩ := ownerCount_exec
    (fun f => embProg bank id (outer f)) (dim+1) data.H J M W hm hw ownerUser ownerState vol base trailing (by
      intro i hi
      have clean := free (caller i) (by change 58 ≤ i.val; omega)
      change ownerState.R ((placement (i.castAdd K)).castAdd 5) = [] at clean
      rwa [directoryOrdinaryBank_caller archiveRoom i] at clean) size
  change embStk bank filled = start at view
  have wholeEq : embStk placement (embStk bank filled) = whole := congrArg (embStk placement) view
  let u := embDn placement (embDn bank prepared)
  rw [← shared] at scanInput
  have initial := directoryReady_of_inputs schedules labels whole scanInput.archive scanInput.widths scanInput.headers
  have spec := generatedRecordScan_exec v positive w proj width idem factor hd rankFits parent parentInv reciprocal io arity
    hm hw hW length (le_max_left ..) (fun _ => blank) 0 space.leaf (columnLeafFits io) space.entry space.exit (directoryEntryStates_fit T) (directoryExitStates_fit T) (fun _ => 0) body u whole space.pool directory prefixes archiveTail
    c bounded space.matrix B shape free positiveDir brSize rowsSize beforeSize parents mask mode queue initial
  obtain ⟨writer,z,D,t,user,time,run,done,step,keepL,keepR,projectorKept,liveBits,badBits,_⟩ := spec
  let slot := (((LeafCore.roleSlot io).castAdd 24).castAdd 31).castAdd work
  have port : recordRoundTripPorts slot 0 = caller 24 := recordRoundTripPorts_other slot 0 (by decide)
  have finish {core padding : Pr F (66+K) columnCapacity prime U}
      (rows : ∀ j js word y A, ¬ (live j = true ∧ bad j = true) → ready A (j::js) →
        RecordPayload (recordRoundTripPorts slot 0) (fun _ => blank) 0 word A →
        ∃ z D t next, z.user = y.user ∧ t ≤ price core j ∧
          Exec body (if live j then core.seq (clearWorkTapes privateTapes) else padding) (mk y A) t (mk z D) ∧ ready D js ∧
          (if live j then effect j else Eq) word next ∧
          RecordPayload (recordRoundTripPorts slot 0) (fun _ => blank) 0 next D ∧
          D.R (caller 57) = A.R (caller 57) ∧ D.R (caller 56) = A.R (caller 56)) :
      ∃ (core padding : Pr F (66+K) columnCapacity prime U), ∀ j js word y A, ¬ (live j = true ∧ bad j = true) →
        ready A (j::js) → payload word A →
        ∃ z D t next, z.user = y.user ∧ t ≤ price core j ∧
          Exec body (if live j then core.seq (clearWorkTapes privateTapes) else padding) (mk y A) t (mk z D) ∧
          ready D js ∧ (if live j then effect j else Eq) word next ∧ payload next D ∧
          D.R (caller 57) = A.R (caller 57) ∧ D.R (caller 56) = A.R (caller 56) :=
    ⟨core,padding,by simpa only [payload,port] using rows⟩
  obtain ⟨core,padding,ordinary⟩ := finish step
  have left : D.L (caller 24) = whole.L (caller 24) := by rw [← port]; exact keepL
  have right : D.R (caller 24) = whole.R (caller 24) := by rw [← port]; exact keepR
  let action := fun j => (if live j then effect j else Eq) (input j)
  have adm : Admissible prime proj := by
    simpa using admissible_of_lt Networks.Shared50ModularControl.prime_prime
      (fun k (h : k ∈ denominators proj) => hd k (by simp [factorizationDenominators,h])) 1
  have bodyBound (f) : mnProgPush (outer f) ≤ c := by
    simpa only [outer,embProg_push] using bounded f
  have filledBlank : ∀ j, readAt blank ((embStk bank filled).L (big 24)) ((embStk bank filled).R (big 24)) j = blank := by
    rw [view]
    exact blankPort
  have filledEmpty : (embStk bank filled).R (directoryMatrixTape archiveRoom) = [] := by
    rw [view]
    exact empty
  have startRun {p} (h : Exec body p (mk u whole) t (mk z D)) :
      Exec body p (mk u (embStk placement (embStk bank filled))) t (mk z D) := by rw [wholeEq]; exact h
  have runFilled := startRun run
  have pass := classifiedDirectory_exec dimension v proj idem adm parent parentInv reciprocal data hm hw hW
    archiveRoom space.writer anchor outer c bodyBound prefixes archiveTail bad (price core) action length input body (fun _ => rfl)
    _ (core.seq (clearWorkTapes privateTapes)) padding selectorBudget ownerTail prepared filled filledEmpty
    ⟨z,D,t,user,time,runFilled,by simpa only [count] using done,
      by rw [wholeEq]; exact left,by rw [wholeEq]; exact right,by rw [wholeEq]; exact projectorKept,
      by simpa only [count] using liveBits,by simpa only [count] using badBits⟩
    (by simpa only [count,input,Function.comp_def] using ((stays 0 (by decide)).trans owner).trans (congrArg (· ++ ownerTail) (ownerRow_queue roleLength word))) ((stays 1 (by decide)).trans accumulator)
    filledSize ((stays 3 (by decide)).trans saved) ((stays 4 (by decide)).trans tmp)
    filledBlank
    (fun j _ no y A readyRow payloadRow => ordinary j _ (input j) y A no readyRow payloadRow)
  obtain ⟨prepare,finishState,final,t,n,rows,s,midUser,mid,hu,setup,controls,midReady,projectorEq,initBound,scan,exec,correct,ownerLeft,out,free,done,archive,maskEnd,modeEnd⟩ := pass
  have recordsPos : 0 < LabelMask.records directory :=
    Nat.mul_pos (Nat.mul_pos positiveDir.1 positiveDir.2.1) positiveDir.2.2.1
  have radixPos : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
  have radixFits : M ≤ N := by
    change prime^(w+1) ≤ volume prime v
    rw [← directoryPayloadLength (finSumFinEquiv.trans (finCongr dimension)) length,pow_succ]
    exact (Nat.le_mul_of_pos_left _ (pow_pos radixPos dim)).trans (Nat.le_mul_of_pos_right _ hW)
  have boxes : directory.beforeRows*directory.rows*B ≤ LabelMask.records directory := by
    change _ ≤ directory.beforeRows*directory.rows*directory.beforeH
    rw [shape,← Nat.mul_assoc]
    exact Nat.le_mul_of_pos_right _ (pow_pos Shared50ModularControl.prime_prime.pos _)
  have setupVolume := maskSetup_volume_le m w (LabelMask.records directory) (directory.beforeRows*directory.rows*B)
    privateTapes.length ((privateTapes.map fun i => 4*(whole.L i).length).sum) (LabelMask.records directory*N)
    (radixFits.trans (Nat.le_mul_of_pos_left _ recordsPos))
    (Nat.le_mul_of_pos_right _ (radixPos.trans_le radixFits)) boxes
  have selectorsPaid := setup.trans (by simpa only [selectorBudget,labels,List.length_range] using setupVolume)
  rw [count] at correct
  obtain ⟨output,rowAction,packed⟩ := ownerRows_pack roleLength correct
  refine ⟨_,core,padding,prepare,finishState,final,t,n,output,k,s,(hu.trans sameUser).trans prefixUser,
    ⟨Exec.seq prefixRun (Exec.seq counterRun exec),?_⟩,rowAction,out.trans (congrArg (· ++ ownerTail) packed),free,done,archive,maskEnd,modeEnd,?_⟩
  · intro j
    rw [← encodedOwnerCell]
    exact ownerWord_reads word output ownerTail owner ownerRead
      (ownerLeft.trans (congrFun countLeft _)) (out.trans (congrArg (· ++ ownerTail) packed)) j
  intro counterBound selectorBound V suffix base p prepareBound advanceTime childCost ordinaryCost baseline rate degree
  apply packedOwner_charge _ _ labels.length N baseline degree rate share
    (by simpa only [labels,List.length_range,← Nat.cast_mul,roleLength,N] using
          (show ((LabelMask.records directory*volume prime v : ℕ) : ℝ) = share from
            (congrArg Nat.cast roleLength).trans shareEq))
    (radixPos.trans_le radixFits)
  simp only [Nat.add_assoc]
  apply Nat.add_le_add setupPaid
  apply Nat.add_le_add paidCounter
  apply Nat.add_le_add (show s ≤ selectorBound by
    simpa only [selectorBound,labels,List.length_range,roleLength,N] using selectorsPaid)
  apply Nat.add_le_add (show t ≤ prepareBound by
    have positiveRecords : 0 < data.records := count ▸ recordsPos
    obtain ⟨initLe,queueLe⟩ := DirectoryReady.matrixSetup_volume data archiveRoom (embStk bank mid) midReady
      binary radixFits positiveRecords
    have widthEq := midReady.2.1 0 (List.mem_range.mpr positiveRecords)
    change ((embStk bank mid).R (placement (caller 47))).length = (prefixes 0).length at widthEq
    have placed : placement (caller 47) = big 47 := directoryOrdinaryBank_caller archiveRoom 47
    rw [placed] at widthEq
    change ((embStk bank mid).R ((47 : Fin 66).castAdd (K+1))).length = _ at widthEq
    change (embStk bank mid).R (big 48) = (embStk placement (embStk bank filled)).R (caller 48) at projectorEq
    rw [wholeEq] at projectorEq
    change (embStk bank mid).R ((48 : Fin 66).castAdd (K+1)) = whole.R (caller 48) at projectorEq
    have paid := (initBound p (le_max_left ..) (fun f => (bodyBound f).trans (le_max_right ..))).trans (Nat.add_le_add (Nat.add_le_add initLe queueLe) (Nat.add_le_add_left
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left p initLe))) _))
    simpa only [widthEq,projectorEq,max_eq_right prefixFits,count,roleLength,V,N] using paid)

  let e := finSumFinEquiv.trans (finCongr dimension)
  let physical := data.physical e proj parent parentInv
  let scratch := (List.finRange (66+(K+1))).filter fun i => decide (58 ≤ i.val ∧ i ≠ directoryMatrixTape archiveRoom)
  let pushBound := max (mnProgPush (directoryExceptionalCore (P := F) (U := U) dim archiveRoom anchor)) c
  let rare := fun j =>
    let C := physical.table (LabelStock.residue m (w+1) 1 j)
    let pivots := classPivots C
    exceptionalRecordTime U pivots (negativeAnchor pivots C) m w W data.H J scratch.length pushBound (prefixes j).length
  have widths (j) (hj : j ∈ labels) : (prefixes j).length = (prefixes 0).length := by
    have inside := List.mem_range.mp hj
    exact (initial.2.1 j hj).symm.trans (initial.2.1 0 (List.mem_range.mpr (by omega)))
  have tripBound : trip ≤ childCost := by
    change (if 0 < proj.rank ∧ data.H = (prime^(w+1)).size ∧ J = W.size then
      min raw (pivotCost+recordRoundTripRate m*N) else raw) ≤ pivotCost+recordRoundTripRate m*N
    rw [if_pos ⟨active,binary,digits⟩]
    exact min_le_right ..
  have ordinaryBound : runCost 0 ≤ ordinaryCost := by
    have run := generatedRecordTime_binary_le m w (prefixes 0).length trip v positive radixFits
    change generatedRecordTime m w M.size _ _ _ ≤ _ at run
    calc
      runCost 0 ≤ trip+(12*m*m+4)*(prefixes 0).length+generatedRecordRate m*N := by
        simpa only [runCost,binary,N] using run
      _ ≤ childCost+(12*m*m+4)*N+generatedRecordRate m*N :=
        Nat.add_le_add_right (Nat.add_le_add tripBound (Nat.mul_le_mul_left _ prefixFits)) _
      _ = ordinaryCost := by dsimp only [ordinaryCost]; ring
  apply (show n ≤ _ from scan).trans
  rw [count]
  apply packedClassifiedTime_le (N := N) idem factor hd rankFits directory shape
    (fun j => price core j + advanceTime) rare baseline (rate*N)
  · intro j hj
    have same : runCost j = runCost 0 := by simp only [runCost,widths j hj]
    apply le_trans _ (Nat.le_max_right ..)
    apply Nat.add_le_add_right
    dsimp only [price]
    rw [same,widths j hj]
    split
    · apply le_trans _ (Nat.le_max_left ..)
      exact Nat.add_le_add ordinaryBound (Nat.add_le_add_left
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ordinaryBound)) _)
    · exact Nat.le_max_right ..
  · intro j hj
    let C := physical.table (LabelStock.residue m (w+1) 1 j)
    have bound : exceptionalRecordTime U (classPivots C) (negativeAnchor (classPivots C) C) m w W M.size W.size
        scratch.length pushBound (prefixes j).length ≤ rate*(M^(dim+1)*W)+4*(prefixes j).length :=
      (exceptionalRecordTime_binary_le U dim m scratch.length pushBound).choose_spec.choose_spec
        (classPivots C) (negativeAnchor (classPivots C) C) w W (prefixes j).length hW
    change exceptionalRecordTime U _ _ _ _ _ data.H J _ _ _ ≤ _
    rw [binary,digits]
    apply bound.trans
    rw [directoryPayloadLength e length,widths j hj,Nat.add_comm]
    exact Nat.add_le_add_right (Nat.le_max_left ..) _


theorem remainderAnchorFits [M8.Machine.Net] :
    (anchorProgram 127 true).1+(anchorProgram 127 false).1+1 ≤ columnCapacity :=
  (show (anchorProgram 127 true).1+(anchorProgram 127 false).1+1 = 11192 by decide +kernel).le.trans remainderStates_fit

/-- Split the inherited tape at the measured entry width, retaining its suffix. -/
private theorem splitParentWords {α : Type} (xs : List α) (width parents : ℕ) :
    xs = (List.range parents).flatMap (fun i => (xs.drop (i*width)).take width) ++
      xs.drop (parents*width) := by
  induction parents with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton,List.append_assoc,Nat.succ_mul]
    rw [List.drop_take_append_drop]
    exact ih

open RingFormula LabelTraversal IntegerMultBounds.MathlibTM2.Fast.Main RecursiveInterchangeLayout Matrix Finset
  IntegerMultBounds.Swap.LowerTriangular IntegerMultBounds.Swap.Modular in
/-- Run the selected remainder interval on its owner. With no incoming weights the root writes
64 padded ones on the empty weight tape. A recursive invocation reads the packed incoming units. -/
theorem remainderOwnerDirectory_exec [M8.Machine.Net] {T : ℕ} {F U : Type}
    (interval : ℕ × ℕ) (member : interval ∈ BitHosting.remainderIntervals) (layout : Descriptor) (w rows B : ℕ)
    (positiveLayout : layout.Positive) (layoutWidth : layout.width = 64*(w+1)) (split : layout.rows = 142080*rows)
    (shape : layout.beforeH = B*prime^(64*((w+1)*64)))
    (incoming : Option (Fin 64 → (ZMod (prime^(w+1)))ˣ))
    (io : Fin T) (arity : ℕ) :
    let H := (prime^(w+1)).size
    let weights := incoming.getD (fun _ => 1)
    let parent := fun i => (weights i : ZMod (prime^(w+1)))
    let parentInv := fun i => (↑((weights i)⁻¹) : ZMod (prime^(w+1)))
    let W := layout.between*layout.afterD
    let m := 64
    let dim := 127
    let J := W.size
    let v := remainderRecordChild interval.1 interval.2 (w+1) W
    let proj : Matrix (Fin m) (Fin m) ℚ := Matrix.diagonal fun i =>
      if interval.1 ≤ i.val ∧ i.val < interval.2 then 1 else 0
    let rankFits : proj.rank ≤ m := proj.rank_le_height
    let dimension : m+m = dim+1 := by decide
    let length : volume prime v = (prime^(w+1))^m*((prime^(w+1))^m*W) := by
      obtain ⟨ordered,upper,_⟩ := BitHosting.remainder_counts interval member
      exact remainderRecordChild_volume _ _ _ _ (by omega)
    let roleLength : LabelMask.records (role layout 142080)*volume prime v = volume prime (role layout 142080) := by
      have packed := remainderRecord_volume layout w rows interval member layoutWidth split
      have total := role_volume_mul prime 142080 layout ⟨rows,split⟩
      exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 142080) (packed.trans total.symm)
    let directory := role layout 142080
    let space := directorySpace T m dim
    let K := CommonBank.count T+24+31+space.work
    let room : 72 ≤ 66+(K+1) := by dsimp only [K]; omega
    let bank := (Fin.castLEEmb room).trans (Fin.castAddEmb 5)
    let r := remainderDirectoryPorts.trans bank
    let parents := layout.beforeRows*rows*B
    let box := (prime^(w+1))^(64*64)
    let scratch := ([0,4,9,10,11,12] : List (Fin 15)).map r ++ [bank 71]
    let reg := fun i : Fin 5 => i.natAdd (66+(K+1))
    ∀ (body : F → Pr F (66+K) columnCapacity prime U) (u : HS ((66+(K+1))+5) columnCapacity prime U)
      (raw : Stacks ((66+(K+1))+5) prime) (word : Fin (volume prime directory) → ZMod 2)
      (c : ℕ),
      let source := raw.R (bank 58)
      let width := (raw.R (bank 47)).length
      let inherited := fun i => (source.drop (i*width)).take width
      let tail := source.drop (parents*width)
      let setupBound := (366+16*64*64+19*64+344)*(LabelMask.records directory*prime^layout.width*W) +
        (scratch.map (fun i => 4*(raw.L i).length)).sum + 2*tail.length
      (∀ f, mnProgPush (body f) ≤ c) →
      (raw.R (bank 29)).length = layout.beforeRows → (raw.R (bank 30)).length = rows →
      (raw.R (bank 31)).length = layout.beforeH →
      (∀ i : Fin (66+(K+1)), 59 ≤ i.val → raw.R (i.castAdd 5) = []) →
      parents*width ≤ source.length →
      (raw.R (bank 47)).length ≤ prime^layout.width →
      raw.R (bank 28) = [] → raw.R (bank 44) = [] → raw.R (bank 49) = [] → DirectorySeed w W H J (incoming.elim [] (fun ws =>
        (List.ofFn fun i => binSyms H (ws i : ZMod (prime^(w+1))).val).flatten)) (fun i => raw.R (bank (i.castLE (by decide)))) →
      raw.R (bank 50) = [] → raw.R (bank 57) = [] → raw.R (bank 56) = [] → raw.R (bank 54) = [] →
      (∀ j, readAt blank (raw.L (reg 0)) (raw.R (reg 0)) j =
        putWord (fun _ => blank) 0 (List.ofFn fun i => SparseRoleCircuit.encode (a := prime) (word i)) j) →
      (∀ i : Fin 5, i ≠ 0 → raw.R (reg i) = []) →
      (∀ j, readAt blank (raw.L (bank 24)) (raw.R (bank 24)) j = blank) →
      ∃ D q, (∀ k, (D.L k).length ≤ (raw.L k).length) ∧ D.R (bank 48) = matrixWords prime H (reduce (prime^(w+1)) proj) ++ raw.R (bank 48) ∧
        OwnerDirectoryPass (J := J) directory v w proj rankFits parent parentInv (fun i => (weights i).val_inv) io dimension H length roleLength remainderAnchorFits
          body D word (fun j => inherited (j/box)) (raw.R (bank 46)) ((raw.R (reg 0)).drop (volume prime directory)) c (remainderOwnerSetup incoming.isNone interval.1 interval.2 bank) u raw q setupBound ((volume prime layout : ℝ)/142080) := by
  intro H weights parent parentInv W m dim J v proj rankFits dimension length roleLength
  -- The physical scan generates its matrices and reads each row from the owner.
  let data : ScanData 64 127 w W := {
    records := LabelMask.records (role layout 142080), H := H, J := J,
    table := fun _ => 0, matrix := fun _ => 0, input := fun _ _ => 0,
    signed := [], matrixTail := [], pivotTail := [], inputTail := [], outputTail := [] }
  have precision : data.H = (prime^(w+1)).size := rfl
  have reciprocal (i) : parent i * parentInv i = 1 := (weights i).val_inv
  obtain ⟨ordered,upper,_⟩ := BitHosting.remainder_counts interval member
  have rank : proj.rank = interval.2-interval.1 := intervalDiagonal_rank (show interval.2 ≤ m by dsimp [m]; omega)
  have width : v.width = proj.rank*(w+1) := by rw [rank]; rfl
  have pos : 0 < prime^(w+1) := pow_pos Shared50ModularControl.prime_prime.pos _
  have hW : 0 < W := Nat.mul_pos positiveLayout.2.2.2.1 positiveLayout.2.2.2.2
  have positive : v.Positive := ⟨Nat.zero_lt_one,Nat.zero_lt_one,Nat.zero_lt_one,pow_pos pos _,hW⟩
  have idem := intervalDiagonal_idem m interval.1 interval.2
  let factor := intervalFactor m interval.1 interval.2
  have hd := intervalFactor_denominators m interval.1 interval.2
  have rolePositive := RecursiveRowsNodeLayout.role_positive 142080 layout (by decide) positiveLayout ⟨rows,split⟩
  have pass := generatedOwnerDirectory_exec (F := F) (U := U) (role layout 142080) B rolePositive v positive w shape proj width idem factor hd (by rw [rank]; exact Nat.sub_pos_of_lt (BitHosting.remainder_counts_strict interval member).1) rankFits parent parentInv reciprocal
    io arity dimension data precision (show J = W.size from rfl) hW length roleLength remainderAnchorFits

  intro directory space K room bank r parents box scratch reg body u raw word c source width inherited tail setupBound bounded
    br nr bh clean capacity fits short padded spare params parentPort mask mode queue payload empty blankData
  have packedSource := splitParentWords source width parents
  have widths (i : ℕ) (hi : i < parents) : (inherited i).length = width := by
    have bound := (Nat.mul_le_mul_right width (Nat.succ_le_of_lt hi)).trans capacity
    rw [Nat.succ_mul] at bound
    simp only [inherited,List.length_take,List.length_drop]
    exact Nat.min_eq_left (by omega)
  let placement := directoryOrdinaryBank space.archive
  let outer := fun f => embProg (fun i : Fin (66+(K+1)) => i.castAdd 5) id (embProg placement id (body f))
  have parameters : ParentParameters incoming.isNone W data.H J parent (fun i => raw.R (bank (i.castLE (by decide)))) := by
    cases incoming with
    | none => exact ⟨fun _ => rfl,params⟩
    | some ws => exact params
  obtain ⟨y,D,q,user,paid,build,input,free,matrix,right,left,size,regs⟩ :=
    remainderDirectory_prepareOwner room outer layout v w rows B W data.H J positiveLayout layoutWidth split shape
      interval.1 interval.2 precision rfl rfl ordered (by omega) (by intro i; fin_cases i <;> rfl) incoming.isNone parent inherited tail u raw br nr bh clean packedSource widths fits short padded spare parameters
  let whole := embStk placement (embStk (fun i : Fin (66+(K+1)) => i.castAdd 5) D)
  have frame (i : Fin 58) (off : i ∉ ([28,33,34,35,36,37,38,44,46,48,55] : List (Fin 58))) :
      whole.R ((i.castAdd 8).castAdd K) = raw.R (bank (i.castLE (by decide))) := by
    change D.R ((placement ((i.castAdd 8).castAdd K)).castAdd 5) = _
    rw [directoryOrdinaryBank_caller]
    exact right i off
  have workEmpty (i : Fin (66+K)) (hi : 58 ≤ i.val) : whole.R i = [] := by
    apply free
    by_contra! lo
    let j : Fin 66 := ⟨(placement i).val,by omega⟩
    have eq : placement i = placement (j.castAdd K) := by rw [directoryOrdinaryBank_caller]; exact Fin.ext rfl
    have h := congrArg Fin.val (placement.injective eq)
    change i.val = (placement i).val at h
    omega
  have roleRows : directory.rows = rows := by simp [directory,role,split]
  have saved (i : Fin 5) (hi : i ≠ 0) := (regs i).1.trans (empty i hi)
  simp_rw [← encodedOwnerCell] at payload
  have packed := payload_prefix_of_read word (fun _ => blank) 0 (raw.L (reg 0)) (raw.R (reg 0)) (by simpa only [sub_zero] using payload)
  have parentsPos : 0 < parents := by
    have rowsPos : 0 < rows := roleRows ▸ rolePositive.2.1
    have bPos : 0 < B := by
      by_contra! hz
      have := positiveLayout.2.2.1
      simp [shape,Nat.eq_zero_of_le_zero hz] at this
    exact Nat.mul_pos (Nat.mul_pos positiveLayout.1 rowsPos) bPos
  have prefixFits : (inherited (0/box)).length ≤ volume prime v := by
    rw [Nat.zero_div,widths 0 parentsPos]
    apply fits.trans
    rw [layoutWidth,Nat.mul_comm 64 (w+1),pow_mul,length]
    exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (pow_pos pos _) hW)
  have setupPaid : q ≤ setupBound := by
    have scale : 0 < prime^layout.width*142080 := Nat.mul_pos (pow_pos Shared50ModularControl.prime_prime.pos _) (by decide)
    have ownerVolume : LabelMask.records directory*prime^layout.width*W*prime^layout.width =
        volume prime directory := by
      dsimp only [LabelMask.records,volume,directory,role,W]
      ring
    have full := role_volume_mul prime 142080 layout ⟨rows,split⟩
    apply Nat.le_of_mul_le_mul_right _ scale
    calc
      q*(prime^layout.width*142080) = prime^layout.width*q*142080 := by ring
      _ ≤ _ := paid
      _ = setupBound*(prime^layout.width*142080) := by
        rw [← full,← ownerVolume]
        dsimp only [setupBound]
        ring
  refine ⟨D,q,size,matrix,?_⟩
  exact pass body y D word (fun j => inherited (j/box)) (raw.R (bank 46)) ((raw.R (reg 0)).drop (volume prime directory)) c bounded workEmpty
    ((congrArg List.length (frame 29 (by decide))).trans br)
    (((congrArg List.length (frame 30 (by decide))).trans nr).trans roleRows.symm)
    ((congrArg List.length (frame 31 (by decide))).trans bh)
    ((frame 50 (by decide)).trans parentPort) ((frame 57 (by decide)).trans mask)
    ((frame 56 (by decide)).trans mode) ((frame 54 (by decide)).trans queue) input rfl prefixFits
    (free _ (by have h := directoryMatrixTape_private space.archive; omega))
    ((regs 0).1.trans packed) (by intro j; rw [(regs 0).1,(regs 0).2]; exact payload j) (saved 1 (by decide)) (saved 2 (by decide)) (saved 3 (by decide)) (saved 4 (by decide))
    (by intro j; change readAt blank (D.L (bank 24)) (D.R (bank 24)) j = blank
        have hl : D.L (bank 24) = raw.L (bank 24) := left 24
        have hr : D.R (bank 24) = raw.R (bank 24) := right 24 (by decide)
        rw [hl,hr]; exact blankData j)
    (remainderOwnerSetup incoming.isNone interval.1 interval.2 bank) u raw q setupBound ((volume prime layout : ℝ)/142080) (by
      apply (eq_div_iff (by norm_num)).mpr
      exact_mod_cast role_volume_mul prime 142080 layout ⟨rows,split⟩) setupPaid user build

/-- The idle descriptor has the width, volume, and rational pivot certificate
required by the generated record program, with the actual binary header sizes. -/
theorem remainderRecord_scan [M8.Machine.Net] {T work Q : ℕ} {F U : Type}
    (e : ℕ × ℕ) (he : e ∈ BitHosting.remainderIntervals) (w W : ℕ) (hW : 0 < W)
    (parent parentInv : Fin 64 → ZMod (prime^(w+1))) (inv : ∀ i, parent i * parentInv i = 1)
    (io : Fin T) (arity : ℕ) (source : ℤ → Fin 4) (head : ℤ)
    (capacity : 217 ≤ Q) (fits : LeafCore.small ≤ work) (cap : (LeafCore.core io).states ≤ Q) (single : Bool := false) :
    let M := prime^(w+1)
    let child := remainderRecordChild e.1 e.2 (w+1) W
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
    ⟨Nat.zero_lt_one,Nat.zero_lt_one,Nat.zero_lt_one,pow_pos pos _,hW⟩
  have length : volume prime child = M^64*(M^64*W) := by
    exact remainderRecordChild_volume _ _ _ _ bounded
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
