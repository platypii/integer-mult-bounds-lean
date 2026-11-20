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
