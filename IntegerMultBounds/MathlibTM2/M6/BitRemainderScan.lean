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
    {count src dst saved tmp : Fin T} (layout : [count,src,dst,saved,tmp].Nodup)
    (word : Fin N → ZMod 2) (u : HS T Q prime U) (S : Stacks T prime)
    (done : RecordPayload src (fun _ => blank) 0 word S) (width : (S.R count).length = N)
    (hs : S.R saved = []) (ht : S.R tmp = []) :
    let bits := payloadWord (SparseRoleCircuit.encode ∘ word)
    let F := {S with R := Function.update (Function.update S.R src ((S.R src).drop N)) dst (bits ++ S.R dst)}
    ∃ z, z.user = u.user ∧ Exec body (movePrefix count src dst saved tmp) (mk u S) (6*N+6) (mk z F) ∧
      ∀ j, readAt blank (F.L src) (F.R src) j = blank := by
  intro bits F
  have front :=  payload_prefix_of_read word _ _ _ _ done
  have len : bits.length = N := by simp [bits,payloadWord]
  obtain ⟨z,user,run⟩ := movePrefix_exec (body := body) layout bits _ u S front (width.trans len.symm) hs ht
  refine ⟨z,user,by simpa only [len] using run,?_⟩
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
    (elapsed : ℝ) + records*(2*(6*(N : ℝ)+6)) ≤ overhead + 2 +
      (ordinary+24+((degree : ℝ)/prime)*rate)*volume prime v/142080 := by
  intro records N degree positive base scan
  have size : ((records : ℝ)*N)*142080 = volume prime v := by
    exact_mod_cast remainderRecord_volume v w rows e he width split
  have one : (1 : ℝ) ≤ N := by exact_mod_cast positive
  have io : 2*(6*(N : ℝ)+6) ≤ 24*N := by linarith
  calc
    _ ≤ overhead + records*(ordinary*N) + 2 + ((degree : ℝ)/prime)*rate*(records*N) + records*(24*N) := by
      grw [scan,base,io]
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
