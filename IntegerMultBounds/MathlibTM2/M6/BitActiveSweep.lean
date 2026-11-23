module

public import IntegerMultBounds.MathlibTM2.M6.BitWorkerDispatch
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderCompactRead

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover.Fallback Stack Host
open RecursiveInterchangeLayout M8.RevMachine
open Shared50ModularControl (prime)
open Certificates.PR589
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

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
  have read : WordAtZero word (S.L (bank 24)) (S.R (bank 24)) := by
    intro j
    rw [← encodedOwnerCell]
    simpa only [sub_zero,List.map_ofFn] using ready.src j
  simpa only [fresh,List.append_nil] using loadCompactWord_exec body (bank 24) tmp dst apart word u S read left right

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
