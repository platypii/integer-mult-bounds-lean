module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOutputCrop
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderReturnTranspose
import IntegerMultBounds.MathlibTM2.Host.ChunkSwap

/-! Load the compact crop result as an exact stack word, preserving the source tape. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host Cover.Fallback
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

private theorem markedPayload {V : ℕ} (x : Fin V → ZMod 2) (L R : List (Fin (prime+4)))
    (ready : WordAtZero x L R) :
    ∀ z, readAt blank (separator::L) R (z-1) =
      RadixZeroFill.encodedBinary (List.ofFn (fun i => decide (x i = 1))) z := by
  intro z
  rw [encodedBinary_eq,← readAt_single,List.map_ofFn]
  have same (p : ℤ) : readAt blank L R p =
      readAt blank [] (List.ofFn fun i => SparseRoleCircuit.encode (x i)) p := by
    rw [ready,putWord_blank_zero,readAt_nil_left]
  rcases int_cases (z-1) with ⟨k,h⟩ | ⟨k,h⟩
  · rw [h,readAt_nonneg,readAt_nonneg]
    exact same k
  · rw [h,readAt_neg,readAt_neg]
    cases k with
    | zero => rfl
    | succ k => simpa only [readAt_neg,List.getElem?_cons_succ] using same (-((k+1 : ℕ) : ℤ))

def loadCompactWord {T Q A : ℕ} {P U : Type} (src tmp dst : Fin T) : Pr P T Q A U :=
  .seq (.act (.push (.lt src) (fun _ => separator) .done))
    ((copyDescriptor src tmp dst).seq (.act (.pop (.lt src) (fun u _ => u) .done)))

theorem loadCompactWord_exec {T Q V : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (src tmp dst : Fin T) (apart : [src,tmp,dst].Nodup) (x : Fin V → ZMod 2)
    (u : HS T Q prime U) (S : Stacks T prime) (ready : WordAtZero x (S.L src) (S.R src))
    (left : S.L tmp = []) (right : S.R tmp = []) :
    ∃ v, v.user = u.user ∧ Exec body (loadCompactWord src tmp dst) (mk u S) (8*V+10)
      (mk v {S with R := Function.update S.R dst ((List.ofFn fun i => SparseRoleCircuit.encode (x i))++S.R dst)}) := by
  let D := {S with L := Function.update S.L src (separator::S.L src)}
  have ne : tmp ≠ src := by intro eq; subst tmp; simp at apart
  have mark : Exec body (.act (.push (.lt src) (fun _ => separator) .done)) (mk u S) 1 (mk u D) := by
    apply (Exec.act _ _).cast rfl
    simp [Action.run,D,get_lt,update_lt]
  obtain ⟨v,same,run⟩ := copyDescriptor_exec body apart (List.ofFn fun i => decide (x i = 1)) u D
    (by simpa [D] using markedPayload x _ _ ready) (by simp [D,Function.update_of_ne ne,left]) right
  refine ⟨v,same,(Exec.seq mark (Exec.seq run (Exec.act _ _))).cast ?_ ?_⟩
  · simp; omega
  · simp only [Action.run,mk_var,mk_stk,get_lt,update_lt,List.map_ofFn]
    simp [D,Function.update_idem,Function.comp_def,SparseRoleCircuit.encode]

/-- Load and transpose every record on the source tape, preserving its contents. -/
theorem returnRecordTape_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (bank : Fin 8 ↪ Fin T) (src : Fin T) (apart : ∀ i, src ≠ bank i) :
    ∃ code, ∀ (A B K : ℕ), 0 < B → 0 < K →
      ∀ (x : Fin (B*(A*K)) → ZMod 2) (u : HS T Q prime U) (S : Stacks T prime)
        (record rowWidth : List (Fin (prime+4))),
      WordAtZero x (S.L src) (S.R src) → record.length = K → S.L (bank 1) = [] →
      embStk bank S = transposeStacks (embStk bank S) [] [] (List.replicate A record.reverse).flatten record rowWidth →
      ∃ v F t, Exec body code (mk u S) t (mk v F) ∧ t ≤ 8*(B*(A*K))+10 + (A*(compactPassCost B K A+2)+2) ∧ v.user = u.user ∧
        embStk bank F = transposeStacks (embStk bank S) []
          (List.ofFn (fun i => SparseRoleCircuit.encode (compactTranspose x i))) [] record rowWidth ∧
        ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  let loopCode : Pr Empty 8 Q prime U := .seq (.act (peekR 3)) returnTransposeLoop
  refine ⟨.seq (loadCompactWord src (bank 1) (bank 0)) (embProg bank Empty.elim loopCode),?_⟩
  intro A B K hb hk x u S record rowWidth word width tmp prepared
  have atPort (i) := congrArg (fun D : Stacks 8 prime => D.R i) prepared
  have empty : S.R (bank 0) = [] := atPort 0
  have scratch : S.R (bank 1) = [] := atPort 1
  have sep : [src,bank 1,bank 0].Nodup := by simp [List.nodup_cons,apart,bank.injective.eq_iff]
  obtain ⟨v,user,load⟩ := loadCompactWord_exec body _ _ _ sep x u S word tmp scratch
  rw [empty,List.append_nil] at load
  let X := fun i => SparseRoleCircuit.encode (a := prime) (x i)
  let D := {S with R := Function.update S.R (bank 0) (List.ofFn X)}
  obtain ⟨z,t,same,run,time⟩ := returnRecordBlocks_exec (P := Empty) (U := U) Empty.elim A B K hb hk X
    (embStk bank S) (embDn bank v) record rowWidth width
  have start : embStk bank D = transposeStacks (embStk bank S) (List.ofFn X) []
      (List.replicate A record.reverse).flatten record rowWidth := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    fin_cases i <;> first | exact Function.update_self .. |
      (change Function.update S.R (bank 0) _ (bank _) = _; rw [Function.update_of_ne (bank.injective.ne (by decide))]; exact atPort _)
  obtain ⟨v',F,placed,_,keep,view,off⟩ := exec_emb (ι := (Empty.elim : Empty → P)) (body' := body)
    bank.injective (fun e => nomatch e) run v rfl D start
  refine ⟨v',F,_,Exec.seq load placed,Nat.add_le_add_left time _,keep.trans (same.trans user),view,?_⟩
  intro j h
  exact ⟨(off j h).1,(off j h).2.trans (Function.update_of_ne (h 0).symm ..)⟩

/-- Return every scanner row to parent order. Coordinates precede the
parent and label indices, and each trailing record stays contiguous. -/
theorem returnLabeledRows_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (bank : Fin 8 ↪ Fin T) (src : Fin T) (apart : ∀ i, src ≠ bank i) :
    ∃ code, ∀ (M B N K : ℕ), 0 < B*N → 0 < K →
      let A := M^128
      ∀ (x : Fin ((B*N)*(A*K)) → ZMod 2) (u : HS T Q prime U) (S : Stacks T prime)
        (record rowWidth : List (Fin (prime+4))),
      WordAtZero x (S.L src) (S.R src) → record.length = K → S.L (bank 1) = [] →
      embStk bank S = transposeStacks (embStk bank S) [] [] (List.replicate A record.reverse).flatten record rowWidth →
      ∃ z F steps, ∃ y : Fin (A*((B*N)*K)) → ZMod 2, Exec body code (mk u S) steps (mk z F) ∧
        steps ≤ 8*((B*N)*(A*K))+10 + (A*(compactPassCost (B*N) K A+2)+2) ∧ z.user = u.user ∧
        F.L (bank 6) = S.L (bank 6) ∧ F.R (bank 6) = List.ofFn (fun j => SparseRoleCircuit.encode (y j)) ∧
        (∀ a (b : Fin B) (g : Fin N) k, y (finProdFinEquiv (a,finProdFinEquiv (finProdFinEquiv (b,g),k))) =
          x (finProdFinEquiv (finProdFinEquiv (b,g),finProdFinEquiv (a,k)))) ∧
        ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨code,run⟩ := returnRecordTape_exec body bank src apart
  refine ⟨code,?_⟩
  intro M B N K rows width A x u S record rowWidth word length scratch registers
  obtain ⟨z,F,steps,exec,bill,user,view,off⟩ := run A (B*N) K rows width x u S record rowWidth word length scratch registers
  refine ⟨z,F,steps,compactTranspose x,exec,bill,user,congrArg (fun D : Stacks 8 prime => D.L 6) view,
    congrArg (fun D : Stacks 8 prime => D.R 6) view,?_,off⟩
  intro a b g k
  simp only [compactTranspose,Equiv.symm_apply_apply]

/-- Read a crop tape on the enclosing host and restore staging order. -/
theorem returnCompactTape_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (bank : Fin 8 ↪ Fin T) (src : Fin T) (apart : ∀ i, src ≠ bank i) :
    ∃ code, ∀ (w B K : ℕ), 0 < B → 0 < K →
      let A := (prime^w)^16
      let N := prime^(64*(w*64))
      ∀ (x : Fin (B*(A*K)) → ZMod 2) (u : HS T Q prime U) (S : Stacks T prime)
        (record rowWidth : List (Fin (prime+4))),
      WordAtZero x (S.L src) (S.R src) → record.length = K → S.L (bank 1) = [] →
      embStk bank S = transposeStacks (embStk bank S) [] [] (List.replicate A record.reverse).flatten record rowWidth →
      ∃ v F t, Exec body code (mk u S) t (mk v F) ∧ t ≤ 60*(A*(B*N*K))+12 ∧ v.user = u.user ∧
        embStk bank F = transposeStacks (embStk bank S) []
          (List.ofFn (fun i => SparseRoleCircuit.encode (compactTranspose x i))) [] record rowWidth ∧
        ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨code,run⟩ := returnRecordTape_exec body bank src apart
  refine ⟨code,?_⟩
  intro w B K hb hk A N x u S record rowWidth word width tmp prepared
  obtain ⟨v,F,t,exec,paid,user,out,off⟩ := run A B K hb hk x u S record rowWidth word width tmp prepared
  have volume : B*(A*K) ≤ A*(B*N*K) := by
    have pos : 0 < N := pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _
    calc
      _ = A*(B*K) := by ring
      _ ≤ _ := Nat.mul_le_mul_left A (Nat.mul_le_mul_right K (Nat.le_mul_of_pos_right B pos))
  have scans := compactTranspose_volume_bound w B K hb hk
  change A*(compactPassCost B K A+2)+2 ≤ 52*(A*(B*N*K))+2 at scans
  exact ⟨v,F,t,exec,by omega,user,out,off⟩

/-- Split the ordinary row's 128 coordinates into the 16 active and 112
spectator coordinates before running the return transpose. -/
theorem ordinaryCompact_width (M W : ℕ) : M^16*(M^112*W) = M^128*W := by
  rw [← Nat.mul_assoc,← pow_add]

def ordinaryCompactView {M B W : ℕ} (x : Fin (B*1*(M^128*W)) → ZMod 2) :
    Fin (B*(M^16*(M^112*W))) → ZMod 2 :=
  fun j => x (j.cast (by rw [ordinaryCompact_width,Nat.mul_one]))

theorem ordinaryCompactView_tape {M B W : ℕ} (x : Fin (B*1*(M^128*W)) → ZMod 2)
    {L R} (live : WordAtZero x L R) : WordAtZero (ordinaryCompactView x) L R := by
  have castWord {m n : ℕ} (h : m = n) (f : Fin n → Fin (prime+4)) :
      List.ofFn (fun j => f (j.cast h)) = List.ofFn f := by subst n; rfl
  intro z
  rw [live,show (List.ofFn fun i => SparseRoleCircuit.encode (a := prime) (ordinaryCompactView x i)) =
    List.ofFn (fun i => SparseRoleCircuit.encode (x i)) from castWord (show B*(M^16*(M^112*W)) = B*1*(M^128*W) by rw [ordinaryCompact_width,Nat.mul_one]) (fun i => SparseRoleCircuit.encode (x i))]

theorem ordinaryCompactView_cell {M B W : ℕ} (x : Fin (B*1*(M^128*W)) → ZMod 2)
    (a : Fin (M^16)) (b : Fin B) (k : Fin (M^112*W)) :
    compactTranspose (ordinaryCompactView x) (finProdFinEquiv (a,finProdFinEquiv (b,k))) =
      x (finProdFinEquiv (finProdFinEquiv (b,(0 : Fin 1)),(finProdFinEquiv (a,k)).cast (ordinaryCompact_width M W))) := by
  simp only [compactTranspose,Equiv.symm_apply_apply,ordinaryCompactView]
  apply congrArg x
  apply Fin.ext
  simp only [Fin.val_cast,finProdFinEquiv_apply_val,Fin.val_zero,Nat.one_mul,Nat.zero_add,ordinaryCompact_width]

end IntegerMultBounds.MathlibTM2.M6.BitNode
