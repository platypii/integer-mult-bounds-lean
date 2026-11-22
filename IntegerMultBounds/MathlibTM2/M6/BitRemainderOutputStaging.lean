module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderCompactRead

/-! The ordinary scanner's identity row is returned to staging order on the host. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host Cover
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _).ne'⟩

theorem ordinaryOutputStaging_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (fits : 235 ≤ Q) (bank : Fin 14 ↪ Fin T) (headers : Fin 4 → Fin T)
    (apart : ∀ i j, headers i ≠ bank j) (port : Fin 12 ↪ Fin T)
    (shared : port 0 = bank 11) (privatePorts : ∀ j, j ≠ 0 → ∀ i, bank i ≠ port j)
    (trans : Fin 8 ↪ Fin T) (separate : ∀ j, (∀ i, bank i ≠ trans j) ∧ (∀ i, port i ≠ trans j)) :
    ∃ code, ∀ {w B W : ℕ} {interval parent c}, 0 < B → 0 < W →
      let M := prime^(w+1)
      let N := M^(64*64)
      let K := M^128*W
      let idRow := LabelAddress.address (1 : LabelPadding.Label 64 (w+1))
      ∀ (input output : Fin ((B*N)*K) → ZMod 2),
      OriginalPortReads _ W B interval parent c input output → c.Checked → (∀ i, IsUnit (parent i)) →
      (∀ b j k, j ≠ idRow → input (finProdFinEquiv (finProdFinEquiv (b,j),k)) = 0) →
      ∀ u S, (∀ i z, readAt blank (S.L (headers i)) (S.R (headers i)) (z-1) =
        RadixZeroFill.encodedBinary (bits (![K,N,(0-idRow).val,B] i)) z) →
      (∀ j : Fin 14, j ≠ 10 → j ≠ 11 → S.L (bank j) = [] ∧ S.R (bank j) = []) →
      WordAtZero output (S.L (bank 10)) (S.R (bank 10)) →
      (∀ z, readAt blank (S.L (bank 11)) (S.R (bank 11)) z = blank) →
      CropCounters port B N K S →
      (∀ z, readAt blank (S.L (port 1)) (S.R (port 1)) z = blank) →
      ∀ (record rowWidth : List (Fin (prime+4))), record.length = M^112*W → S.L (trans 1) = [] →
      (∀ i, S.R (trans i) = (transposeStacks (embStk trans S) [] []
        (List.replicate (M^16) record.reverse).flatten record rowWidth).R i) →
      ∃ v F t, ∃ staged : Fin (M^16*(B*(M^112*W))) → ZMod 2, Exec body code (mk u S) t (mk v F) ∧ t ≤ 15923*(B*(N*K))+577 ∧ v.user = u.user ∧
        F.L (trans 6) = S.L (trans 6) ∧ F.R (trans 6) = List.ofFn (fun j => SparseRoleCircuit.encode (staged j)) ∧
        (∀ (a : Fin (M^16)) (b : Fin B) (k : Fin (M^112*W)),
          staged (finProdFinEquiv (a,finProdFinEquiv (b,k))) = output (finProdFinEquiv
            (finProdFinEquiv (b,idRow),(finProdFinEquiv (a,k)).cast (ordinaryCompact_width M W)))) ∧
        ∀ j, (∀ i, bank i ≠ j) → (∀ i, port i ≠ j) → (∀ i, trans i ≠ j) →
          F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨crop,run⟩ := ordinaryOutputCrop_exec body fits bank headers apart port shared privatePorts
  obtain ⟨back,restore⟩ := returnCompactTape_exec body trans (port 1) (fun j => (separate j).2 1)
  refine ⟨crop.seq back,?_⟩
  intro w B W interval parent c hb hw M N K idRow input output reads checked units support u S words free src dest counters blankDest record rowWidth width tmp regs
  obtain ⟨v,D,t,compact,cut,time,user,_,word,row,_,off⟩ := run hb hw input output reads checked units support u S words free src dest counters blankDest
  have keep i := off _ (separate i).1 (separate i).2
  have hk : 0 < M^112*W := Nat.mul_pos (pow_pos (pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _) _) hw
  obtain ⟨z,F,k,returned,cost,same,view,outside⟩ := restore (w+1) B (M^112*W) hb hk (ordinaryCompactView compact)
    v D record rowWidth (ordinaryCompactView_tape compact word) width ((keep 1).1.trans tmp) (by
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      exact (keep i).2.trans (regs i))
  have labels : prime^(64*((w+1)*64)) = N := by
    change _ = (prime^(w+1))^(64*64)
    rw [← pow_mul]; congr 1; omega
  have volume : M^16*(B*N*(M^112*W)) = B*(N*K) := by
    change _ = B*(N*(M^128*W))
    rw [← ordinaryCompact_width]
    ring
  change k ≤ 60*(M^16*(B*prime^(64*((w+1)*64))*(M^112*W)))+12 at cost
  rw [labels,volume] at cost
  change t ≤ 15863*(B*(N*K))+565 at time
  refine ⟨z,F,_,compactTranspose (ordinaryCompactView compact),Exec.seq cut returned,by omega,same.trans user,?_,?_,?_,?_⟩
  · exact (congrArg (fun D : Stacks 8 prime => D.L 6) view).trans (keep 6).1
  · exact congrArg (fun D : Stacks 8 prime => D.R 6) view
  · intro a b k
    exact (ordinaryCompactView_cell compact a b k).trans (row b _)
  · intro j hb hp ht
    exact ⟨(outside j ht).1.trans (off j hb hp).1,(outside j ht).2.trans (off j hb hp).2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
