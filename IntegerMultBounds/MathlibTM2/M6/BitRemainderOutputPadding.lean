module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOutputStaging

/-! Restore the padded staging owner after an ordinary remainder scan. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host Cover
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _).ne'⟩

theorem ordinaryOutputPadded_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (fits : 235 ≤ Q) (bank : Fin 14 ↪ Fin T) (headers : Fin 4 → Fin T)
    (apart : ∀ i j, headers i ≠ bank j) (port : Fin 12 ↪ Fin T)
    (shared : port 0 = bank 11) (privatePorts : ∀ j, j ≠ 0 → ∀ i, bank i ≠ port j)
    (trans : Fin 8 ↪ Fin T) (separate : ∀ j, (∀ i, bank i ≠ trans j) ∧ (∀ i, port i ≠ trans j))
    (pad : Fin 12 ↪ Fin T) (readPort : pad 0 = trans 6)
    (privatePad : ∀ j, j ≠ 0 → (∀ i, bank i ≠ pad j) ∧ (∀ i, port i ≠ pad j) ∧ (∀ i, trans i ≠ pad j)) :
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
      S.L (trans 6) = [] →
      CropCounters pad (M^16*B) (prime^(64*((w+1)*64))) (M^112*W) S →
      (∀ z, readAt blank (S.L (pad 1)) (S.R (pad 1)) z = blank) →
      ∃ v F t, ∃ staged : Fin (M^16*(B*(M^112*W))) → ZMod 2, Exec body code (mk u S) t (mk v F) ∧ t ≤ 22944*(B*(N*K))+583 ∧ v.user = u.user ∧
        WordAtZero (singleLabelBank (firstRowLabel (w+1)) (fun _ => staged) 0) (F.L (pad 1)) (F.R (pad 1)) ∧
        (∀ (a : Fin (M^16)) (b : Fin B) (k : Fin (M^112*W)),
          staged (finProdFinEquiv (a,finProdFinEquiv (b,k))) = output (finProdFinEquiv
            (finProdFinEquiv (b,idRow),(finProdFinEquiv (a,k)).cast (ordinaryCompact_width M W)))) ∧
        ∀ j, (∀ i, bank i ≠ j) → (∀ i, port i ≠ j) → (∀ i, trans i ≠ j) → (∀ i, pad i ≠ j) →
          F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨staging,run⟩ := ordinaryOutputStaging_exec body fits bank headers apart port shared privatePorts trans separate
  let code : Pr P T Q prime U := embProg pad Empty.elim
    (foreign (liftQ RowPaddingConstructedAlphabet.program (by omega : 215 ≤ Q)))
  refine ⟨staging.seq code,?_⟩
  intro w B W interval parent c hb hw M N K idRow input output reads checked units support u S words free src dest counters blankDest record rowWidth width tmp regs left padCounters padBlank
  obtain ⟨v,D,t,staged,back,time,user,head,word,cells,off⟩ := run hb hw input output reads checked units support u S words free src dest counters blankDest record rowWidth width tmp regs
  have keep j (h : j ≠ 0) := off _ (privatePad j h).1 (privatePad j h).2.1 (privatePad j h).2.2
  have hk : 0 < M^112*W := Nat.mul_pos (pow_pos (pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _) _) hw
  obtain ⟨z,F,k,padded,cost,same,result,_,outside⟩ := placedOwnerPad (w := w+1) hb hk (by omega) body pad
    (fun _ => staged) 0 v D (by
      intro l
      rw [encodedOwnerCell,readPort,head,left,word,sub_zero,readAt_nil_left,putWord_blank_zero])
    (fun l => by rw [(keep 1 (by decide)).1,(keep 1 (by decide)).2]; exact padBlank l)
    (fun j hs hd l => by rw [(keep j hs).1,(keep j hs).2]; exact padCounters j hs hd l)
  have labels : prime^(64*((w+1)*64)) = N := by
    change _ = (prime^(w+1))^(64*64)
    rw [← pow_mul]; congr 1; omega
  change k ≤ 7021*(M^16*B)*(prime^(64*((w+1)*64))*(M^112*W))+6 at cost
  rw [labels,show 7021*(M^16*B)*(N*(M^112*W)) = 7021*(B*(N*K)) by
    change _ = 7021*(B*(N*(M^128*W))); rw [← ordinaryCompact_width]; ring] at cost
  change t ≤ 15923*(B*(N*K))+577 at time
  refine ⟨z,F,_,staged,Exec.seq back padded,by omega,same.trans user,?_,cells,?_⟩
  · intro l
    have read := result l
    rw [encodedOwnerCell,sub_zero] at read
    exact read
  · intro j hb hp ht hpad
    exact ⟨(outside j hpad).1.trans (off j hb hp ht).1,(outside j hpad).2.trans (off j hb hp ht).2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
