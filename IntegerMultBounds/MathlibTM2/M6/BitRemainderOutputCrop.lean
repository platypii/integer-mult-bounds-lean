module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOutputRotation

/-! Crop the returned ordinary result on the owner's host tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host Cover
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits bits_value bits_canonical)

def CropCounters {T : ℕ} (port : Fin 12 ↪ Fin T) (B N K : ℕ) (S : Stacks T prime) : Prop :=
  ∀ j : Fin 12, j ≠ 0 → j ≠ 1 → ∀ z, (ownerPadFrame B N K).tape j z =
    readAt blank (S.L (port j)) (S.R (port j)) (z-(ownerPadFrame B N K).head j)

theorem padFrame_aux (B N K : ℕ) (f g : ℤ → Fin (prime+4)) (j : Fin 12) (hs : j ≠ 0) (hd : j ≠ 1) :
      let frame := RowPaddingConstructedAlphabet.bank f g 0 0 (bits B) (bits 1) (bits N) (bits K)
      frame.tape j = (ownerPadFrame B N K).tape j ∧ frame.head j = (ownerPadFrame B N K).head j := by
  fin_cases j <;> first | contradiction | exact ⟨rfl,rfl⟩

theorem placedOrdinaryCrop_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (fits : 215 ≤ Q) (port : Fin 12 ↪ Fin T) {B N K : ℕ}
    (hb : 0 < B) (hn : 0 < N) (hk : 0 < K) (x : Fin ((B*N)*K) → ZMod 2)
    (u : HS T Q prime U) (S : Stacks T prime) (source : WordAtZero x (S.L (port 0)) (S.R (port 0)))
    (dest : ∀ z, readAt blank (S.L (port 1)) (S.R (port 1)) z = blank)
    (ready : CropCounters port B N K S) :
    ∃ v F t, Exec body (embProg port (Empty.elim : Empty → P)
      (foreign (liftQ RowPaddingConstructedAlphabet.cropProgram fits))) (mk u S) t (mk v F) ∧
      t ≤ 7021*(B*(N*K))+6 ∧ v.user = u.user ∧
      WordAtZero (RecursiveRowPadding.crop (R := 1) hn x) (F.L (port 1)) (F.R (port 1)) ∧
      CropCounters port B N K F ∧ ∀ j, (∀ i, port i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  have crop := RowPaddingConstructedAlphabet.crop_bits_hoare (a := prime) (fun _ => blank) (fun _ => blank)
    0 0 _ _ _ _ B 1 N K (fun j => decide (x j = 1)) (bits_value _) (bits_value _) (bits_value _)
    (bits_value _) (bits_canonical _) (bits_canonical _) (bits_canonical _) (bits_canonical _)
    hb Nat.zero_lt_one hn hk
  obtain ⟨v,F,t,exec,time,user,done,off⟩ := placedHoare_exec _ port fits body crop u S (by
    intro j z
    by_cases hs : j = 0
    · subst j; exact (source z).symm.trans (congrArg (readAt blank (S.L (port 0)) (S.R (port 0))) (sub_zero z).symm)
    by_cases hd : j = 1
    · subst j; exact (dest z).symm.trans (congrArg (readAt blank (S.L (port 1)) (S.R (port 1))) (sub_zero z).symm)
    rw [(padFrame_aux B N K _ _ j hs hd).1,(padFrame_aux B N K _ _ j hs hd).2]
    exact ready j hs hd z)
  refine ⟨v,F,t,exec,time.trans_eq (by ring),user,?_,?_,off⟩
  · intro z
    have h := (done 1 z).symm
    change readAt blank (F.L (port 1)) (F.R (port 1)) (z-0) =
      putWord (fun _ => blank) 0 (List.ofFn (RecursiveRowPadding.crop (A := B) (R := 1) (L := K) hn
        (fun i => SparseRoleCircuit.encode (a := prime) (x i)))) z at h
    rw [sub_zero] at h
    exact h
  · intro j hs hd z
    have h := done j z
    rw [(padFrame_aux B N K _ _ j hs hd).1,(padFrame_aux B N K _ _ j hs hd).2] at h
    exact h

local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- The rotation destination is the crop source. Both machines execute on
the enclosing host, and the crop counters survive for the next owner. -/
theorem ordinaryOutputCrop_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (fits : 235 ≤ Q) (bank : Fin 14 ↪ Fin T) (headers : Fin 4 → Fin T)
    (apart : ∀ i j, headers i ≠ bank j) (port : Fin 12 ↪ Fin T)
    (shared : port 0 = bank 11) (privatePorts : ∀ j, j ≠ 0 → ∀ i, bank i ≠ port j) :
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
      ∃ v F t compact, Exec body code (mk u S) t (mk v F) ∧ t ≤ 15863*(B*(N*K))+565 ∧
        v.user = u.user ∧ WordAtZero output (F.L (bank 10)) (F.R (bank 10)) ∧
        WordAtZero compact (F.L (port 1)) (F.R (port 1)) ∧
        (∀ b (k : Fin K), compact (finProdFinEquiv (finProdFinEquiv (b,(0 : Fin 1)),k)) =
          output (finProdFinEquiv (finProdFinEquiv (b,idRow),k))) ∧
        CropCounters port B N K F ∧
        ∀ j, (∀ i, bank i ≠ j) → (∀ i, port i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨rotate,run⟩ := ordinaryOutputRotation_exec body fits bank headers apart
  let crop : Pr P T Q prime U := embProg port (Empty.elim : Empty → P) (foreign (liftQ RowPaddingConstructedAlphabet.cropProgram
    (by omega : 215 ≤ Q)))
  refine ⟨rotate.seq crop,?_⟩
  intro w B W interval parent c hb hw M N K idRow input output reads checked units support u S words free src dest counters blankDest
  obtain ⟨v,D,t,padded,rot,time,user,kept,result,row,off⟩ := run hb hw input output reads checked units support
    u S words free src dest
  have hk : 0 < K := Nat.mul_pos (pow_pos (pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _) _) hw
  have preserved j (hj : j ≠ 0) := off _ (privatePorts j hj)
  obtain ⟨z,F,k,cut,cost,same,word,ready,frame⟩ := placedOrdinaryCrop_exec body (by omega) port hb (NeZero.pos N) hk padded v D
    (shared ▸ result) (by rw [(preserved 1 (by decide)).1,(preserved 1 (by decide)).2]; exact blankDest)
    (fun j hs hd l => by rw [(preserved j hs).1,(preserved j hs).2]; exact counters j hs hd l)
  have outside : ∀ j, port j ≠ bank 10 := by
    intro j; by_cases h : j = 0
    · subst j; rw [shared]; exact bank.injective.ne (by decide)
    · exact (privatePorts j h 10).symm
  have source := frame _ outside
  change t ≤ 8842*(B*(N*K))+559 at time
  refine ⟨z,F,_,_,Exec.seq rot cut,by omega,same.trans user,?_,word,row,ready,?_⟩
  · rw [source.1,source.2]; exact kept
  · intro j hj hp
    exact ⟨(frame j hp).1.trans (off j hj).1,(frame j hp).2.trans (off j hj).2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
