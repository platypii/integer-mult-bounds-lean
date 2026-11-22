module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderInputStaging

/-! Pad the ordinary block sequence and rotate it directly onto the scanner's live identity row. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host Cover
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _).ne'⟩

theorem ordinaryInputRotation_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (fits : 235 ≤ Q) (pad : Fin 12 ↪ Fin T) (bank : Fin 14 ↪ Fin T) (headers : Fin 4 → Fin T)
    (apart : ∀ i j, headers i ≠ bank j) (saved : ∀ i j, pad j ≠ headers i)
    (shared : bank 10 = pad 1) (privateBank : ∀ i, i ≠ 10 → ∀ j, pad j ≠ bank i) :
    ∃ code, ∀ w B K, 0 < B → 0 < K →
      let A := (prime^w)^16
      let N := prime^(64*(w*64))
      let g := ordinaryIdentityRow w
      ∀ (x : Fin 142081 → Fin (A*(B*K)) → ZMod 2) i u S,
      WordAtZero (compactTranspose (x i)) (S.L (pad 0)) (S.R (pad 0)) →
      (∀ z, readAt blank (S.L (pad 1)) (S.R (pad 1)) z = blank) →
      CropCounters pad B N (A*K) S →
      (∀ j z, readAt blank (S.L (headers j)) (S.R (headers j)) (z-1) =
        RadixZeroFill.encodedBinary (bits (![A*K,N,g.val,B] j)) z) →
      (∀ j : Fin 14, j ≠ 10 → j ≠ 11 → S.L (bank j) = [] ∧ S.R (bank j) = []) →
      (∀ z, readAt blank (S.L (bank 11)) (S.R (bank 11)) z = blank) →
      ∃ v F t, Exec body code (mk u S) t (mk v F) ∧ t ≤ 15863*(B*(N*(A*K)))+565 ∧
        v.user = u.user ∧ WordAtZero (fun j => singleLabelBank (firstRowLabel w) x i
          ((ordinaryRowLayout (Equiv.swap 0 g)).symm j)) (F.L (bank 11)) (F.R (bank 11)) ∧
        ∀ j, (∀ i, pad i ≠ j) → (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨rotate,run⟩ := placedRotation_exec body fits bank headers apart
  let padding : Pr P T Q prime U := embProg pad Empty.elim (foreign (liftQ RowPaddingConstructedAlphabet.program (by omega : 215 ≤ Q)))
  refine ⟨padding.seq rotate,?_⟩
  intro w B K hb hk A N g x i u S source dest ready words free empty
  have hw : 0 < A*K := Nat.mul_pos (pow_pos (pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _) _) hk
  let padded := RecursiveRowPadding.pad (A := B) (R := 1) (L := A*K) N 0
    (fun j => compactTranspose (x i) (j.cast (by simp)))
  have padRun := compactTranspose_pad_hoare hb hw (NeZero.pos N) (x i)
  obtain ⟨v,D,t,exec,cost,user,done,off⟩ := placedHoare_exec _ pad (by omega : 215 ≤ Q) body padRun u S (by
    intro j z
    by_cases hs : j = 0
    · subst j; exact (source z).symm.trans (congrArg (readAt blank (S.L _) (S.R _)) (sub_zero z).symm)
    by_cases hd : j = 1
    · subst j; exact (dest z).symm.trans (congrArg (readAt blank (S.L _) (S.R _)) (sub_zero z).symm)
    rw [(padFrame_aux B N (A*K) _ _ j hs hd).1,(padFrame_aux B N (A*K) _ _ j hs hd).2]
    exact ready j hs hd z)
  have payload : WordAtZero padded (D.L (bank 10)) (D.R (bank 10)) := by
    rw [shared]
    intro z
    have h := (done 1 z).symm
    change readAt blank (D.L (pad 1)) (D.R (pad 1)) (z-0) = _ at h
    rw [sub_zero] at h
    exact h
  let row := fun b k => compactTranspose (x i) (finProdFinEquiv (b,k))
  let owner := fun j => singleLabelBank (firstRowLabel w) x i ((ordinaryRowLayout (Equiv.swap 0 g)).symm j)
  have keep j (h : j ≠ 10) := off _ (privateBank j h)
  obtain ⟨z,F,k,rot,time,same,_,out,frame⟩ := run hb hw 0 g row padded owner (by
    intro b j k
    obtain ⟨⟨a,k⟩,rfl⟩ := finProdFinEquiv.surjective k
    simpa only [padded,row,compactTranspose,Equiv.symm_apply_apply,Fin.ext_iff,Fin.val_zero] using
      compactTranspose_pad (N := N) 0 (x i) b j a k) (by
    intro b j k
    obtain ⟨⟨a,k⟩,rfl⟩ := finProdFinEquiv.surjective k
    simpa only [owner,g,row,compactTranspose,Equiv.symm_apply_apply] using ordinaryIdentityRow_payload x i a b j k)
    v D (fun j z => by rw [(off _ (saved j)).1,(off _ (saved j)).2,sub_zero]; exact words j z)
    (fun j hs hd => by rw [(keep j hs).1,(keep j hs).2]; exact free j hs hd)
    payload (fun z => by rw [(keep 11 (by decide)).1,(keep 11 (by decide)).2]; exact empty z)
  change t ≤ (413*B*(N*(A*K)))*17+6 at cost
  rw [show 413*B*(N*(A*K))*17 = 7021*(B*(N*(A*K))) by ring] at cost
  change k ≤ 8842*(B*(N*(A*K)))+559 at time
  refine ⟨z,F,_,Exec.seq exec rot,by omega,same.trans user,out,?_⟩
  intro j hp hr
  exact ⟨(frame j hr).1.trans (off j hp).1,(frame j hr).2.trans (off j hp).2⟩

/-- A single host program carries the padded staging owner onto the identity
row, preserving the order of the spectators in every inherited block. -/
theorem stagingToIdentity_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (crop : Fin 12 ↪ Fin T) (trans : Fin 8 ↪ Fin T) (distinct : ∀ i j, crop i ≠ trans j)
    (fits : 235 ≤ Q) (pad : Fin 12 ↪ Fin T) (bank : Fin 14 ↪ Fin T) (headers : Fin 4 → Fin T)
    (apart : ∀ i j, headers i ≠ bank j) (saved : ∀ i j, pad j ≠ headers i)
    (shared : bank 10 = pad 1) (privateBank : ∀ i, i ≠ 10 → ∀ j, pad j ≠ bank i)
    (port : pad 0 = trans 0)
    (sparePad : ∀ j, j ≠ 0 → (∀ i, crop i ≠ pad j) ∧ (∀ i, trans i ≠ pad j))
    (spareBank : ∀ j, j ≠ 10 → (∀ i, crop i ≠ bank j) ∧ (∀ i, trans i ≠ bank j))
    (spareHeaders : ∀ j, (∀ i, crop i ≠ headers j) ∧ (∀ i, trans i ≠ headers j)) :
    ∃ code, ∀ w B K, 0 < B → 0 < K →
      let A := (prime^w)^16
      let N := prime^(64*(w*64))
      let g := ordinaryIdentityRow w
      ∀ (x : Fin 142081 → Fin (A*(B*K)) → ZMod 2) i u S,
      WordAtZero (singleLabelBank (firstRowLabel w) x i) (S.L (crop 0)) (S.R (crop 0)) →
      (∀ z, readAt blank (S.L (crop 1)) (S.R (crop 1)) z = blank) → CropCounters crop (A*B) N K S →
      ∀ (record rowWidth : List (Fin (prime+4))), record.length = K → rowWidth.length = B*K →
      S.L (trans 0) = [] → S.L (trans 1) = [] →
      (∀ j, S.R (trans j) = (transposeStacks (embStk trans S) [] [] [] record rowWidth).R j) →
      (∀ z, readAt blank (S.L (pad 1)) (S.R (pad 1)) z = blank) →
      CropCounters pad B N (A*K) S →
      (∀ j z, readAt blank (S.L (headers j)) (S.R (headers j)) (z-1) =
        RadixZeroFill.encodedBinary (bits (![A*K,N,g.val,B] j)) z) →
      (∀ j : Fin 14, j ≠ 10 → j ≠ 11 → S.L (bank j) = [] ∧ S.R (bank j) = []) →
      (∀ z, readAt blank (S.L (bank 11)) (S.R (bank 11)) z = blank) →
      ∃ v F t, Exec body code (mk u S) t (mk v F) ∧ t ≤ 22944*(A*(B*N*K))+583 ∧
        v.user = u.user ∧ WordAtZero (fun j => singleLabelBank (firstRowLabel w) x i
          ((ordinaryRowLayout (Equiv.swap 0 g)).symm j)) (F.L (bank 11)) (F.R (bank 11)) ∧
        (∀ l, readAt blank (F.L (crop 0)) (F.R (crop 0)) l = blank) ∧
        ∀ j, (∀ i, crop i ≠ j) → (∀ i, trans i ≠ j) → (∀ i, pad i ≠ j) → (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨forward,stage⟩ := stagingInputTranspose_exec body (by omega) crop trans distinct
  obtain ⟨rotate,turn⟩ := ordinaryInputRotation_exec body fits pad bank headers apart saved shared privateBank
  refine ⟨forward.seq rotate,?_⟩
  intro w B K hb hk A N g x i u S source empty counters record rowWidth width rowLen left tmp regs padBlank padReady words free dest
  obtain ⟨v,D,t,cut,time,user,compact,head,_,erased,off⟩ := stage w B K hb hk x i u S record rowWidth source empty counters
    width rowLen tmp regs
  have keep j (hj : j ≠ 0) := off _ (sparePad j hj).1 (sparePad j hj).2
  have scratch j (hj : j ≠ 10) := off _ (spareBank j hj).1 (spareBank j hj).2
  have header j := off _ (spareHeaders j).1 (spareHeaders j).2
  obtain ⟨z,F,k,rot,paid,same,out,frame⟩ := turn w B K hb hk x i v D (by
    intro l
    rw [port,head,left,compact,readAt_nil_left,putWord_blank_zero])
    (by rw [(keep 1 (by decide)).1,(keep 1 (by decide)).2]; exact padBlank)
    (fun j hs hd l => by rw [(keep j hs).1,(keep j hs).2]; exact padReady j hs hd l)
    (fun j l => by rw [(header j).1,(header j).2]; exact words j l)
    (fun j hs hd => by rw [(scratch j hs).1,(scratch j hs).2]; exact free j hs hd)
    (by rw [(scratch 11 (by decide)).1,(scratch 11 (by decide)).2]; exact dest)
  change t ≤ 7081*(A*(B*N*K))+18 at time
  change k ≤ 15863*(B*(N*(A*K)))+565 at paid
  rw [show B*(N*(A*K)) = A*(B*N*K) by ring] at paid
  refine ⟨z,F,_,Exec.seq cut rot,by omega,same.trans user,out,?_,?_⟩
  · have hp (j) : pad j ≠ crop 0 := by
      by_cases h : j = 0
      · subst j; rw [port]; exact (distinct 0 0).symm
      · exact ((sparePad j h).1 0).symm
    have hr (j) : bank j ≠ crop 0 := by
      by_cases h : j = 10
      · subst j; rw [shared]; exact hp 1
      · exact ((spareBank j h).1 0).symm
    have unchanged := frame _ hp hr
    rw [unchanged.1,unchanged.2]; exact erased
  · intro j hc ht hp hr
    exact ⟨(frame j hp hr).1.trans (off j hc ht).1,(frame j hp hr).2.trans (off j hc ht).2⟩

/-- Reindexing the physical identity-row tape at scanner dimensions preserves
every cell and identifies the unique label which can contain data. -/
theorem identityScannerInput {w B W : ℕ} :
    let M := prime^w
    let A := M^16
    let K := M^112*W
    let g := ordinaryIdentityRow w
    ∀ (x : Fin 142081 → Fin (A*(B*K)) → ZMod 2) i L R,
      WordAtZero (fun j => singleLabelBank (firstRowLabel w) x i
        ((ordinaryRowLayout (Equiv.swap 0 g)).symm j)) L R →
      ∃ input : Fin ((B*M^(64*64))*(M^128*W)) → ZMod 2, WordAtZero input L R ∧
        ∀ b j a k, input (finProdFinEquiv (finProdFinEquiv (b,j),
          (finProdFinEquiv (a,k)).cast (ordinaryCompact_width M W))) =
          if j = LabelAddress.address (1 : LabelPadding.Label 64 w)
          then x i (finProdFinEquiv (a,finProdFinEquiv (b,k))) else 0 := by
  intro M A K g x i L R live
  let N := prime^(64*(w*64))
  have labels : M^(64*64) = N := by
    change (prime^w)^(64*64) = prime^(64*(w*64))
    rw [← pow_mul]; congr 1; omega
  have width := ordinaryCompact_width M W
  have size : B*M^(64*64)*(M^128*W) = B*N*(A*K) := by rw [labels,← width]
  let owner := fun j => singleLabelBank (firstRowLabel w) x i ((ordinaryRowLayout (Equiv.swap 0 g)).symm j)
  refine ⟨fun j => owner (j.cast size),?_,?_⟩
  · have pack {m n : ℕ} (h : m = n) (f : Fin n → Fin (prime+4)) :
        List.ofFn (fun i => f (i.cast h)) = List.ofFn f := by subst n; rfl
    intro z
    rw [pack size (fun i => SparseRoleCircuit.encode (owner i))]
    exact live z
  · intro b j a k
    have address : (finProdFinEquiv (finProdFinEquiv (b,j),(finProdFinEquiv (a,k)).cast width)).cast size =
        finProdFinEquiv (finProdFinEquiv (b,j.cast labels),finProdFinEquiv (a,k)) := by
      apply Fin.ext
      simp only [Fin.val_cast,finProdFinEquiv_apply_val,labels,width]
    change owner ((finProdFinEquiv (finProdFinEquiv (b,j),(finProdFinEquiv (a,k)).cast width)).cast size) = _
    rw [address]
    have cell := ordinaryIdentityRow_payload x i a b (j.cast labels) k
    simpa only [owner,g,ordinaryIdentityRow,Fin.ext_iff,Fin.val_cast] using cell

end IntegerMultBounds.MathlibTM2.M6.BitNode
