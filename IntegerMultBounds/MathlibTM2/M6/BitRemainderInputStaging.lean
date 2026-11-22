module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderCompactRead

/-! Crop the staging owner and place its compact transpose on the host. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host Cover
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)

/-- Read a crop tape on the enclosing host and enter ordinary block order. -/
theorem forwardCompactTape_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (bank : Fin 8 ↪ Fin T) (src : Fin T) (apart : ∀ i, src ≠ bank i) :
    ∃ code, ∀ (w B K : ℕ), 0 < B → 0 < K →
      let A := (prime^w)^16
      let N := prime^(64*(w*64))
      ∀ (x : Fin (A*(B*K)) → ZMod 2) (u : HS T Q prime U) (S : Stacks T prime)
        (record rowWidth : List (Fin (prime+4))),
      WordAtZero x (S.L src) (S.R src) → record.length = K → rowWidth.length = B*K → S.L (bank 1) = [] →
      embStk bank S = transposeStacks (embStk bank S) [] [] [] record rowWidth →
      ∃ v F t, Exec body code (mk u S) t (mk v F) ∧ t ≤ 60*(A*(B*N*K))+12 ∧ v.user = u.user ∧
        embStk bank F = transposeStacks (embStk bank S)
          (List.ofFn (fun i => SparseRoleCircuit.encode (compactTranspose x i))) [] (List.replicate A record.reverse).flatten record rowWidth ∧
        ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  let loopCode : Pr Empty 8 Q prime U := .seq (.act (peekR 6)) transposeLoop
  refine ⟨.seq (loadCompactWord src (bank 1) (bank 6)) (embProg bank Empty.elim loopCode),?_⟩
  intro w B K hb hk A N x u S record rowWidth word width rowLen tmp prepared
  have atPort (i) := congrArg (fun D : Stacks 8 prime => D.R i) prepared
  have empty : S.R (bank 6) = [] := atPort 6
  have scratch : S.R (bank 1) = [] := atPort 1
  have sep : [src,bank 1,bank 6].Nodup := by simp [List.nodup_cons,apart,bank.injective.eq_iff]
  obtain ⟨v,user,load⟩ := loadCompactWord_exec body _ _ _ sep x u S word tmp scratch
  rw [empty,List.append_nil] at load
  let X := fun i => SparseRoleCircuit.encode (a := prime) (x i)
  let D := {S with R := Function.update S.R (bank 6) (List.ofFn X)}
  obtain ⟨z,clock,t,clockEq,same,run,time⟩ := remainderCompactTranspose_exec (P := Empty) (U := U) Empty.elim w B K hb hk X
    (embStk bank S) (embDn bank v) record rowWidth width rowLen
  subst clock
  have start : embStk bank D = transposeStacks (embStk bank S) [] (List.ofFn X) [] record rowWidth := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    fin_cases i <;> first | exact Function.update_self .. |
      (change Function.update S.R (bank 6) _ (bank _) = _; rw [Function.update_of_ne (bank.injective.ne (by decide))]; exact atPort _)
  obtain ⟨v',F,placed,_,keep,view,off⟩ := exec_emb (ι := (Empty.elim : Empty → P)) (body' := body)
    bank.injective (fun e => nomatch e) run v rfl D start
  have volume : A*(B*K) ≤ A*(B*N*K) := by
    have pos : 0 < N := pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _
    exact Nat.mul_le_mul_left A (Nat.mul_le_mul_right K (Nat.le_mul_of_pos_right B pos))
  change t ≤ 52*(A*(B*N*K))+2 at time
  refine ⟨v',F,_,Exec.seq load placed,by omega,keep.trans (same.trans user),view,?_⟩
  intro j h
  exact ⟨(off j h).1,(off j h).2.trans (Function.update_of_ne (h 6).symm ..)⟩

/-- The staging crop writes the very tape from which the transpose loads.
Register 3 retains the full width clock for the eventual return pass. -/
theorem stagingInputTranspose_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (fits : 215 ≤ Q) (port : Fin 12 ↪ Fin T) (bank : Fin 8 ↪ Fin T)
    (apart : ∀ i j, port i ≠ bank j) :
    ∃ code, ∀ (w B K : ℕ), 0 < B → 0 < K →
      let A := (prime^w)^16
      let N := prime^(64*(w*64))
      ∀ (x : Fin 142081 → Fin (A*(B*K)) → ZMod 2) i (u : HS T Q prime U) S
        (record rowWidth : List (Fin (prime+4))),
      WordAtZero (singleLabelBank (firstRowLabel w) x i) (S.L (port 0)) (S.R (port 0)) →
      (∀ z, readAt blank (S.L (port 1)) (S.R (port 1)) z = blank) → CropCounters port (A*B) N K S →
      record.length = K → rowWidth.length = B*K → S.L (bank 1) = [] →
      (∀ j, S.R (bank j) = (transposeStacks (embStk bank S) [] [] [] record rowWidth).R j) →
      ∃ v F t, Exec body code (mk u S) t (mk v F) ∧ t ≤ 7081*(A*(B*N*K))+18 ∧ v.user = u.user ∧
        F.R (bank 0) = List.ofFn (fun j => SparseRoleCircuit.encode (compactTranspose (x i) j)) ∧
        F.L (bank 0) = S.L (bank 0) ∧ F.R (bank 3) = (List.replicate A record.reverse).flatten ∧
        ∀ j, (∀ i, port i ≠ j) → (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨forward,run⟩ := forwardCompactTape_exec body bank (port 1) (apart 1)
  let crop : Pr P T Q prime U := embProg port Empty.elim (foreign (liftQ RowPaddingConstructedAlphabet.cropProgram fits))
  refine ⟨crop.seq forward,?_⟩
  intro w B K hb hk A N x i u S record rowWidth source dest counters width rowLen scratch regs
  obtain ⟨v,D,t,cut,time,user,done,off⟩ := placedHoare_exec _ port fits body (singleLabelBank_crop_hoare hb hk x i) u S (by
    intro j z
    by_cases hs : j = 0
    · subst j
      exact (source z).symm.trans (congrArg (readAt blank (S.L (port 0)) (S.R (port 0))) (sub_zero z).symm)
    by_cases hd : j = 1
    · subst j
      exact (dest z).symm.trans (congrArg (readAt blank (S.L (port 1)) (S.R (port 1))) (sub_zero z).symm)
    rw [(padFrame_aux (A*B) N K _ _ j hs hd).1,(padFrame_aux (A*B) N K _ _ j hs hd).2]
    exact counters j hs hd z)
  have word : WordAtZero (x i) (D.L (port 1)) (D.R (port 1)) := by
    intro z
    have h := (done 1 z).symm
    change readAt blank (D.L (port 1)) (D.R (port 1)) (z-0) = _ at h
    rw [sub_zero] at h
    exact h
  have keep j := off _ (fun i => apart i j)
  obtain ⟨z,F,k,ins,paid,same,view,outside⟩ := run w B K hb hk (x i) v D record rowWidth word width rowLen
    ((keep 1).1.trans scratch) (by
      refine Stacks.ext rfl rfl rfl ?_
      funext j
      exact (keep j).2.trans (regs j))
  change t ≤ (413*(A*B)*(N*K))*17+6 at time
  rw [show 413*(A*B)*(N*K)*17 = 7021*(A*(B*N*K)) by ring] at time
  change k ≤ 60*(A*(B*N*K))+12 at paid
  refine ⟨z,F,_,Exec.seq cut ins,by omega,same.trans user,?_,?_,?_,?_⟩
  · exact congrArg (fun D : Stacks 8 prime => D.R 0) view
  · exact (congrArg (fun D : Stacks 8 prime => D.L 0) view).trans (keep 0).1
  · exact congrArg (fun D : Stacks 8 prime => D.R 3) view
  · intro j hp ht
    exact ⟨(outside j ht).1.trans (off j hp).1,(outside j ht).2.trans (off j hp).2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
