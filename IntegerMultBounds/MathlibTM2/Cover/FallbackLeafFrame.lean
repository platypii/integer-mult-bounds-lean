module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPlacedLeaf

/-! A private leaf bank shares only the payload tape with the recursive caller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {n T Q A : ℕ} {P U : Type}

/-- Exchange the local payload slot with the caller's payload slot. -/
def payloadBank (payload : Fin n) (localPayload : Fin T) : Fin T ↪ Fin (n+T) :=
  (Fin.natAddEmb n).trans (Equiv.swap (localPayload.natAdd n) (payload.castAdd T)).toEmbedding

theorem payloadBank_shared (payload : Fin n) (localPayload : Fin T) :
    payloadBank payload localPayload localPayload = payload.castAdd T := by simp [payloadBank]

theorem payloadBank_private (payload : Fin n) (localPayload j : Fin T) (ne : j ≠ localPayload) :
    payloadBank payload localPayload j = j.natAdd n := by
  have apart : j.natAdd n ≠ payload.castAdd T := by
    intro eq
    have h := congrArg Fin.val eq
    simp only [Fin.val_natAdd,Fin.val_castAdd] at h
    omega
  exact Equiv.swap_apply_of_ne_of_ne ((Fin.natAddEmb n).injective.ne ne) apart

/-- Load the six live headers and the unit pivot into a fresh leaf bank.
The payload is already in place. The private destination tape starts blank. -/
def leafHeaderSources : Fin 7 → Fin 58 := ![2,53,28,44,45,56,44]
def leafHeaderTargets : Fin 7 ↪ Fin 62 := ⟨![2,53,28,44,45,56,61],by decide⟩

/-- The padded header is copied twice, once as the leaf's unit pivot. -/
theorem leafHeaderCopy_cost (lengthAt : Fin 58 → ℕ) (H J w rank : ℕ)
    (base : lengthAt 2 = H) (width : lengthAt 53 = J) (unitLen : lengthAt 28 = 1)
    (padded : lengthAt 44 = H) (clockLen : lengthAt 45 = w) (archive : lengthAt 56 = rank*H) :
    ((List.finRange 7).map fun i => 6*lengthAt (leafHeaderSources i)+6).sum+1 =
      6*(3*H+J+1+w+rank*H)+43 := by
  change (6*lengthAt 2+6) + ((6*lengthAt 53+6) + ((6*lengthAt 28+6) +
    ((6*lengthAt 44+6) + ((6*lengthAt 45+6) + ((6*lengthAt 56+6) +
    ((6*lengthAt 44+6) + 0)))))) + 1 = _
  rw [base,width,unitLen,padded,clockLen,archive]
  omega

def copyLeafHeaders {k : ℕ} (src dst : Fin k → Fin T) (tmp aux : Fin T) : List (Fin k) → Pr P T Q A U
  | [] => .act .done
  | i :: is => .seq (bcopy (src i) (dst i) tmp aux) (copyLeafHeaders src dst tmp aux is)

theorem copyLeafHeaders_exec {k : ℕ} (body : P → Pr P T Q A U) (src : Fin k → Fin T) (dst : Fin k ↪ Fin T)
    (tmp aux : Fin T) (apart : ∀ i j, src i ≠ dst j)
    (ports : ∀ i, [src i,dst i,tmp,aux].Nodup) (xs : List (Fin k)) (unique : xs.Nodup)
    (v : HS T Q A U) (S : Stacks T A) (ht : S.R tmp = []) (ha : S.R aux = [])
    (empty : ∀ i ∈ xs, S.R (dst i) = []) :
    ∃ z F, z.user = v.user ∧
      Exec body (copyLeafHeaders src dst tmp aux xs) (mk v S)
        ((xs.map fun i => 6*(S.R (src i)).length+6).sum+1) (mk z F) ∧
      F.L = S.L ∧ (∀ i ∈ xs, F.R (dst i) = S.R (src i)) ∧
      ∀ k, (∀ i ∈ xs, dst i ≠ k) → F.R k = S.R k := by
  induction xs generalizing v S with
  | nil => exact ⟨v,S,rfl,Exec.act _ _,rfl,by simp,fun _ _ => rfl⟩
  | cons i xs ih =>
    obtain ⟨u,hu,copy⟩ := bcopy_exec body (ports i) v S ht ha
    rw [empty i (by simp),List.append_nil] at copy
    let D := {S with R := Function.update S.R (dst i) (S.R (src i))}
    have keep (k) (ne : k ≠ dst i) : D.R k = S.R k := Function.update_of_ne ne _ _
    have nd := ports i
    simp only [List.nodup_cons,List.mem_cons,not_or] at nd
    obtain ⟨z,F,hz,rest,left,loaded,off⟩ := ih unique.tail u D
      ((keep _ (Ne.symm nd.2.1.1)).trans ht) ((keep _ (Ne.symm nd.2.1.2.1)).trans ha)
      (fun j hj => (keep _ (dst.injective.ne (fun eq => unique.notMem (eq ▸ hj)))).trans
        (empty j (by simp [hj])))
    have sizes : (xs.map fun j => 6*(D.R (src j)).length+6) =
        (xs.map fun j => 6*(S.R (src j)).length+6) := List.map_congr_left fun j _ => by rw [keep _ (apart j i)]
    rw [sizes] at rest
    refine ⟨z,F,hz.trans hu,?_,left,?_,?_⟩
    · simpa only [copyLeafHeaders,List.map_cons,List.sum_cons,Nat.add_assoc] using Exec.seq copy rest
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | h
      · exact (off (dst j) (fun a ha => dst.injective.ne (fun eq => unique.notMem (eq ▸ ha)))).trans (Function.update_self ..)
      · exact (loaded j h).trans (keep _ (apart j i))
    · intro k hk
      exact (off _ (fun a ha => hk a (List.mem_cons_of_mem _ ha))).trans
        (keep _ (hk i (by simp)).symm)

/-- Copy selected caller headers into distinct private tapes and preserve every caller stack. -/
theorem loadPrivateHeaders_exec {k c h : ℕ} (caller : Fin c ↪ Fin n) (localHost : Fin h ↪ Fin T)
    (sources : Fin k → Fin c) (targets : Fin k ↪ Fin h) (tmp aux : Fin h)
    (distinctPorts : ∀ i, [targets i,tmp,aux].Nodup)
    (body : P → Pr P (n+T) Q A U) (v : HS (n+T) Q A U) (S : Stacks (n+T) A)
    (free : ∀ j : Fin T, S.L (j.natAdd n) = [] ∧ S.R (j.natAdd n) = []) :
    let src := fun i => (caller (sources i)).castAdd T
    let privatePort := localHost.trans (Fin.natAddEmb n)
    let dst := targets.trans privatePort
    ∃ z F, z.user = v.user ∧
      Exec body (copyLeafHeaders src dst (privatePort tmp) (privatePort aux) (List.finRange k)) (mk v S)
        (((List.finRange k).map fun i => 6*(S.R (src i)).length+6).sum+1) (mk z F) ∧
      F.L = S.L ∧ (∀ j : Fin n, F.R (j.castAdd T) = S.R (j.castAdd T)) ∧
      (∀ i, F.R (dst i) = S.R (src i)) ∧
      ∀ j : Fin T, (∀ i, localHost (targets i) ≠ j) → F.R (j.natAdd n) = [] := by
  intro src privatePort dst
  have apart (j : Fin n) (k : Fin T) : j.castAdd T ≠ k.natAdd n := by
    intro eq
    have val := congrArg Fin.val eq
    simp only [Fin.val_castAdd,Fin.val_natAdd] at val
    omega
  have ports (i : Fin k) : [src i,dst i,privatePort tmp,privatePort aux].Nodup := by
    have distinct := List.Nodup.map privatePort.injective
      (distinctPorts i)
    apply List.nodup_cons.mpr
    exact ⟨by simp [src,dst,privatePort,Function.Embedding.trans_apply,apart],distinct⟩
  obtain ⟨z,F,hz,run,left,loaded,off⟩ := copyLeafHeaders_exec body src dst _ _ (fun i j => apart _ _)
    ports (List.finRange k) (List.nodup_finRange _) v S (free _).2 (free _).2 (fun _ _ => (free _).2)
  exact ⟨z,F,hz,run,left,fun j => off _ (fun _ _ => (apart j _).symm),
    fun i => loaded i (List.mem_finRange i),fun j hj =>
      (off _ (fun i _ => (Fin.natAddEmb n).injective.ne (hj i))).trans (free j).2⟩

/-- Initialize the actual seven leaf words from the 58-port caller bank.
Every caller stack is preserved, including both stacks of the shared payload. -/
theorem loadPrivateLeaf_exec (caller : Fin 58 ↪ Fin n) (localHost : Fin 62 ↪ Fin T)
    (body : P → Pr P (n+T) Q A U) (v : HS (n+T) Q A U) (S : Stacks (n+T) A)
    (free : ∀ j : Fin T, S.L (j.natAdd n) = [] ∧ S.R (j.natAdd n) = []) :
    let src := fun i => (caller (leafHeaderSources i)).castAdd T
    let privatePort := localHost.trans (Fin.natAddEmb n)
    let dst := leafHeaderTargets.trans privatePort
    ∃ z F, z.user = v.user ∧
      Exec body (copyLeafHeaders src dst (privatePort 0) (privatePort 1) (List.finRange 7)) (mk v S)
        (((List.finRange 7).map fun i => 6*(S.R (src i)).length+6).sum+1) (mk z F) ∧
      F.L = S.L ∧ (∀ j : Fin n, F.R (j.castAdd T) = S.R (j.castAdd T)) ∧
      (∀ i, F.R (dst i) = S.R (src i)) ∧
      ∀ j : Fin T, (∀ i, localHost (leafHeaderTargets i) ≠ j) → F.R (j.natAdd n) = [] := by
  exact loadPrivateHeaders_exec caller localHost leafHeaderSources leafHeaderTargets 0 1 (by decide) body v S free

/-- The loaded private bank presents the original word and a blank destination
to the first column operation. The reciprocal archive stays on its separate tape. -/
theorem privateLeaf_ready {b w W d : ℕ} [NeZero (b^(w+1))] {α : Type}
    (caller : Fin 58 ↪ Fin n) (host : Fin 62 ↪ Fin T) (H J : ℕ) (sym : α → Fin 4)
    (source : ℤ → Fin 4) (word : Fin ((b^(w+1))^d*W) → α) (S F : Stacks (n+T) A)
    (base : S.R ((caller 2).castAdd T) = binSyms H (b^(w+1)))
    (width : S.R ((caller 53).castAdd T) = binSyms J W)
    (one : S.R ((caller 28).castAdd T) = binSyms 1 1)
    (padded : S.R ((caller 44).castAdd T) = binSyms H (1 : ZMod (b^(w+1))).val)
    (clockLen : (S.R ((caller 45).castAdd T)).length = w)
    (left : F.L = S.L) (keep : ∀ j : Fin n, F.R (j.castAdd T) = S.R (j.castAdd T))
    (loaded : ∀ i, F.R ((host (leafHeaderTargets i)).natAdd n) =
      S.R ((caller (leafHeaderSources i)).castAdd T))
    (freeL : ∀ j : Fin T, S.L (j.natAdd n) = [])
    (freeR : ∀ j : Fin T, (∀ i, host (leafHeaderTargets i) ≠ j) → F.R (j.natAdd n) = [])
    (src : ∀ z, readAt blank (S.L ((caller 24).castAdd T)) (S.R ((caller 24).castAdd T)) (z-0) =
      RadixToBinary.binaryEncoding.encode (putWord source 0 (List.ofFn (sym ∘ word)) z)) :
    ColumnRecordReady (leafColumn.trans host) H J (binSyms H (1 : ZMod (b^(w+1))).val)
      sym source (fun _ => blank) 0 0 word id (embStk (payloadBank (caller 24) (host 24)) F) ∧
    let D := embStk (payloadBank (caller 24) (host 24)) F
    D.R (host 56) = S.R ((caller 56).castAdd T) ∧
    ∀ j, (∀ i, host i ≠ j) → D.L j = [] ∧ D.R j = [] := by
  let bank := payloadBank (caller 24) (host 24)
  have privateAt (j : Fin 62) (ne : j ≠ 24) : bank (host j) = (host j).natAdd n :=
    payloadBank_private _ _ _ (host.injective.ne ne)
  have header (i : Fin 7) :
      (embStk bank F).R (host (leafHeaderTargets i)) = S.R ((caller (leafHeaderSources i)).castAdd T) := by
    change F.R (bank _) = _
    rw [privateAt _ ((by decide : ∀ i, leafHeaderTargets i ≠ 24) i)]
    exact loaded i
  have emptyAt (j : Fin 62) (ne : j ≠ 24) (miss : ∀ i, leafHeaderTargets i ≠ j) :
      (embStk bank F).L (host j) = [] ∧ (embStk bank F).R (host j) = [] := by
    change F.L (bank _) = [] ∧ F.R (bank _) = []
    rw [privateAt _ ne,left]
    exact ⟨freeL _,freeR _ (fun i => host.injective.ne (miss i))⟩
  refine ⟨?_,header 5,?_⟩
  swap
  · intro j outside
    have ne := (outside 24).symm
    change F.L (bank j) = [] ∧ F.R (bank j) = []
    rw [show bank j = j.natAdd n from payloadBank_private _ _ _ ne,left]
    exact ⟨freeL _,freeR _ (fun i => outside (leafHeaderTargets i))⟩
  refine ⟨word,⟨(header 0).trans base,(header 1).trans width,(header 2).trans one,
    (header 3).trans padded,(congrArg List.length (header 4)).trans clockLen,(header 6).trans padded,?_,?_,?_⟩,
    fun _ _ => rfl⟩
  · intro j hj
    have h := (by decide : ∀ j ∈ shearWork, leafColumn j ≠ 24 ∧ ∀ i, leafHeaderTargets i ≠ leafColumn j) j hj
    exact emptyAt _ h.1 h.2
  · intro z
    change readAt _ (F.L (payloadBank _ (host 24) (host 24))) (F.R (payloadBank _ (host 24) (host 24))) _ = _
    rw [payloadBank_shared,left,keep]
    exact src z
  · intro z
    obtain ⟨l,r⟩ := emptyAt 25 (by decide) (by decide)
    change readAt _ ((embStk bank F).L (host 25)) ((embStk bank F).R (host 25)) _ = _
    rw [l,r]
    simp [readAt]
    rfl

/-- A completed inner run can change no other caller stack, even when
its destination or header stacks finish in a noncanonical representation. -/
theorem payloadFrame_exec {Q' : ℕ} (capacity : Q ≤ Q') (payload : Fin n) (localPayload : Fin T) (positive : 0 < Q)
    (body : P → Pr P (n+T) Q' A U) (prog : Pr Empty T Q A U)
    (v : HS (n+T) Q' A U) (S : Stacks (n+T) A) :
    let bank := payloadBank payload localPayload
    ∀ u D steps, Exec Empty.elim prog (mk (stateLiftDown positive (embDn bank v)) (embStk bank S)) steps (mk u D) →
      ∃ z F, z.user = u.user ∧
        Exec body (statePlacedNormalized bank capacity positive Empty.elim prog)
          (mk v S) (1+steps) (mk z F) ∧ embStk bank F = D ∧
        ∀ j : Fin n, j ≠ payload → F.L (j.castAdd T) = S.L (j.castAdd T) ∧ F.R (j.castAdd T) = S.R (j.castAdd T) := by
  intro bank u D steps run
  obtain ⟨z,_,hz,placed⟩ := statePlaced_exec_normalized bank bank.injective capacity positive Empty.elim
    (body' := body) (fun e => nomatch e) v S run
  refine ⟨z,_,hz,placed,embStk_ovr bank.injective _ _,?_⟩
  intro j ne
  apply embOvr_off
  intro i
  by_cases eq : i = localPayload
  · subst i
    exact (payloadBank_shared payload localPayload) ▸ ((Fin.castAddEmb T).injective.ne ne.symm)
  · rw [show bank i = i.natAdd n from payloadBank_private payload localPayload i eq]
    intro hit
    have h := congrArg Fin.val hit
    simp only [Fin.val_natAdd,Fin.val_castAdd] at h
    omega

/-- Run initialization and the embedded leaf, then release all private tapes.
Only the caller payload can change, and it contains the inner run's exact stacks. -/
theorem privateLeaf_return {Q' : ℕ} (capacity : Q ≤ Q') (positive : 0 < Q)
    (caller : Fin 58 ↪ Fin n) (host : Fin 62 ↪ Fin T) (body : P → Pr P (n+T) Q' A U)
    (prog : Pr Empty T Q A U) (v : HS (n+T) Q' A U) (S : Stacks (n+T) A)
    (free : ∀ i : Fin (n+T), n ≤ i.val → S.L i = [] ∧ S.R i = []) :
    let src := fun i => (caller (leafHeaderSources i)).castAdd T
    let port := host.trans (Fin.natAddEmb n)
    let dst := leafHeaderTargets.trans port
    let setup : Pr P (n+T) Q' A U := copyLeafHeaders src dst (port 0) (port 1) (List.finRange 7)
    let initSteps := ((List.finRange 7).map fun i => 6*(S.R (src i)).length+6).sum+1
    let payload := caller 24
    let localPayload := host 24
    let bank := payloadBank payload localPayload
    let run := setup.seq (statePlacedNormalized bank capacity positive Empty.elim prog)
    let work := (List.finRange (n+T)).filter fun i => n ≤ i.val
    ∃ (u : HS (n+T) Q' A U) (D : Stacks (n+T) A), u.user = v.user ∧ D.L = S.L ∧
      (∀ j : Fin n, D.R (j.castAdd T) = S.R (j.castAdd T)) ∧
      (∀ i, D.R (dst i) = S.R (src i)) ∧
      (∀ j : Fin T, (∀ i, host (leafHeaderTargets i) ≠ j) → D.R (j.natAdd n) = []) ∧
    ∀ z F steps push, Exec Empty.elim prog (mk (stateLiftDown positive (embDn bank u)) (embStk bank D))
      steps (mk z F) → Fast.Main.mnProgPush run ≤ push → (∀ f, Fast.Main.mnProgPush (body f) ≤ push) →
      let ticks := initSteps+(1+steps)
      ∃ a G l, a.user = z.user ∧ l ≤ ticks+(4*work.length+1+work.length*(6*(push*ticks))) ∧
        Exec body (run.seq (clearWorkTapes work)) (mk v S) l (mk a G) ∧
        G.L (payload.castAdd T) = F.L localPayload ∧ G.R (payload.castAdd T) = F.R localPayload ∧
        (∀ j : Fin n, j ≠ payload → G.L (j.castAdd T) = S.L (j.castAdd T) ∧ G.R (j.castAdd T) = S.R (j.castAdd T)) ∧
        ∀ i : Fin (n+T), n ≤ i.val → G.L i = [] ∧ G.R i = [] := by
  intro src port dst setup initSteps payload localPayload bank run work
  obtain ⟨u,D,hu,init,left,keep,loaded,empty⟩ := loadPrivateLeaf_exec caller host body v S
    (fun j => free (j.natAdd n) (Nat.le_add_right ..))
  refine ⟨u,D,hu,left,keep,loaded,empty,?_⟩
  intro z F steps push inner hp hb ticks
  obtain ⟨a,G,ha,placed,proj,frame⟩ := payloadFrame_exec capacity payload localPayload positive body prog u D z F steps inner
  obtain ⟨a',G',l,ha',_,bound,finished,small,clean⟩ := clearPrivateAfter n body run v a S G ticks push
    (Exec.seq init placed) hp hb free
  have shared := small (payload.castAdd T) payload.isLt
  have lhit := congrArg (fun B : Stacks T A => B.L localPayload) proj
  have rhit := congrArg (fun B : Stacks T A => B.R localPayload) proj
  change G.L (payloadBank payload localPayload localPayload) = _ at lhit
  change G.R (payloadBank payload localPayload localPayload) = _ at rhit
  rw [payloadBank_shared] at lhit rhit
  refine ⟨a',G',l,ha'.trans ha,bound,finished,shared.1.trans lhit,shared.2.trans rhit,?_,clean⟩
  intro j ne
  have h := small (j.castAdd T) j.isLt
  exact ⟨h.1.trans ((frame j ne).1.trans (congrFun left _)),h.2.trans ((frame j ne).2.trans (keep j))⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
