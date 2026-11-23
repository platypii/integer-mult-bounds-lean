module

public import IntegerMultBounds.MathlibTM2.M6.BitPackedStageHandoff
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderCompactRead
public import IntegerMultBounds.MathlibTM2.Cover.FallbackShearCleanup
public import IntegerMultBounds.MathlibTM2.Host.OrderedMove

/-! Materialize a represented owner word on its own tape at recursive entry. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host Cover.Fallback
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- Two temporary tapes can be shared by every owner. The clearing term is
exactly the charge for the two physical stacks of this owner. -/
theorem materializeOwnerInPlace {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (src tmp buf : Fin T) (regs : [src,tmp,buf].Nodup) :
    ∃ code : Pr P T Q prime U, ∀ {V : ℕ} (x : Fin V → ZMod 2) u (S : Stacks T prime),
      WordAtZero x (S.L src) (S.R src) → S.L tmp = [] → S.R tmp = [] → S.R buf = [] →
      ∃ z, z.user = u.user ∧ Exec body code (mk u S)
        (12*V+19+4*(S.L src).length+2*(S.R src).length)
        (mk z {S with L := Function.update S.L src [],
                      R := Function.update S.R src (List.ofFn fun i => SparseRoleCircuit.encode (x i))}) := by
  refine ⟨(loadCompactWord src tmp buf).seq ((clearWorkTapes [src]).seq (moveRightOrdered buf tmp src)),?_⟩
  intro V x u S word tl tr br
  obtain ⟨v,user,copy⟩ := loadCompactWord_exec body src tmp buf regs x u S word tl tr
  rw [br,List.append_nil] at copy
  regs_ne regs
  let xs := List.ofFn fun i => SparseRoleCircuit.encode (a := prime) (x i)
  let B := {S with R := Function.update S.R buf xs}
  obtain ⟨w,same,clear⟩ := clearWorkTapes_exec body [src] (by simp) v B
  let D := {B with L := fun j => if j ∈ [src] then [] else B.L j,
                   R := fun j => if j ∈ [src] then [] else B.R j}
  obtain ⟨z,done,move⟩ := moveRightOrdered_exec (body := body) buf tmp src
    ‹tmp ≠ buf›.symm ‹src ≠ buf›.symm ‹src ≠ tmp›.symm w D
    (by simp [D,B,‹src ≠ tmp›.symm,‹tmp ≠ buf›,tr])
  refine ⟨z,done.trans (same.trans user),(copy.seq (clear.seq move)).cast ?_ ?_⟩
  · simp [D,B,xs,‹src ≠ buf›,‹src ≠ buf›.symm]
    omega
  · apply congrArg (mk z)
    refine Stacks.ext ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · funext j
      simp [D,B,Function.update_apply]
    · funext j
      by_cases a : j = src
      · subst j; simp [D,B,xs,‹src ≠ buf›.symm]
      · by_cases b : j = buf
        · subst j; simp [D,B,a,br]
        · simp [D,B,a,b]

/-- Materialize a whole fan in place, charging each owner once. Both buffers
are restored between owners and the control tapes are untouched. -/
theorem materializeOwnerBank {P U : Type} {T Q k : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin k ↪ Fin T) (tmp buf : Fin T) (regs : ∀ i, [bank i,tmp,buf].Nodup)
    (is : List (Fin k)) (distinct : is.Nodup) :
    ∃ code : Pr P T Q prime U, ∀ {V : ℕ} (x : Fin k → Fin V → ZMod 2) u (S : Stacks T prime),
      (∀ i ∈ is, WordAtZero (x i) (S.L (bank i)) (S.R (bank i))) →
      S.L tmp = [] → S.R tmp = [] → S.R buf = [] →
      ∃ z F n, Exec body code (mk u S) n (mk z F) ∧ z.user = u.user ∧
        n = (is.map (fun i => 12*V+19+4*(S.L (bank i)).length+2*(S.R (bank i)).length)).sum+1 ∧
        (∀ i ∈ is, F.L (bank i) = [] ∧ F.R (bank i) = List.ofFn (fun j => SparseRoleCircuit.encode (x i j))) ∧
        ∀ j, (∀ i ∈ is, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  induction is with
  | nil =>
    refine ⟨.act .done,?_⟩
    intro V x u S _ _ _ _
    exact ⟨u,S,1,Exec.act _ _,rfl,rfl,by simp,by simp⟩
  | cons i is ih =>
    obtain ⟨head,one⟩ := materializeOwnerInPlace body (bank i) tmp buf (regs i)
    obtain ⟨rest,run⟩ := ih distinct.of_cons
    refine ⟨head.seq rest,?_⟩
    intro V x u S ready tl tr br
    obtain ⟨v,same,first⟩ := one (x i) u S (ready i List.mem_cons_self) tl tr br
    let D := {S with L := Function.update S.L (bank i) [], R := Function.update S.R (bank i) (List.ofFn fun j => SparseRoleCircuit.encode (x i j))}
    have away j (mem : j ∈ is) : bank j ≠ bank i := bank.injective.ne (fun h => distinct.notMem (h ▸ mem))
    have ports := regs i
    regs_ne ports
    obtain ⟨z,F,n,next,user,time,words,frame⟩ := run x v D
      (by intro j mem; simpa [D,away j mem] using ready j (List.mem_cons_of_mem _ mem))
      (by simp [D,Ne.symm ‹bank i ≠ tmp›,tl]) (by simp [D,Ne.symm ‹bank i ≠ tmp›,tr])
      (by simp [D,Ne.symm ‹bank i ≠ buf›,br])
    refine ⟨z,F,_,first.seq next,user.trans same,?_,?_,?_⟩
    · have eq : is.map (fun j => 12*V+19+4*(D.L (bank j)).length+2*(D.R (bank j)).length) =
          is.map (fun j => 12*V+19+4*(S.L (bank j)).length+2*(S.R (bank j)).length) :=
          List.map_congr_left (fun j mem => by simp [D,away j mem])
      rw [time,eq,List.map_cons,List.sum_cons,Nat.add_assoc]
      omega
    · intro j mem
      rcases List.mem_cons.mp mem with rfl|h
      · simpa [D] using frame (bank j) (fun t ht => away t ht)
      · exact words j h
    · intro j off
      have ne := (off i List.mem_cons_self).symm
      simpa [D,ne] using frame j (fun t ht => off t (List.mem_cons_of_mem _ ht))

/-- Call the packed worker on the splitter's owner tapes, including its spare
owner. The worker may change private tapes within its charged budget. -/
theorem callOnRepresentedOwners {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (src dst : Fin (142081+2) ↪ Fin T) (tmp buf : Fin T)
    (regs : ∀ i : Fin 142081, [src (i.castAdd 2),tmp,buf].Nodup) (entry : P) :
    let owner := (Fin.castAddEmb 2 (n := 142081)).trans src
    ∃ code : Pr P T Q prime U, ∀ {V price} effect seed,
      PackedPieceHandoffWithCharge cleanupWeight V effect body (body entry) src dst seed price →
      ∀ x u (S : Stacks T prime), HelperFan src x S →
      S.L tmp = [] → S.R tmp = [] → S.R buf = [] →
      (∀ j, (∀ i, src i ≠ j) → S.L j = seed.L j ∧ S.R j = seed.R j) →
      ∃ z F t y, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        ParentStageWords (fun i => dst (i.castAdd 2)) dst V y F ∧ effect x y ∧
        ∀ js : List (Fin T), js.Nodup → (∀ j ∈ js, ∀ i, owner i ≠ j) →
          t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+price+
            ((List.finRange 142081).map (fun i =>
              12*V+19+4*(S.L (owner i)).length+2*(S.R (owner i)).length)).sum+3 := by
  intro owner
  obtain ⟨prep,run⟩ := materializeOwnerBank body owner tmp buf regs _ (List.nodup_finRange _)
  refine ⟨prep.seq (.call entry),?_⟩
  intro V price effect seed worker x u S rows tl tr br privateTapes
  obtain ⟨v,D,a,exec,user,bill,words,frame⟩ := run x u S (by
    intro i _ j
    simpa only [owner,Function.Embedding.trans_apply,Fin.castAddEmb_apply,encodedOwnerCell,sub_zero] using fanPayload rows i j) tl tr br
  have keep j (away : ∀ i, owner i ≠ j) := frame j (fun i _ => away i)
  have ready : ParentStageWords (fun i => src (i.castAdd 2)) src V x D := by
    refine ⟨fun i => (words i (List.mem_finRange i)).1,fun i => (words i (List.mem_finRange i)).2,?_⟩
    intro j t
    have stable := keep (src (j.natAdd 142081)) (fun i => src.injective.ne (by
      intro e; have h := congrArg Fin.val e; change i.val = 142081+j.val at h; omega))
    change _ = readAt blank _ _ _
    rw [stable.1,stable.2]
    simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_right,CountedLoopReuseAlphabet.bank,
      CountedLoopReuseAlphabet.controls,ite_self,embStk,Function.comp_apply] using rows (j.natAdd 142081) t
  obtain ⟨z,F,n,y,call,paid,same,out,action⟩ := worker x v D ready (by
    intro j off
    have stable := keep j (fun i => off (i.castAdd 2))
    exact ⟨stable.1.trans (privateTapes j off).1,stable.2.trans (privateTapes j off).2⟩)
  refine ⟨z,F,_,y,exec.seq (Exec.call call),same.trans user,out,action,?_⟩
  intro js unique away
  have charge : tapeCharge cleanupWeight js D = tapeCharge cleanupWeight js S := by
    unfold tapeCharge
    apply congrArg List.sum
    apply List.map_congr_left
    intro j mem
    rw [(keep j (away j mem)).1,(keep j (away j mem)).2]
  have h := paid js unique
  rw [charge] at h
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
