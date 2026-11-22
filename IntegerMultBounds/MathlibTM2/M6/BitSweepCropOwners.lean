module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderInputStaging
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOrdinaryOwner

/-! Recover the compact owner bank for the PR589 exit correction. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover
open Shared50ModularControl (prime)

theorem cropSweepOwners_exec {w B K T Q : ℕ} {P U : Type}
    (port : Fin 142081 → Fin 12 ↪ Fin T)
    (shared : ∀ i k j, j ≠ 0 → j ≠ 1 → port i j = port k j)
    (apart : ∀ i k, i ≠ k → ∀ j, port i j ≠ port k 0 ∧ port i j ≠ port k 1)
    (fits : 215 ≤ Q) (body : P → Pr P T Q prime U) (hb : 0 < B) (hk : 0 < K) :
    let A := (prime^w)^16
    let N := prime^(64*(w*64))
    let code := fun i => embProg (port i) (Empty.elim : Empty → P)
      (foreign (liftQ RowPaddingConstructedAlphabet.cropProgram fits))
    ∀ (x : Fin 142081 → Fin (A*(B*K)) → ZMod 2) (order : List (Fin 142081)), order.Nodup →
      ∀ u S, CropCounters (port 0) (A*B) N K S →
      (∀ i ∈ order, WordAtZero (singleLabelBank (firstRowLabel w) x i) (S.L (port i 0)) (S.R (port i 0))) →
      (∀ i ∈ order, ∀ z, readAt blank (S.L (port i 1)) (S.R (port i 1)) z = blank) →
      ∃ z F t, Exec body (Prog.seqList (order.map code)) (mk u S) t (mk z F) ∧
        t ≤ order.length*(7021*(A*B)*(N*K)+6)+1 ∧ z.user = u.user ∧ CropCounters (port 0) (A*B) N K F ∧
        (∀ i ∈ order, WordAtZero (x i) (F.L (port i 1)) (F.R (port i 1))) ∧
        ∀ j, (∀ i ∈ order, ∀ h, port i h ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro A N code x order
  have crop (i) (u : HS T Q prime U) (S : Stacks T prime)
      (input : WordAtZero (singleLabelBank (firstRowLabel w) x i) (S.L (port i 0)) (S.R (port i 0)))
      (empty : ∀ z, readAt blank (S.L (port i 1)) (S.R (port i 1)) z = blank)
      (headers : CropCounters (port i) (A*B) N K S) :
      ∃ v F t, Exec body (code i) (mk u S) t (mk v F) ∧ t ≤ 7021*(A*B)*(N*K)+6 ∧
        v.user = u.user ∧ WordAtZero (x i) (F.L (port i 1)) (F.R (port i 1)) ∧
        CropCounters (port i) (A*B) N K F ∧
        ∀ j, (∀ h, port i h ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
    obtain ⟨v,F,t,run,paid,user,done,off⟩ := placedHoare_exec _ (port i) fits body
      (singleLabelBank_crop_hoare hb hk x i) u S (by
        intro j z
        by_cases hs : j = 0
        · subst j; exact (input z).symm.trans (congrArg (readAt blank (S.L (port i 0)) (S.R (port i 0))) (sub_zero z).symm)
        by_cases hd : j = 1
        · subst j; exact (empty z).symm.trans (congrArg (readAt blank (S.L (port i 1)) (S.R (port i 1))) (sub_zero z).symm)
        rw [(padFrame_aux (A*B) N K _ _ j hs hd).1,(padFrame_aux (A*B) N K _ _ j hs hd).2]
        exact headers j hs hd z)
    refine ⟨v,F,t,run,paid.trans_eq (by ring),user,?_,?_,off⟩
    · intro j
      have h := (done 1 j).symm
      change readAt blank (F.L (port i 1)) (F.R (port i 1)) (j-0) = _ at h
      rw [sub_zero] at h
      exact h
    · intro j hs hd z
      have read := done j z
      rw [(padFrame_aux (A*B) N K _ _ j hs hd).1,(padFrame_aux (A*B) N K _ _ j hs hd).2] at read
      exact read
  induction order with
  | nil =>
    intro _ u S auxS _ _
    exact ⟨u,S,1,Exec.act .done _,by simp,rfl,auxS,by simp,fun _ _ => ⟨rfl,rfl⟩⟩
  | cons i ks ih =>
    intro unique u S auxS inputs empty
    obtain ⟨fresh,nd⟩ := List.nodup_cons.mp unique
    obtain ⟨v,C,m,first,paid,user,out,ready,off⟩ := crop i u S
      (inputs i List.mem_cons_self) (empty i List.mem_cons_self) (by
        intro j h0 h1 l
        rw [shared i 0 j h0 h1]
        exact auxS j h0 h1 l)
    have ne (k) (hk : k ∈ ks) : i ≠ k := fun eq => fresh (eq ▸ hk)
    obtain ⟨z,F,n,rest,bill,same,auxF,outputs,keep⟩ := ih nd v C (by
      intro j h0 h1 l
      rw [← shared i 0 j h0 h1]
      exact ready j h0 h1 l) (by
      intro k hk l
      obtain ⟨hl,hr⟩ := off _ (fun j => (apart i k (ne k hk) j).1)
      rw [hl,hr]
      exact inputs k (List.mem_cons_of_mem _ hk) l) (by
      intro k hk l
      obtain ⟨hl,hr⟩ := off _ (fun j => (apart i k (ne k hk) j).2)
      rw [hl,hr]
      exact empty k (List.mem_cons_of_mem _ hk) l)
    refine ⟨z,F,m+n,Exec.seq first rest,?_,same.trans user,auxF,?_,?_⟩
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      change m ≤ 7021*(A*B)*(N*K)+6 at paid
      omega
    · intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · obtain ⟨hl,hr⟩ := keep _ (fun a ha j => (apart a k (ne a ha).symm j).2)
        intro l
        rw [hl,hr]
        exact out l
      · exact outputs k hk
    · intro j outside
      obtain ⟨hl,hr⟩ := keep j (fun k hk => outside k (List.mem_cons_of_mem _ hk))
      obtain ⟨ll,rr⟩ := off j (outside i List.mem_cons_self)
      exact ⟨hl.trans ll,hr.trans rr⟩

/-- Crop the recursive handoff and execute the exit chart on its compact
outputs. Each padding counter is reused for all owners, including the spare. -/
theorem cropAndCorrectSweep_exec {w B K T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (port : Fin 142081 → Fin 12 ↪ Fin T)
    (shared : ∀ i k j, j ≠ 0 → j ≠ 1 → port i j = port k j)
    (apart : ∀ i k, i ≠ k → ∀ j, port i j ≠ port k 0 ∧ port i j ≠ port k 1)
    (fits : 215 ≤ Q) (hb : 0 < B) (hk : 0 < K) :
    let A := (prime^w)^16
    let N := prime^(64*(w*64))
    ∀ (leave : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := A*(B*K))))
      (chart : Fin leave.tapes ↪ Fin T) (_room : leave.states ≤ Q)
      (fan : Fin (142081+2) ↪ Fin T),
      (∀ i, port i 0 = fan (i.castAdd 2)) → (∀ i, chart (leave.slots i) = port i 1) →
      (∀ j, (∀ i, leave.slots i ≠ j) → ∀ i h, port i h ≠ chart j) →
      ∃ code, ∀ x u S, HelperFan fan (singleLabelBank (firstRowLabel w) x) S →
        ChartPrivateReady leave (embStk chart S) → CropCounters (port 0) (A*B) N K S →
        (∀ i z, readAt blank (S.L (port i 1)) (S.R (port i 1)) z = blank) →
        ∃ z F t, Exec body code (mk u S) t (mk z F) ∧
          t ≤ 142081*(7021*(A*B)*(N*K)+6)+1 + (leave.cost*(leave.tapes+5)+6) ∧
          z.user = u.user ∧ RepT (phaseOwners (leave.transform x))
            (fun i => F.L (port i 1)) (fun i => F.R (port i 1)) ∧
          ∀ j, (∀ i h, port i h ≠ j) → (∀ h, chart h ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro A N leave chart room fan src dst separation
  let order := List.finRange 142081
  let crop : Fin 142081 → Pr P T Q prime U := fun i => embProg (port i) (Empty.elim : Empty → P)
    (foreign (liftQ RowPaddingConstructedAlphabet.cropProgram fits))
  refine ⟨(Prog.seqList (order.map crop)).seq (embProg chart Empty.elim (foreign (liftQ leave.program room))),?_⟩
  intro x u S live privateReady headers empty
  obtain ⟨v,D,k,run,paid,user,_,words,off⟩ := cropSweepOwners_exec (w := w) port shared apart fits body hb hk x order
    (List.nodup_finRange _) u S headers (by
      intro i _ j
      rw [src]
      have payload := fanPayload live i j
      rw [encodedOwnerCell,sub_zero] at payload
      exact payload) (fun i _ => empty i)
  obtain ⟨z,F,l,correct,time,same,_,out,_,frame⟩ := ownerStage_exec_emb leave chart room body x v D (by
    intro j hj h
    have kept := off _ (fun i _ a => separation j hj i a)
    change _ = readAt blank (D.L (chart j)) (D.R (chart j)) _
    rw [kept.1,kept.2]
    exact privateReady j hj h) (by
    intro i j
    change _ = readAt blank (D.L (chart (leave.slots i))) (D.R (chart (leave.slots i))) (j-0)
    rw [dst,sub_zero]
    exact (words i (List.mem_finRange i) j).symm)
  refine ⟨z,F,k+l,Exec.seq run correct,Nat.add_le_add (by simpa [order] using paid) time,
    same.trans user,?_,?_⟩
  · intro i j
    have read := out i j
    simpa only [embStk,Function.comp_apply,dst] using read
  · intro j hp hc
    have kept := off j (fun i _ => hp i)
    exact ⟨((frame j hc).1).trans kept.1,((frame j hc).2).trans kept.2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
