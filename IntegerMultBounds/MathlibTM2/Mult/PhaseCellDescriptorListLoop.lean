module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorListLoopTrace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedDescriptorFinish

/-! A structural list proof for counted dispatch over physical descriptor packets. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host

variable {N T Q A : ℕ} {P U β : Type} {body : P → Pr P T Q A U}

theorem descriptorListLoop_exec (work : Fin N → Fin T)
    (words : β → Fin N → List (Fin (A+4)))
    (src saved result clock : Fin T) (hreg : [src,saved,result,clock].Nodup)
    (fresh : List (Fin T)) (hsep : ∀ k ∈ fresh, k ∉ [src,saved,result,clock])
    (L : Fin T → List (Fin (A+4))) (step : Pr P T Q A U) (cost : β → ℕ)
    (good : β → List (Fin (A+4)) → Prop) (records : List β)
    (hstep : ∀ r ∈ records, ∀ (v : HS T Q A U) S rest,
      (∀ k ∈ fresh, S.R k = []) → S.L = L →
      S.R src = descriptorBankTape (placedDescriptorFields work (words r))++rest →
      ∃ v' n output, v'.user = v.user ∧ n ≤ cost r ∧
        Exec body step (mk v S) n (mk v' (dispatchedDescriptorState work (words r) src saved result rest output S)) ∧
        good r output)
    (v : HS T Q A U) (S : Stacks T A) (rest : List (Fin (A+4)))
    (hfresh : ∀ k ∈ fresh, S.R k = []) (hL : S.L = L)
    (hsource : S.R src = descriptorScheduleTape work words records++rest)
    (hclock : (S.R clock).length = records.length) :
    ∃ v' n outputs, v'.user = v.user ∧ n ≤ (records.map (fun r => cost r+3)).sum+2 ∧
      Exec body (countedLoop clock step) (mk v S) n
        (mk v' (descriptorLoopFinal work words records src saved result clock rest outputs S)) ∧
      List.Forall₂ good records outputs := by
  obtain ⟨v',n,outputs,hu,hn,he,hgood,_⟩ := descriptorListLoop_exec_trace
    work words src saved result clock hreg fresh hsep L step cost cost good records
    (by intro r hr vi Si tail hf hL hs
        obtain ⟨vf,m,output,hu,hm,he,hgood⟩ := hstep r hr vi Si tail hf hL hs
        exact ⟨vf,m,output,hu,hm,he,hgood,
          IntegerMultBounds.MathlibTM2.Fast.Main.mn_bounded_exec_certify he hm⟩)
    v S rest hfresh hL hsource hclock
  exact ⟨v',n,outputs,hu,hn,he,hgood⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
