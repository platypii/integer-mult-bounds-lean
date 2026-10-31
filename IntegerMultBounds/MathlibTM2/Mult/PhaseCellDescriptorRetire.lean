module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorEmit

/-! Retire generated descriptor prefixes by reading their actual length headers.
The caller's queue suffix is preserved, with no supplied payload counter. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def retireDescriptorPacket (src count tmp : Fin T) : Pr P T Q A U :=
  .seq (preTake src count) (.seq (usub count src tmp) (uclear count))

theorem retireDescriptorPacket_exec (src count tmp : Fin T) (hreg : [src,count,tmp].Nodup)
    (xs rest : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = descriptorPacket xs++rest) (hcount : S.R count = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 9*xs.length+9 ∧
      Exec body (retireDescriptorPacket src count tmp) (mk v S) n
        (mk v' {S with R := Function.update S.R src rest}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,S₁,n₁,hu₁,hn₁,he₁,hh₁,hframe₁⟩ := preTake_runs (body := body) (tg := id) Function.injective_id
    ‹src ≠ count› S.R (by simpa only [descriptorPacket,List.append_assoc] using hsrc) v S (fun _ => rfl)
  let R₁ := Function.update (Function.update S.R src (xs++rest)) count (List.replicate xs.length tick)
  have hS₁ : S₁ = {S with R := R₁} := by
    refine Stacks.ext hframe₁.1 hframe₁.2.1 hframe₁.2.2.1 ?_
    funext i
    simpa only [R₁,hcount,List.append_nil,id_eq] using hh₁ i
  subst S₁
  obtain ⟨v₂,hu₂,he₂⟩ := usub_exec (body := body) ‹src ≠ count›.symm ‹count ≠ tmp› ‹src ≠ tmp› v₁ {S with R := R₁}
    (by simp [R₁,‹src ≠ tmp›.symm,‹count ≠ tmp›.symm,htmp])
  have hlen : (R₁ count).length = xs.length := by simp [R₁]
  have hsource : R₁ src = xs++rest := by simp [R₁,‹src ≠ count›]
  let M : Stacks T A := {S with R := Function.update R₁ src rest}
  have he₂' : Exec body (usub count src tmp) (mk v₁ {S with R := R₁}) (4*xs.length+4) (mk v₂ M) := by
    simpa only [hlen,hsource,List.drop_left,M] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body count v₂ M
  have hc : (M.R count).length = xs.length := by simp [M,R₁,‹src ≠ count›.symm]
  rw [hc] at he₃
  refine ⟨v₃,n₁+((4*xs.length+4)+(2*xs.length+2)),hu₃.trans (hu₂.trans hu₁),by omega,
    (Exec.seq he₁ (Exec.seq he₂' he₃)).cast rfl ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hic : i = count
  · subst i; simp [M,R₁,‹src ≠ count›.symm,hcount]
  by_cases his : i = src
  · subst i; simp [M,hic]
  · simp only [M,R₁,Function.update_of_ne hic,Function.update_of_ne his]

/-- The fixed field count determines traversal, while each payload length is
read from the queue itself. -/
def retireDescriptorBank (src count tmp : Fin T) : ℕ → Pr P T Q A U
  | 0 => .act .done
  | n+1 => .seq (retireDescriptorPacket src count tmp) (retireDescriptorBank src count tmp n)

theorem retireDescriptorBank_exec (src count tmp : Fin T) (hreg : [src,count,tmp].Nodup)
    (fields : List (Fin T × List (Fin (A+4)))) (rest : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = descriptorBankTape fields++rest) (hcount : S.R count = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 9*(descriptorBankTape fields).length+1 ∧
      Exec body (retireDescriptorBank src count tmp fields.length) (mk v S) n
        (mk v' {S with R := Function.update S.R src rest}) := by
  induction fields generalizing v S with
  | nil =>
    refine ⟨v,1,rfl,by simp [descriptorBankTape],?_⟩
    have hsource : S.R src = rest := by simpa [descriptorBankTape] using hsrc
    simpa [retireDescriptorBank,Action.run,←hsource,Function.update_eq_self] using Exec.act (body := body) .done (mk v S)
  | cons f fields ih =>
    have hr := hreg
    regs_ne hr
    obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := retireDescriptorPacket_exec src count tmp hreg f.2
      (descriptorBankTape fields++rest) v S
      (by simpa only [descriptorBankTape,List.flatMap_cons,List.append_assoc] using hsrc) hcount htmp
    let M : Stacks T A := {S with R := Function.update S.R src (descriptorBankTape fields++rest)}
    obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := ih v₁ M (by simp [M])
      (by simpa only [M,Function.update_of_ne ‹src ≠ count›.symm] using hcount)
      (by simpa only [M,Function.update_of_ne ‹src ≠ tmp›.symm] using htmp)
    refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl ?_⟩
    · simp only [descriptorBankTape,List.flatMap_cons,List.length_append,descriptorPacket,preFld,
        List.length_replicate,List.length_singleton]
      simp only [descriptorBankTape,descriptorPacket,preFld] at hn₂
      omega
    · apply congrArg (mk v₂)
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      by_cases hi : i = src
      · subst i; simp only [Function.update_self]
      · simp only [M,Function.update_of_ne hi]

theorem retireDescriptorPacket_native (src count tmp : Fin T) :
    mnNativePushBound 1 (retireDescriptorPacket (P := P) (Q := Q) (A := A) (U := U) src count tmp) := by
  simp [retireDescriptorPacket,preTake,preWhileTop,prePeek,twMvTop,usub,uclear,scanR,drainR,
    popDo,keepIn,dropTop,moveR,whileR,moveStep,peekR,mnNativePushBound,mnActPush]

theorem retireDescriptorBank_native (src count tmp : Fin T) (n : ℕ) :
    mnNativePushBound 1 (retireDescriptorBank (P := P) (Q := Q) (A := A) (U := U) src count tmp n) := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => exact ⟨retireDescriptorPacket_native _ _ _,ih⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
