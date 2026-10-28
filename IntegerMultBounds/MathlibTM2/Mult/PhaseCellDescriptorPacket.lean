module

public import IntegerMultBounds.MathlibTM2.Fast.PrepBase
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! Read an arbitrary length-prefixed packet and save its exact reverse. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def descriptorPacket (xs : List (Fin (A+4))) : List (Fin (A+4)) :=
  preFld xs.length ++ xs

def takeDescriptorPacket (src dst saved count tmp spare : Fin T) : Pr P T Q A U :=
  .seq (preTake src count)
    (.seq (copyR count saved tmp id)
      (.seq (.act (.push (.rt saved) (fun _ => bitSymbol false) .done))
        (.seq (copyPrefix count src dst spare tmp)
          (.seq (transfer count src saved tmp) (uclear count)))))

theorem takeDescriptorPacket_exec (src dst saved count tmp spare : Fin T)
    (hreg : [src,dst,saved,count,tmp,spare].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (xs rest : List (Fin (A+4)))
    (hsrc : S.R src = descriptorPacket xs++rest)
    (hcount : S.R count = []) (htmp : S.R tmp = []) (hspare : S.R spare = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 23*xs.length+24 ∧
      Exec body (takeDescriptorPacket src dst saved count tmp spare) (mk v S) n
        (mk v' {S with R := Function.update (Function.update (Function.update S.R src rest)
          dst (xs++S.R dst)) saved ((descriptorPacket xs).reverse++S.R saved)}) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁,S₁,n₁,hu₁,hn₁,he₁,hh₁,hframe₁⟩ :=
    preTake_runs (body := body) (tg := id) Function.injective_id ‹src ≠ count› S.R
      (by simpa only [descriptorPacket,List.append_assoc] using hsrc) v S (fun _ => rfl)
  let R₁ := Function.update (Function.update S.R src (xs++rest)) count (List.replicate xs.length tick)
  have hS₁ : S₁ = {S with R := R₁} := by
    refine Stacks.ext hframe₁.1 hframe₁.2.1 hframe₁.2.2.1 ?_
    funext i
    simpa only [R₁,hcount,List.append_nil,id_eq] using hh₁ i
  subst S₁
  let S₂ : Stacks T A := {S with R := (Function.update R₁ saved
    (((R₁ count).map id).reverse++R₁ saved))}
  obtain ⟨v₃,hu₃,he₂⟩ := copyR_exec (body := body) count saved tmp
    (Ne.symm ‹saved ≠ count›) ‹count ≠ tmp› ‹saved ≠ tmp› id v₁ {S with R := R₁}
    (by simp [R₁,htmp,Ne.symm ‹count ≠ tmp›,Ne.symm ‹src ≠ tmp›])
  let S₃ : Stacks T A := {S₂ with R := Function.update S₂.R saved (bitSymbol false::S₂.R saved)}
  have he₃ : Exec body (.act (.push (.rt saved) (fun _ => bitSymbol false) .done))
      (mk v₃ S₂) 1 (mk v₃ S₃) := by
    simpa [S₃,Action.run,update_rt] using
      (Exec.act (body := body) (.push (.rt saved) (fun _ => bitSymbol false) .done) (mk v₃ S₂))
  have hc₃ : (S₃.R count).length = xs.length := by
    simp [S₃,S₂,R₁,(Ne.symm ‹saved ≠ count›)]
  have hs₃ : S₃.R src = xs++rest := by
    simp [S₃,S₂,R₁,‹src ≠ saved›,‹src ≠ count›]
  have ht₃ : S₃.R tmp = [] := by
    simp [S₃,S₂,R₁,htmp,Ne.symm ‹saved ≠ tmp›,Ne.symm ‹count ≠ tmp›,Ne.symm ‹src ≠ tmp›]
  have hp₃ : S₃.R spare = [] := by
    simp [S₃,S₂,R₁,hspare,Ne.symm ‹saved ≠ spare›,Ne.symm ‹count ≠ spare›,Ne.symm ‹src ≠ spare›]
  obtain ⟨v₄,hu₄,he₄⟩ := copyPrefix_exec (body := body)
    (show [count,src,dst,spare,tmp].Nodup by simp_all <;> omega) v₃ S₃ xs rest hs₃ hc₃ hp₃ ht₃
  let S₄ : Stacks T A := {S₃ with R := Function.update S₃.R dst (xs++S₃.R dst)}
  obtain ⟨v₅,hu₅,he₅⟩ := transfer_exec (body := body)
    (show [count,src,saved,tmp].Nodup by simp_all <;> omega) v₄ S₄ xs rest
    (by simpa [S₄,‹src ≠ dst›] using hs₃)
    (by simpa [S₄,Ne.symm ‹dst ≠ count›] using hc₃)
    (by simpa [S₄,Ne.symm ‹dst ≠ tmp›] using ht₃)
  let S₅ : Stacks T A := {S₄ with R := Function.update (Function.update S₄.R src rest) saved (xs.reverse++S₄.R saved)}
  obtain ⟨v₆,hu₆,he₆⟩ := uclear_exec body count v₅ S₅
  have hc₂ : (R₁ count).length = xs.length := by
    simp [R₁]
  have hc₅ : (S₅.R count).length = xs.length := by
    simpa [S₅,S₄,(Ne.symm ‹saved ≠ count›),Ne.symm ‹src ≠ count›,Ne.symm ‹dst ≠ count›] using hc₃
  refine ⟨v₆,n₁+((4*(R₁ count).length+4)+(1+((10*xs.length+10)+
    ((4*xs.length+4)+(2*(S₅.R count).length+2))))),hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans hu₁))),?_,
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ he₆))))).cast rfl ?_⟩
  · rw [hc₂,hc₅]
    omega
  · apply congrArg (mk v₆)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    simp only [S₅,S₄,S₃,S₂,R₁,Function.update_apply,descriptorPacket,
      preFld,List.reverse_append,List.reverse_replicate,List.reverse_cons,List.reverse_nil,
      List.nil_append,List.singleton_append,List.map_id,hcount]
    split_ifs <;> subst_vars <;> simp_all [List.append_assoc]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
