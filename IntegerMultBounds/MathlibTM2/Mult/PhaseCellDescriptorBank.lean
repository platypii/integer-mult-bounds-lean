module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorPacket

/-! A fixed list of destination ports reads one variable-size descriptor bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def descriptorBankTape (fields : List (Fin T × List (Fin (A+4)))) : List (Fin (A+4)) :=
  fields.flatMap (fun f => descriptorPacket f.2)

def descriptorBankR : List (Fin T × List (Fin (A+4))) → Regs T A → Regs T A
  | [], R => R
  | (dst,xs)::fields, R => descriptorBankR fields (Function.update R dst (xs++R dst))

theorem descriptorBankR_frame (fields : List (Fin T × List (Fin (A+4))))
    (R : Regs T A) (k : Fin T) (hk : ∀ f ∈ fields, f.1 ≠ k) :
    descriptorBankR fields R k = R k := by
  induction fields generalizing R with
  | nil => rfl
  | cons f fields ih =>
    obtain ⟨dst,xs⟩ := f
    rw [descriptorBankR,ih _ (fun f hf => hk f (by simp [hf]))]
    exact Function.update_of_ne (hk (dst,xs) (by simp)).symm _ _

theorem descriptorBankR_update (fields : List (Fin T × List (Fin (A+4))))
    (R : Regs T A) (k : Fin T) (xs : List (Fin (A+4)))
    (hk : ∀ f ∈ fields, f.1 ≠ k) :
    descriptorBankR fields (Function.update R k xs) = Function.update (descriptorBankR fields R) k xs := by
  induction fields generalizing R with
  | nil => rfl
  | cons f fields ih =>
    obtain ⟨dst,ys⟩ := f
    have hdst : dst ≠ k := hk (dst,ys) (by simp)
    simp only [descriptorBankR,Function.update_of_ne hdst]
    rw [Function.update_comm hdst.symm,ih _ (fun f hf => hk f (by simp [hf]))]

def takeDescriptorBank (src saved count tmp spare : Fin T) : List (Fin T) → Pr P T Q A U
  | [] => .act .done
  | dst::ds => .seq (takeDescriptorPacket src dst saved count tmp spare)
      (takeDescriptorBank src saved count tmp spare ds)

def takeDescriptorBankCost (fields : List (Fin T × List (Fin (A+4)))) : ℕ :=
  (fields.map (fun f => 23*f.2.length+24)).sum+1

theorem takeDescriptorBank_exec (src saved count tmp spare : Fin T)
    (hreg : [src,saved,count,tmp,spare].Nodup)
    (fields : List (Fin T × List (Fin (A+4))))
    (hfields : ∀ f ∈ fields, f.1 ∉ [src,saved,count,tmp,spare])
    (v : HS T Q A U) (S : Stacks T A) (rest : List (Fin (A+4)))
    (hsrc : S.R src = descriptorBankTape fields++rest)
    (hcount : S.R count = []) (htmp : S.R tmp = []) (hspare : S.R spare = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ takeDescriptorBankCost fields ∧
      Exec body (takeDescriptorBank src saved count tmp spare (fields.map Prod.fst)) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (descriptorBankR fields S.R) src rest)
          saved ((descriptorBankTape fields).reverse++S.R saved))}) := by
  induction fields generalizing v S with
  | nil =>
    have hfinal : ({S with R := Function.update (Function.update S.R src rest) saved (S.R saved)} : Stacks T A) = S := by
      simp only [descriptorBankTape,List.flatMap_nil,List.nil_append] at hsrc
      rw [← hsrc,Function.update_eq_self,Function.update_eq_self]
    refine ⟨v,1,rfl,by simp [takeDescriptorBankCost],?_⟩
    simpa only [List.map_nil,takeDescriptorBank,descriptorBankR,descriptorBankTape,
      List.flatMap_nil,List.reverse_nil,List.nil_append,hfinal,Action.run] using
      (Exec.act (body := body) .done (mk v S))
  | cons f fields ih =>
    obtain ⟨dst,xs⟩ := f
    have hd : dst ∉ [src,saved,count,tmp,spare] := hfields (dst,xs) (by simp)
    have hf : ∀ f ∈ fields, f.1 ∉ [src,saved,count,tmp,spare] := fun f hm => hfields f (by simp [hm])
    have hdst : [src,dst,saved,count,tmp,spare].Nodup :=
      (List.Perm.swap src dst [saved,count,tmp,spare]).nodup_iff.mp (List.nodup_cons.mpr ⟨hd,hreg⟩)
    have hr := hreg
    regs_ne hr
    have hdsep : dst ≠ src ∧ dst ≠ saved ∧ dst ≠ count ∧ dst ≠ tmp ∧ dst ≠ spare := by
      simpa only [List.mem_cons,List.not_mem_nil,or_false,not_or] using hd
    obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := takeDescriptorPacket_exec (body := body)
      src dst saved count tmp spare hdst v S xs (descriptorBankTape fields++rest)
      (by simpa only [descriptorBankTape,List.flatMap_cons,List.append_assoc] using hsrc) hcount htmp hspare
    let S₁ : Stacks T A := {S with R := (Function.update (Function.update (Function.update S.R src
      (descriptorBankTape fields++rest)) dst (xs++S.R dst)) saved ((descriptorPacket xs).reverse++S.R saved))}
    have hn : src ≠ saved ∧ count ≠ saved ∧ tmp ≠ saved ∧ spare ≠ saved ∧
        count ≠ src ∧ tmp ≠ src ∧ spare ≠ src ∧ count ≠ dst ∧ tmp ≠ dst ∧ spare ≠ dst := by
      exact ⟨‹src ≠ saved›,(Ne.symm ‹saved ≠ count›),(Ne.symm ‹saved ≠ tmp›),
        (Ne.symm ‹saved ≠ spare›),(Ne.symm ‹src ≠ count›),(Ne.symm ‹src ≠ tmp›),
        (Ne.symm ‹src ≠ spare›),hdsep.2.2.1.symm,hdsep.2.2.2.1.symm,hdsep.2.2.2.2.symm⟩
    obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := ih hf v₁ S₁
      (by simp [S₁,hn.1,hdsep.1.symm])
      (by simp [S₁,hn,hcount]) (by simp [S₁,hn,htmp]) (by simp [S₁,hn,hspare])
    have hsep (k : Fin T) (hk : k ∈ [src,saved,count,tmp,spare]) : ∀ f ∈ fields, f.1 ≠ k := by
      intro f hm he
      exact hf f hm (he ▸ hk)
    refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl ?_⟩
    · simp only [takeDescriptorBankCost,List.map_cons,List.sum_cons] at hn₂ ⊢
      omega
    · apply congrArg (mk v₂)
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      have hdsrc : dst ≠ src := by
        intro he; exact hd (by simp [he])
      have hdsaved : dst ≠ saved := by
        intro he; exact hd (by simp [he])
      simp only [S₁,descriptorBankTape,List.flatMap_cons,List.reverse_append,descriptorBankR]
      rw [descriptorBankR_update fields _ saved _ (hsep saved (by simp))]
      rw [Function.update_comm (Ne.symm hdsrc)]
      rw [descriptorBankR_update fields _ src _ (hsep src (by simp))]
      simp only [Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all [List.append_assoc]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
