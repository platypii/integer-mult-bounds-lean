module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairBitPlanes
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Serialize actual borrowed register contents into ordinary descriptor packets.
Length headers are generated from the live words, and scratch is restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def emitDescriptorPacket (src dst tmp saved : Fin T) : Pr P T Q A U :=
  .seq (copyMappedWords src dst tmp saved id)
    (.seq (.act (.push (.rt dst) (fun _ => bitSymbol false) .done)) (ucopy src dst saved))

theorem emitDescriptorPacket_exec (src dst tmp saved : Fin T)
    (hreg : [src,dst,tmp,saved].Nodup) (v : HS T Q A U) (S : Stacks T A)
    (htmp : S.R tmp = []) (hsaved : S.R saved = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (emitDescriptorPacket src dst tmp saved) (mk v S) (10*(S.R src).length+11)
        (mk v' {S with R := Function.update S.R dst (descriptorPacket (S.R src)++S.R dst)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := copyMappedWords_exec (body := body) src dst tmp saved hreg id v S htmp hsaved
  simp only [List.map_id] at he₁
  let M : Stacks T A := {S with R := Function.update S.R dst (S.R src++S.R dst)}
  let F : Stacks T A := {M with R := Function.update M.R dst (bitSymbol false::M.R dst)}
  have he₂ : Exec body (.act (.push (.rt dst) (fun _ => bitSymbol false) .done)) (mk v₁ M) 1 (mk v₁ F) := by
    simpa only [F,Action.run,mk,update_rt,get_rt] using Exec.act (body := body)
      (.push (.rt dst) (fun _ => bitSymbol false) .done) (mk v₁ M)
  obtain ⟨v₂,hu₂,he₃⟩ := ucopy_exec (body := body) ‹src ≠ dst› ‹src ≠ saved› ‹dst ≠ saved› v₁ F
    (by simp [F,M,‹dst ≠ saved›.symm,hsaved])
  have hsource : F.R src = S.R src := by simp [F,M,‹src ≠ dst›]
  rw [hsource] at he₃
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by omega) ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi : i = dst
  · subst i
    simp [F,M,descriptorPacket,preFld,List.append_assoc]
  · simp only [F,M,Function.update_of_ne hi]

theorem emitDescriptorPacket_native (src dst tmp saved : Fin T) :
    mnNativePushBound 2 (emitDescriptorPacket (P := P) (Q := Q) (A := A) (U := U) src dst tmp saved) := by
  simp [emitDescriptorPacket,copyMappedWords,copyR,copyStep,ucopy,umulSym,scanR,drainR,popDo,
    keepIn,pushN,moveR,whileR,moveStep,peekR,mnNativePushBound,mnActPush]

/-- Reverse allocation order prepends the fields in the loader's forward order. -/
def emitDescriptorBank (dst tmp saved : Fin T) : List (Fin T) → Pr P T Q A U
  | [] => .act .done
  | src::ports => .seq (emitDescriptorBank dst tmp saved ports) (emitDescriptorPacket src dst tmp saved)

def emitDescriptorBankCost (R : Regs T A) : List (Fin T) → ℕ
  | [] => 1
  | src::ports => emitDescriptorBankCost R ports+(10*(R src).length+11)

theorem emitDescriptorBank_exec (dst tmp saved : Fin T) (ports : List (Fin T))
    (hreg : ∀ src ∈ ports, [src,dst,tmp,saved].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (htmp : S.R tmp = []) (hsaved : S.R saved = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (emitDescriptorBank dst tmp saved ports) (mk v S) (emitDescriptorBankCost S.R ports)
        (mk v' {S with R := (Function.update S.R dst
          (descriptorBankTape (ports.map (fun i => (i,S.R i)))++S.R dst))}) := by
  induction ports generalizing v S with
  | nil =>
    refine ⟨v,rfl,?_⟩
    simpa [emitDescriptorBank,emitDescriptorBankCost,descriptorBankTape,Function.update_eq_self,Action.run] using
      Exec.act (body := body) .done (mk v S)
  | cons src ports ih =>
    have hhead := hreg src (by simp)
    have hr := hhead
    regs_ne hr
    obtain ⟨v₁,hu₁,he₁⟩ := ih (by intro i hi; exact hreg i (by simp [hi])) v S htmp hsaved
    let M : Stacks T A := {S with R := (Function.update S.R dst
      (descriptorBankTape (ports.map (fun i => (i,S.R i)))++S.R dst))}
    have hframe (i : Fin T) (hi : i ≠ dst) : M.R i = S.R i := Function.update_of_ne hi _ _
    obtain ⟨v₂,hu₂,he₂⟩ := emitDescriptorPacket_exec src dst tmp saved hhead v₁ M
      (by rw [hframe _ ‹dst ≠ tmp›.symm]; exact htmp)
      (by rw [hframe _ ‹dst ≠ saved›.symm]; exact hsaved)
    rw [hframe _ ‹src ≠ dst›] at he₂
    refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁ he₂).cast rfl ?_⟩
    apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi : i = dst
    · subst i
      simp only [Function.update_self,M,List.map_cons,descriptorBankTape,List.flatMap_cons,List.append_assoc]
    · simp only [Function.update_of_ne hi,M]

theorem emitDescriptorBank_native (dst tmp saved : Fin T) (ports : List (Fin T)) :
    mnNativePushBound 2 (emitDescriptorBank (P := P) (Q := Q) (A := A) (U := U) dst tmp saved ports) := by
  induction ports with
  | nil => exact Nat.zero_le _
  | cons src ports ih => exact ⟨ih,emitDescriptorPacket_native _ _ _ _⟩

theorem emitDescriptorBankCost_le (R : Regs T A) (ports : List (Fin T)) :
    emitDescriptorBankCost R ports ≤ 11*(descriptorBankTape (ports.map (fun i => (i,R i)))).length+1 := by
  induction ports with
  | nil => simp [emitDescriptorBankCost,descriptorBankTape]
  | cons src ports ih =>
    simp only [emitDescriptorBankCost,List.map_cons,descriptorBankTape,List.flatMap_cons,List.length_append]
    simp only [descriptorPacket,preFld,List.length_append,List.length_replicate,List.length_singleton]
    simp only [descriptorBankTape,descriptorPacket,preFld] at ih
    omega

theorem emitDescriptorBank_exec_within (dst tmp saved : Fin T) (ports : List (Fin T))
    (hreg : ∀ src ∈ ports, [src,dst,tmp,saved].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (htmp : S.R tmp = []) (hsaved : S.R saved = []) (depth : ℕ) :
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+
        22*(descriptorBankTape (ports.map (fun i => (i,S.R i)))).length+2) depth
        (emitDescriptorBank dst tmp saved ports) (mk v S) (emitDescriptorBankCost S.R ports)
        (mk v' {S with R := (Function.update S.R dst
          (descriptorBankTape (ports.map (fun i => (i,S.R i)))++S.R dst))}) := by
  obtain ⟨v',hu,he⟩ := emitDescriptorBank_exec (body := body) dst tmp saved ports hreg v S htmp hsaved
  refine ⟨v',hu,?_⟩
  apply mn_native_exec_within he 2 (emitDescriptorBank_native _ _ _ _)
  have hc := emitDescriptorBankCost_le S.R ports
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
