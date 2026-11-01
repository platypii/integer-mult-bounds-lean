module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaHaloProblem
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryPlacement
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Temporarily use gather 119 for the factory publication width. The retained
metadata width at 115 and all ordinary masters remain available to the interior. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 389 Q A U}

def replicaFactoryPublicationReg (i : Fin 117) : Fin 389 :=
  if i = 115 then 119 else Fin.castLE (by decide) i

theorem replicaFactoryPublicationReg_injective : Function.Injective replicaFactoryPublicationReg := by
  intro i j he
  by_cases hi : i = 115 <;> by_cases hj : j = 115
  · exact hi.trans hj.symm
  · simp only [replicaFactoryPublicationReg,if_pos hi,if_neg hj] at he
    have hv := congrArg (fun i : Fin 389 => i.val) he
    have hb := j.isLt
    change 119 = j.val at hv
    omega
  · simp only [replicaFactoryPublicationReg,if_neg hi,if_pos hj] at he
    have hv := congrArg (fun i : Fin 389 => i.val) he
    have hb := i.isLt
    change i.val = 119 at hv
    omega
  · simp only [replicaFactoryPublicationReg,if_neg hi,if_neg hj] at he
    exact Fin.castLE_injective _ he

def generateReplicaFactoryPublicationWidth : Pr P 389 Q A U :=
  embProg replicaFactoryPublicationReg Empty.elim (generatePublicationWidth (P₀ := Empty))

theorem generateReplicaFactoryPublicationWidth_exec (H : ReplicaHaloProblem s) (buffers : ReplicaLoopBuffers A)
    (v : HS 389 Q A U) (S : Stacks 389 A)
    (headers : ReplicaLoopHeaders H replicaRecoveryCallerInterior.gather buffers S)
    (h119 : S.R 119 = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ generatePublicationWidthCost H.t H.band ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+7*generatePublicationWidthCost H.t H.band)
        depth generateReplicaFactoryPublicationWidth (mk v S) n
        (mk v' {S with R := Function.update S.R 119 (List.replicate (publicationGeometryWidth H.t H.band) tick)}) := by
  have ht : ((embStk replicaFactoryPublicationReg S).R 98).length = H.t := by
    have hh := headers.masters (98,98) (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide)
    simp only [replicaFactoryHeaderValue] at hh
    exact hh
  have hb : ((embStk replicaFactoryPublicationReg S).R 100).length = H.band := by
    have hh := headers.masters (100,100) (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide)
    simp only [replicaFactoryHeaderValue] at hh
    exact hh
  obtain ⟨v₀,n,hu,hn,he⟩ := generatePublicationWidth_exec (body := fun f : Empty => nomatch f)
    H.t H.band (embDn replicaFactoryPublicationReg v) (embStk replicaFactoryPublicationReg S) ht hb h119
    (by
      intro k hk
      have hsmall : k.val < 31 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hk
        norm_num at hk
        omega
      have hne : k ≠ 115 := by intro he; have hv := congrArg Fin.val he; norm_num at hv; omega
      change S.R (if k = 115 then 119 else Fin.castLE (by decide) k) = []
      rw [if_neg hne]
      exact headers.blank ⟨k.val,by omega⟩ hsmall)
  have hpush : mnNativePushBound 7 (generatePublicationWidth (P₀ := Empty) (Q := Q) (A := A) (U := U)) := by
    simp [generatePublicationWidth,addUnarySizes,unarySize,ldrLoop,ldrStep,ldrHalfFx,ldrBitAct,
      ucopy,umulSym,uclear,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,
      mnNativePushBound,mnActPush]
  have hw := mn_native_exec_within he 7 hpush depth
    (mnSize (mk (embDn replicaFactoryPublicationReg v) (embStk replicaFactoryPublicationReg S))+depth+
      7*generatePublicationWidthCost H.t H.band) (by omega)
  obtain ⟨v',_,hu',hex⟩ := exec_emb_ovr_within_stock (e := replicaFactoryPublicationReg)
    replicaFactoryPublicationReg_injective (body' := body) (ι := Empty.elim) (fun f => nomatch f)
    hw v rfl S rfl
  rw [embOvr_stream replicaFactoryPublicationReg replicaFactoryPublicationReg_injective] at hex
  exact ⟨v',n,hu'.trans hu,hn,hex⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
