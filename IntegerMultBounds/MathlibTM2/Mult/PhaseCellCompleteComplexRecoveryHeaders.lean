module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComplexRecoveryHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedWeightWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWordWidth

/-! Complete the five derived recovery headers from numerical masters and
ordinary seed dimensions, preserving the original complex payload. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {U : Type}

def derivedRecoveryHeaderPorts : List (Fin 392) := [94,115,121,123,138]

noncomputable def complexRecoverySeedInput (H : ReplicaHaloProblem s) (W : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 392 A :=
  let S := complexRecoveryInput H W Fs inp out
  {S with R := fun k => if k ∈ derivedRecoveryHeaderPorts then [] else S.R k}

def recoveryHeaderGeometryReg : Fin 117 → Fin 392 := Fin.castLE (by decide)

def completeComplexRecoveryHeaders : Pr Empty 392 Q A U :=
  .seq (generateWordWidth 112 94 104)
    (.seq (placedWeightWidth recoveryHeaderGeometryReg)
      (.seq (ucopy 113 138 137) (.seq (usub 111 138 137)
        (.seq (unaryProduct 138 94 123 139 140) (generateDoubleWidth 0 390 121 137)))))

def completeComplexRecoveryHeadersCost (H : ReplicaHaloProblem s) (N : ℕ) : ℕ :=
  (8*H.precision+9)+weightWidthCost (2^15*H.p) H.precision H.wordWidth H.t H.u+
    (4*(H.origin+H.span)+4)+(4*H.origin+4)+(H.span*(4*H.wordWidth+9)+4)+(8*N+9)

theorem completeComplexRecoveryHeaders_exec (H : ReplicaHaloProblem s) (W : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (hN : H.Fs.length = 2*Fs.length)
    (inp : List (Bool ⊕ Bool)) (out : List Bool) (v : HS 392 Q A U) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ completeComplexRecoveryHeadersCost H Fs.length ∧
      Exec (fun f : Empty => nomatch f) completeComplexRecoveryHeaders
        (mk v (complexRecoverySeedInput H W Fs inp out)) steps
        (mk v' (complexRecoveryInput H W Fs inp out)) := by
  let S := complexRecoverySeedInput (A := A) H W Fs inp out
  have hword : 2*H.precision+8 = H.wordWidth := by
    unfold ReplicaHaloProblem.precision ReplicaHaloProblem.wordWidth executionPrecision executionWidth
    omega
  have hseed (k : Fin 392) : S.R k = if k ∈ derivedRecoveryHeaderPorts then [] else
      if k = 124 then cstream A W (Fs.map (packedInterval H.origin H.span)).flatten
      else List.replicate (complexRecoveryHeader H W Fs.length k) tick := by
    simp only [S,complexRecoverySeedInput,complexRecoveryInput_right]
  have hblank (k : Fin 392) (hk : k ∉ complexRecoveryHeaderPorts) (h124 : k ≠ 124) : S.R k = [] := by
    rw [hseed]
    simp only [h124,ite_false,complexRecoveryHeader_off H W Fs.length k hk,List.replicate_zero]
    split_ifs <;> rfl
  have hvalue (k : Fin 392) (hk : k ∉ derivedRecoveryHeaderPorts) (h124 : k ≠ 124) :
      (S.R k).length = complexRecoveryHeader H W Fs.length k := by
    simp only [hseed,hk,h124,ite_false,List.length_replicate]
  obtain ⟨v₁,hu₁,he₁⟩ := generateWordWidth_exec (body := fun f : Empty => nomatch f)
    (show ([(112 : Fin 392),94,104]).Nodup by decide) H.precision v S
    (by simpa [complexRecoveryHeader,generatedRecoveryHeader,replicaFactoryHeaderValue] using hvalue 112 (by decide) (by decide))
    (by simp only [hseed,derivedRecoveryHeaderPorts,List.mem_cons,eq_self,true_or,ite_true])
    (hblank _ (by decide) (by decide))
  rw [hword] at he₁
  let S₁ : Stacks 392 A := {S with R := Function.update S.R 94 (List.replicate H.wordWidth tick)}
  have hF (k : Fin 392) (hk : k ≠ 94) : S₁.R k = S.R k := Function.update_of_ne hk _ _
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := placedWeightWidth_exec_within (body := fun f : Empty => nomatch f)
    recoveryHeaderGeometryReg (by intro i j he; exact Fin.ext (congrArg (fun k : Fin 392 => k.val) he))
    (2^15*H.p) H.precision H.wordWidth H.t H.u v₁ S₁
    (by rw [hF _ (by decide)]; simpa [recoveryHeaderGeometryReg,complexRecoveryHeader,generatedRecoveryHeader,replicaFactoryHeaderValue] using hvalue 114 (by decide) (by decide))
    (by rw [hF _ (by decide)]; simpa [recoveryHeaderGeometryReg,complexRecoveryHeader,generatedRecoveryHeader,replicaFactoryHeaderValue] using hvalue 112 (by decide) (by decide))
    (by change (S₁.R 94).length = H.wordWidth; simp [S₁])
    (by rw [hF _ (by decide)]; simpa [recoveryHeaderGeometryReg,complexRecoveryHeader,generatedRecoveryHeader,replicaFactoryHeaderValue] using hvalue 98 (by decide) (by decide))
    (by rw [hF _ (by decide)]; simpa [recoveryHeaderGeometryReg,complexRecoveryHeader,generatedRecoveryHeader,replicaFactoryHeaderValue] using hvalue 99 (by decide) (by decide))
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals rw [hF _ (by decide)]
      all_goals first
        | exact hblank _ (by decide) (by decide)
        | simp [hseed,recoveryHeaderGeometryReg,derivedRecoveryHeaderPorts]) 0
  let S₂ : Stacks 392 A := {S₁ with R := Function.update S₁.R 115 (List.replicate H.metadataWidth tick)}
  have he₂' : Exec (fun f : Empty => nomatch f) (placedWeightWidth recoveryHeaderGeometryReg)
      (mk v₁ S₁) n₂ (mk v₂ S₂) := he₂.toExec
  obtain ⟨v₃,hu₃,he₃⟩ := ucopy_exec (body := fun f : Empty => nomatch f) (a := 113) (b := 138) (t := 137)
    (show (113 : Fin 392) ≠ 138 by decide) (by decide) (by decide) v₂ S₂
    (by simpa [S₂,S₁,Function.update_of_ne (by decide : (137 : Fin 392) ≠ 115),Function.update_of_ne (by decide : (137 : Fin 392) ≠ 94)] using hblank 137 (by decide) (by decide))
  let S₃ : Stacks 392 A := {S₂ with R := Function.update S₂.R 138 (List.replicate (H.origin+H.span) tick)}
  have h113 : (S₂.R 113).length = H.origin+H.span := by
    simpa [S₂,S₁,Function.update_of_ne (by decide : (113 : Fin 392) ≠ 115),Function.update_of_ne (by decide : (113 : Fin 392) ≠ 94),complexRecoveryHeader,generatedRecoveryHeader] using hvalue 113 (by decide) (by decide)
  have he₃' : Exec (fun f : Empty => nomatch f) (ucopy 113 138 137) (mk v₂ S₂) (4*(H.origin+H.span)+4) (mk v₃ S₃) := by
    have h138 : S₂.R 138 = [] := by simp [S₂,S₁,hseed,derivedRecoveryHeaderPorts]
    simpa only [h113,h138,List.append_nil] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := usub_exec (body := fun f : Empty => nomatch f) (a := 111) (b := 138) (t := 137)
    (show (111 : Fin 392) ≠ 138 by decide) (by decide) (by decide) v₃ S₃
    (by simpa [S₃,S₂,S₁] using hblank 137 (by decide) (by decide))
  let S₄ : Stacks 392 A := {S₃ with R := Function.update S₃.R 138 (List.replicate H.span tick)}
  have h111 : (S₃.R 111).length = H.origin := by
    simpa [S₃,S₂,S₁,complexRecoveryHeader,generatedRecoveryHeader] using hvalue 111 (by decide) (by decide)
  have he₄' : Exec (fun f : Empty => nomatch f) (usub 111 138 137) (mk v₃ S₃) (4*H.origin+4) (mk v₄ S₄) := by
    rw [h111] at he₄
    simpa [S₄,S₃] using he₄
  obtain ⟨v₅,n₅,hu₅,hn₅,he₅⟩ := unaryProduct_exec (body := fun f : Empty => nomatch f)
    (show ([(138 : Fin 392),94,123,139,140]).Nodup by decide) v₄ S₄
    (by simpa [S₄,S₃,S₂,S₁] using hblank 139 (by decide) (by decide))
    (by simpa [S₄,S₃,S₂,S₁] using hblank 140 (by decide) (by decide))
  let S₅ : Stacks 392 A := {S₄ with R := Function.update S₄.R 123 (List.replicate (H.span*H.wordWidth) tick)}
  have hspan : (S₄.R 138).length = H.span := by simp [S₄]
  have hwidth : (S₄.R 94).length = H.wordWidth := by simp [S₄,S₃,S₂,S₁]
  have he₅' : Exec (fun f : Empty => nomatch f) (unaryProduct 138 94 123 139 140)
      (mk v₄ S₄) n₅ (mk v₅ S₅) := by
    simpa [hspan,hwidth,S₅,S₄,S₃,S₂,S₁,hseed,derivedRecoveryHeaderPorts] using he₅
  have hn₅' : n₅ ≤ H.span*(4*H.wordWidth+9)+4 := by simpa [hspan,hwidth] using hn₅
  obtain ⟨v₆,hu₆,he₆⟩ := generateDoubleWidth_exec (body := fun f : Empty => nomatch f)
    (show ([(390 : Fin 392),121,137]).Nodup by decide) Fs.length 0 v₅ S₅
    (by simpa [S₅,S₄,S₃,S₂,S₁,complexRecoveryHeader] using hvalue 390 (by decide) (by decide))
    (by simp [S₅,S₄,S₃,S₂,S₁,hseed,derivedRecoveryHeaderPorts])
    (by simpa [S₅,S₄,S₃,S₂,S₁] using hblank 137 (by decide) (by decide))
  have hfinal : {S₅ with R := Function.update S₅.R 121 (List.replicate (2*Fs.length+0) tick)} =
      complexRecoveryInput H W Fs inp out := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp only [S₅,S₄,S₃,S₂,S₁,S,complexRecoverySeedInput,Function.update_apply]
    by_cases h121 : k = 121
    · subst k; simp [complexRecoveryInput_right,complexRecoveryHeader,generatedRecoveryHeader,replicaFactoryHeaderValue,hN]
    by_cases h123 : k = 123
    · subst k; simp [h121,complexRecoveryInput_right,complexRecoveryHeader,generatedRecoveryHeader]
    by_cases h138 : k = 138
    · subst k; simp [h121,h123,complexRecoveryInput_right,complexRecoveryHeader]
    by_cases h115 : k = 115
    · subst k; simp [h121,h123,h138,complexRecoveryInput_right,complexRecoveryHeader,generatedRecoveryHeader]
    by_cases h94 : k = 94
    · subst k; simp [h121,h123,h138,h115,complexRecoveryInput_right,complexRecoveryHeader,generatedRecoveryHeader,replicaFactoryHeaderValue]
    · simp only [h121,h123,h138,h115,h94,ite_false,derivedRecoveryHeaderPorts,List.mem_cons,List.not_mem_nil,or_false]
  rw [hfinal] at he₆
  refine ⟨v₆,(8*H.precision+9)+(n₂+((4*(H.origin+H.span)+4)+((4*H.origin+4)+(n₅+(8*Fs.length+9))))),
    hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))),?_,?_⟩
  · dsimp only [completeComplexRecoveryHeadersCost]
    omega
  · exact Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄' (Exec.seq he₅' he₆))))

omit [NeZero s] in
theorem completeComplexRecoveryHeaders_pushBound :
    mnNativePushBound 18 (completeComplexRecoveryHeaders (Q := Q) (A := A) (U := U)) := by
  simp only [completeComplexRecoveryHeaders,mnNativePushBound]
  refine ⟨?_,embProg_native _ Empty.elim _ generateWeightWidth_native,?_,?_,?_,?_⟩
  all_goals simp [generateWordWidth,generateDoubleWidth,ucopy,usub,dropTop,unaryProduct,
    scanP,popPush,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,whileR,moveStep,peekR,
    mnNativePushBound,mnActPush]

omit [NeZero s] in
/-- Header generation has a local native trace; its scratch is charged over the
whole initial bank, including the borrowed masters and original payload. -/
theorem completeComplexRecoveryHeaders_within_stock {H : ReplicaHaloProblem s} {N : ℕ}
    {v v' : HS 392 Q A U} {S F : Stacks 392 A} {steps : ℕ}
    (hex : Exec (fun f : Empty => nomatch f) completeComplexRecoveryHeaders
      (mk v S) steps (mk v' F))
    (hn : steps ≤ completeComplexRecoveryHeadersCost H N) (depth : ℕ) :
    ExecWithin (fun f : Empty => nomatch f)
      (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+18*completeComplexRecoveryHeadersCost H N)
      depth completeComplexRecoveryHeaders (mk v S) steps (mk v' F) := by
  exact mn_native_exec_within hex 18 completeComplexRecoveryHeaders_pushBound depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
