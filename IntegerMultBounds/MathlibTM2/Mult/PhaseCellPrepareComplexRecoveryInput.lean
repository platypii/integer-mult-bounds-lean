module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizeRecoveryInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExpandComplexFields
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExpandComplexStock

/-! Produce the raw real-component archive from ordinary complex input. Local
span metadata generates the packet count; all temporary controls are erased. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {U : Type}

noncomputable def complexRecoveryInput (H : ReplicaHaloProblem s) (W : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 392 A :=
  let S := rawRecoveryInput H W Fs inp out
  {S with R := (Function.update (Function.update S.R 390 (List.replicate Fs.length tick))
    138 (List.replicate H.span tick))}

def prepareComplexRecoveryInput : Pr Empty 392 Q A U :=
  .seq (unaryProduct 138 130 139 142 143)
    (.seq (expandComplexKeyCounted 390 139 140 124 141 142 143 144)
      (.seq (uclear 138) (.seq (uclear 139) (uclear 144))))

def prepareComplexRecoveryInputCost (span W N : ℕ) : ℕ :=
  N*(26*(span*W)+19)+span*(6*W+11)+44

theorem prepareComplexRecoveryInput_exec (hA : 4 ≤ A) (H : ReplicaHaloProblem s) (W : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (hN : H.Fs.length = 2*Fs.length)
    (inp : List (Bool ⊕ Bool)) (out : List Bool) (v : HS 392 Q A U) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ prepareComplexRecoveryInputCost H.span W Fs.length ∧
      Exec (fun f : Empty => nomatch f) prepareComplexRecoveryInput
        (mk v (complexRecoveryInput H W Fs inp out)) steps
        (mk v' (rawRecoveryInput H W (complexComponentFields Fs) inp out)) := by
  let S := complexRecoveryInput (A := A) H W Fs inp out
  have hblank (k : Fin 392) (hk : 131 ≤ k.val) (h138 : k ≠ 138) (h390 : k ≠ 390) : S.R k = [] := by
    have h124 : k ≠ 124 := by intro he; subst k; norm_num at hk
    have h129 : k ≠ 129 := by intro he; subst k; norm_num at hk
    have h130 : k ≠ 130 := by intro he; subst k; norm_num at hk
    simp only [S,complexRecoveryInput,rawRecoveryInput,Function.update_of_ne h138,
      Function.update_of_ne h390,Function.update_of_ne h130,Function.update_of_ne h129,
      Function.update_of_ne h124]
    exact generatedRecoveryInput_off H inp out k (by omega) h390
  have hspan : (S.R 138).length = H.span := by simp [S,complexRecoveryInput]
  have hwidth : (S.R 130).length = W := by simp [S,complexRecoveryInput,rawRecoveryInput]
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := fun f : Empty => nomatch f)
    (show ([(138 : Fin 392),130,139,142,143]).Nodup by decide) v S
    (hblank _ (by decide) (by decide) (by decide)) (hblank _ (by decide) (by decide) (by decide))
  let S₁ : Stacks 392 A := {S with R := Function.update S.R 139 (List.replicate (H.span*W) tick)}
  have he₁' : Exec (fun f : Empty => nomatch f) (unaryProduct 138 130 139 142 143)
      (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [hspan,hwidth,hblank 139 (by decide) (by decide) (by decide),List.append_nil] using he₁
  have hn₁' : n₁ ≤ H.span*(4*W+9)+4 := by simpa only [hspan,hwidth] using hn₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := expandComplexFields_exec
    (body := fun f : Empty => nomatch f)
    (show ([(390 : Fin 392),139,140,124,141,142,143,144]).Nodup by decide)
    hA H.origin H.span W H.span_fit Fs [] v₁ S₁
    (by simp [S₁,S,complexRecoveryInput]) (by simp [S₁])
    (by simp [S₁,S,complexRecoveryInput,rawRecoveryInput])
    (by simpa [S₁] using hblank 140 (by decide) (by decide) (by decide))
    (by simpa [S₁] using hblank 141 (by decide) (by decide) (by decide))
    (by simpa [S₁] using hblank 142 (by decide) (by decide) (by decide))
    (by simpa [S₁] using hblank 143 (by decide) (by decide) (by decide))
    (by simpa [S₁] using hblank 144 (by decide) (by decide) (by decide))
  let S₂ : Stacks 392 A := {S₁ with R := (Function.update (Function.update (Function.update S₁.R
    144 (List.replicate Fs.length tick)) 124
      (cstream A W (((complexComponentFields Fs).map (packedInterval H.origin H.span)).flatten)))
    390 (List.replicate (2*Fs.length) tick))}
  have he₂' : Exec (fun f : Empty => nomatch f) (expandComplexKeyCounted 390 139 140 124 141 142 143 144)
      (mk v₁ S₁) n₂ (mk v₂ S₂) := by
    simpa [S₂,S₁,S,complexRecoveryInput,←List.replicate_add,two_mul] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (fun f : Empty => nomatch f) 138 v₂ S₂
  let S₃ : Stacks 392 A := {S₂ with R := Function.update S₂.R 138 []}
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (fun f : Empty => nomatch f) 139 v₃ S₃
  let S₄ : Stacks 392 A := {S₃ with R := Function.update S₃.R 139 []}
  obtain ⟨v₅,hu₅,he₅⟩ := uclear_exec (fun f : Empty => nomatch f) 144 v₄ S₄
  have h138 : (S₂.R 138).length = H.span := by simp [S₂,S₁,S,complexRecoveryInput]
  have h139 : (S₃.R 139).length = H.span*W := by simp [S₃,S₂,S₁]
  have h144 : (S₄.R 144).length = Fs.length := by simp [S₄,S₃,S₂]
  rw [h138] at he₃
  rw [h139] at he₄
  rw [h144] at he₅
  have hfinal : {S₄ with R := Function.update S₄.R 144 []} =
      rawRecoveryInput H W (complexComponentFields Fs) inp out := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h124 : k = 124
    · subst k; simp [S₄,S₃,S₂,S₁,S,complexRecoveryInput,rawRecoveryInput]
    by_cases h390 : k = 390
    · subst k; simp [S₄,S₃,S₂,S₁,S,complexRecoveryInput,rawRecoveryInput,generatedRecoveryInput,hN]
    by_cases h138 : k = 138
    · subst k
      simp [S₄,S₃,S₂,S₁,S,complexRecoveryInput,rawRecoveryInput,generatedRecoveryInput]
    by_cases h139 : k = 139
    · subst k
      simp [S₄,S₃,S₂,S₁,S,complexRecoveryInput,rawRecoveryInput,generatedRecoveryInput]
    by_cases h144 : k = 144
    · subst k
      simp [S₄,S₃,S₂,S₁,S,complexRecoveryInput,rawRecoveryInput,generatedRecoveryInput]
    simp only [S₄,S₃,S₂,S₁,S,complexRecoveryInput,rawRecoveryInput,
      Function.update_of_ne h144,Function.update_of_ne h139,Function.update_of_ne h138,
      Function.update_of_ne h390,Function.update_of_ne h124]
    simp only [Function.update_apply]
    split_ifs <;> rfl
  refine ⟨v₅,n₁+n₂+((2*H.span+2)+((2*(H.span*W)+2)+(2*Fs.length+2))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),?_,?_⟩
  · dsimp only [prepareComplexRecoveryInputCost]
    nlinarith only [hn₁',hn₂]
  · have he := Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄ he₅)))
    rw [hfinal] at he
    simpa only [prepareComplexRecoveryInput,Nat.add_assoc] using he

omit [NeZero s] in
theorem prepareComplexRecoveryInput_pushBound :
    mnNativePushBound 2 (prepareComplexRecoveryInput (Q := Q) (A := A) (U := U)) := by
  simp only [prepareComplexRecoveryInput,mnNativePushBound]
  refine ⟨?_,expandComplexKeyCounted_pushBound _ _ _ _ _ _ _ _,?_,?_,?_⟩
  · simp [unaryProduct,scanP,popPush,drainR,popDo,ucopy,umulSym,scanR,keepIn,pushN,
      moveR,whileR,moveStep,peekR,mnNativePushBound,mnActPush]
  all_goals simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]

omit [NeZero s] in
/-- Every intermediate configuration pays only linear local archive work over
its initial bank, including the temporary product and doubled component data. -/
theorem prepareComplexRecoveryInput_within_stock
    {v v' : HS 392 Q A U} {S G : Stacks 392 A} {steps span W N : ℕ}
    (hex : Exec (fun f : Empty => nomatch f) prepareComplexRecoveryInput
      (mk v S) steps (mk v' G))
    (hn : steps ≤ prepareComplexRecoveryInputCost span W N) (depth : ℕ) :
    ExecWithin (fun f : Empty => nomatch f)
      (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*prepareComplexRecoveryInputCost span W N)
      depth prepareComplexRecoveryInput (mk v S) steps (mk v' G) := by
  exact mn_native_exec_within hex 2 prepareComplexRecoveryInput_pushBound depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
