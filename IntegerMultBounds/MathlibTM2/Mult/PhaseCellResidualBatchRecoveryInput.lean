module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageBoundaryRealUnfold
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Borrow one folded batch result and prepare its real natural-order recovery input, preserving the factor page. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 240 Q A U}

def residualBatchRecoveryInput : Pr P 240 Q A U :=
  .seq (unaryProduct 192 160 231 232 233)
    (.seq (copyPrefix 231 224 217 232 233)
      (.seq sharedPageBoundaryRealUnfold (uclear 231)))

def residualBatchRecoveryInputCost (N w : ℕ) : ℕ :=
  generatedBoundaryUnfoldCost N w+N*(28*w+18)+28

theorem residualBatchRecoveryInputCost_le (N w : ℕ) :
    residualBatchRecoveryInputCost N w ≤ 200*(N+1)*(w+1) := by
  dsimp [residualBatchRecoveryInputCost,generatedBoundaryUnfoldCost]
  nlinarith only [Nat.zero_le (N*w)]

theorem residualBatchRecoveryInput_exec {s : ℕ} [NeZero s] (hA : 4 ≤ A) (w : ℕ)
    (B : Finset (ZMod s)) (solution : List GaussianInt) (hlen : solution.length = B.card)
    (v : HS 240 Q A U) (S : Stacks 240 A) (tail : List (Fin (A+4)))
    (hleft : ∀ i, S.L i = [])
    (hmul : ∀ i : Fin 64, (embStk sharedPageBoundaryUnfoldReg S).R (boundaryFactorMulReg i) = [])
    (hcount : (S.R 116).length = B.card) (hrows : (S.R 192).length = B.card)
    (hw : (S.R 160).length = w)
    (hsource : S.R 224 = cstream A w solution++tail)
    (h217 : S.R 217 = []) (h231 : S.R 231 = []) (h232 : S.R 232 = []) (h233 : S.R 233 = [])
    (hclean : ∀ i ∈ ([234,235,184,223,237,208,211,236,201,215] : List (Fin 240)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ residualBatchRecoveryInputCost B.card w ∧
      Exec body residualBatchRecoveryInput (mk v S) n
        (mk v' {S with R := (Function.update S.R 237
          (cstream A w ((bOrder s B).map (boundarySolutionField B solution))))}) := by
  let outerBody := body
  let raw := cstream A w solution
  let output := cstream A w ((bOrder s B).map (boundarySolutionField B solution))
  have hraw : raw.length = B.card*w := by simp [raw,hlen]
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := outerBody)
    (a := 192) (b := 160) (dst := 231) (t₁ := 232) (t₂ := 233) (by decide) v S h232 h233
  let S₁ : Stacks 240 A := {S with R := Function.update S.R 231 (List.replicate (B.card*w) tick)}
  have he₁' : Exec outerBody (unaryProduct 192 160 231 232 233) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [hrows,hw,h231,List.append_nil] using he₁
  have hn₁' : n₁ ≤ B.card*(4*w+9)+4 := by simpa only [hrows,hw] using hn₁
  obtain ⟨v₂,hu₂,he₂⟩ := copyPrefix_exec (body := outerBody) (count := 231) (src := 224) (dst := 217)
    (saved := 232) (tmp := 233) (by decide) v₁ S₁ raw tail (by simpa [S₁] using hsource)
    (by simp [S₁,hraw]) (by simpa [S₁] using h232) (by simpa [S₁] using h233)
  let S₂ : Stacks 240 A := {S₁ with R := Function.update S₁.R 217 raw}
  have he₂' : Exec outerBody (copyPrefix 231 224 217 232 233) (mk v₁ S₁) (10*raw.length+10) (mk v₂ S₂) := by
    simpa only [S₂,S₁,Function.update_of_ne (by decide : (217 : Fin 240) ≠ 231),h217,List.append_nil] using he₂
  have hm : ∀ i : Fin 64, (embStk sharedPageBoundaryUnfoldReg S₂).R (boundaryFactorMulReg i) = [] := by
    intro i
    have hreg : sharedPageBoundaryUnfoldReg (boundaryFactorMulReg i) = ⟨i.val,by omega⟩ := by
      apply Fin.ext
      have hi := i.isLt
      change (if i.val = 189 then 234 else if i.val = 191 then 235 else
        if i.val = 198 then 236 else if i.val = 204 then 237 else i.val) = i.val
      split_ifs <;> omega
    have hh := hmul i
    simpa only [embStk,Function.comp_def,hreg,S₂,S₁,
      Function.update_of_ne (by apply Fin.ne_of_val_ne; have hi := i.isLt; dsimp; omega : (⟨i.val,by omega⟩ : Fin 240) ≠ 217),
      Function.update_of_ne (by apply Fin.ne_of_val_ne; have hi := i.isLt; dsimp; omega : (⟨i.val,by omega⟩ : Fin 240) ≠ 231)] using hh
  have hc : ∀ i ∈ ([234,235,184,223,237,208,211,236,201,215] : List (Fin 240)), S₂.R i = [] := by
    intro i hi
    have ho : i ≠ 217 ∧ i ≠ 231 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [S₂,S₁,ho.1,ho.2] using hclean i hi
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := sharedPageBoundaryRealUnfold_exec (body := body) hA w B solution hlen
    v₂ S₂ hleft hm (by simpa [S₂,S₁] using hcount) (by simp [S₂,raw])
    (by simpa [S₂,S₁] using hw) hc
  let S₃ : Stacks 240 A := {S₂ with R := Function.update (Function.update S₂.R 217 []) 237 output}
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec outerBody 231 v₃ S₃
  have hclock : (S₃.R 231).length = B.card*w := by simp [S₃,S₂,S₁]
  refine ⟨v₄,n₁+((10*raw.length+10)+(n₃+(2*(S₃.R 231).length+2))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,(Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ he₄))).cast rfl ?_⟩
  · rw [hraw,hclock]
    dsimp only [residualBatchRecoveryInputCost]
    nlinarith only [hn₁',hn₃]
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi217 : i = 217 <;> by_cases hi231 : i = 231 <;> by_cases hi237 : i = 237 <;>
      simp [S₃,S₂,S₁,hi217,hi231,hi237,h217,h231,output]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
