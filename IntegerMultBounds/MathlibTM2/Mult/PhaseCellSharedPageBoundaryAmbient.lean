module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResidualBatchRecoveryInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPagePublicationControls

/-! Publish one borrowed batch result in ambient coordinates while preserving the entire shared page and batch stream. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 240 Q A U}

def sharedPageBoundaryAmbient : Pr P 240 Q A U :=
  .seq residualBatchRecoveryInput sharedPageControlledScatter

def sharedPageBoundaryAmbientCost (N w s : ℕ) : ℕ :=
  residualBatchRecoveryInputCost N w+89*s*w+41

theorem sharedPageBoundaryAmbientCost_le (N w s : ℕ) (hN : N ≤ s) :
    sharedPageBoundaryAmbientCost N w s ≤ 400*(s+1)*(w+1) := by
  have hconvert := residualBatchRecoveryInputCost_le N w
  have hrows : 200*(N+1)*(w+1) ≤ 200*(s+1)*(w+1) := by gcongr
  have hbound := hconvert.trans hrows
  dsimp only [sharedPageBoundaryAmbientCost]
  nlinarith only [hbound,Nat.zero_le (s*w)]

private theorem scatter_restore {A : ℕ} (S : Stacks 240 A)
    (natural output : List (Fin (A+4))) (h237 : S.R 237 = []) :
    let S₁ : Stacks 240 A := {S with R := Function.update S.R 237 natural}
    {S₁ with R := (Function.update (Function.update S₁.R 237 []) 132 (output++S₁.R 132))} =
      {S with R := Function.update S.R 132 (output++S.R 132)} := by
  dsimp only
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi132 : i = 132 <;> by_cases hi237 : i = 237 <;> simp [hi132,hi237,h237]

theorem sharedPageBoundaryAmbient_exec (hA : 4 ≤ A) (s : ℕ) [NeZero s]
    (B : Finset (ZMod s)) (w : ℕ) (hw : 1 ≤ w)
    (solution : List GaussianInt) (hlen : solution.length = B.card)
    (v : HS 240 Q A U) (S : Stacks 240 A) (tail borrowed : List (Fin (A+4)))
    (hleft : ∀ i, S.L i = [])
    (hmul : ∀ i : Fin 64, S.R ⟨i.val,by omega⟩ = [])
    (hc : S.R 116 = List.replicate B.card tick) (hrows : (S.R 192).length = B.card)
    (hwidth : (S.R 160).length = w) (hs : (S.R 121).length = s)
    (hadv : S.R 239 = gatherControls A (originAdvances w 0 (boundaryScatterOrigins s B)++[0])++borrowed)
    (hsource : S.R 224 = cstream A w solution++tail)
    (hclean : ∀ i ∈ ([184,217,223,201,208,211,215,220,231,232,233,234,235,236,237] : List (Fin 240)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ sharedPageBoundaryAmbientCost B.card w s ∧
      Exec body sharedPageBoundaryAmbient (mk v S) n
        (mk v' {S with R := (Function.update S.R 132
          (cstream A w (chirpLine s (boundarySolutionField B solution))++S.R 132))}) ∧
      ∀ (q : ℕ) (x : ZMod s → ℝ) (ε : ℝ), (∀ z ∈ solution, Fits w z) →
        (∀ i < B.card, ‖value q (solution.getD i 0) - (x (bFoldAt s B i) : ℂ)‖ ≤ ε) →
        PhaseCellInterface.ErrorOn B
          (fun i => publishedCellRead q w (0 : ZMod s)
            (cstream A w (chirpLine s (boundarySolutionField B solution))++S.R 132) i) x ε := by
  let G := boundarySolutionField B solution
  let natural := cstream A w ((bOrder s B).map G)
  have hm₁ : ∀ i : Fin 64, (embStk sharedPageBoundaryUnfoldReg S).R (boundaryFactorMulReg i) = [] := by
    intro i
    have hr : sharedPageBoundaryUnfoldReg (boundaryFactorMulReg i) = ⟨i.val,by omega⟩ := by
      apply Fin.ext
      have hi := i.isLt
      dsimp [sharedPageBoundaryUnfoldReg,boundaryFactorMulReg]
      split_ifs <;> omega
    simpa only [embStk,Function.comp_def,hr] using hmul i
  have hc₁ : ∀ i ∈ ([234,235,184,223,237,208,211,236,201,215] : List (Fin 240)), S.R i = [] := by
    intro i hi
    apply hclean
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    tauto
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := residualBatchRecoveryInput_exec (body := body) hA w B solution hlen
    v S tail hleft hm₁ (by rw [hc]; simp) hrows hwidth hsource
    (hclean _ (by simp)) (hclean _ (by simp)) (hclean _ (by simp)) (hclean _ (by simp)) hc₁
  let S₁ : Stacks 240 A := {S with R := Function.update S.R 237 natural}
  have hc₃ : ∀ i ∈ ([184,217,223,201,208,211,215,220] : List (Fin 240)), S₁.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [S₁] using hclean _ (by simp)
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := sharedPageControlledScatter_exec (body := body) s B w hw G
    (fun i hi => boundarySolutionField_off B solution i hi) [] borrowed v₁ S₁
    (by simpa [S₁] using hs) (by simpa [S₁] using hwidth) (by simpa [S₁] using hc)
    (by simpa [S₁] using hadv) (by simp [S₁,natural]) hc₃
  refine ⟨v₃,n₁+n₃,hu₃.trans hu₁,?_,
    (Exec.seq he₁ he₃).cast rfl ?_,?_⟩
  · dsimp only [sharedPageBoundaryAmbientCost]
    omega
  · apply congrArg (mk v₃)
    exact scatter_restore S natural _ (hclean 237 (by simp))
  · intro q x ε hfit herror i hi
    dsimp only
    rw [boundarySolutionField_published_read A q w hA hw B solution hlen hfit (S.R 132) i]
    simpa only [Real.norm_eq_abs] using boundarySolutionField_error q B solution x ε herror i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
