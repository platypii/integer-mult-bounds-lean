module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResidualBatchRecoveryInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPagePackedPublication

/-! Publish one borrowed batch result in ambient coordinates while preserving the entire shared page and batch stream. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 240 Q A U}

def sharedPageBoundaryPacked : Pr P 240 Q A U :=
  .seq residualBatchRecoveryInput sharedPageControlledPackedScatter

def sharedPageBoundaryPackedCost (N w s : ℕ) : ℕ :=
  residualBatchRecoveryInputCost N w+89*s*w+41

theorem sharedPageBoundaryPackedCost_le (N w s : ℕ) (hN : N ≤ s) :
    sharedPageBoundaryPackedCost N w s ≤ 400*(s+1)*(w+1) := by
  have hconvert := residualBatchRecoveryInputCost_le N w
  have hrows : 200*(N+1)*(w+1) ≤ 200*(s+1)*(w+1) := by gcongr
  have hbound := hconvert.trans hrows
  dsimp only [sharedPageBoundaryPackedCost]
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

theorem sharedPageBoundaryPacked_exec (hA : 4 ≤ A) (s : ℕ) [NeZero s]
    (B : Finset (ZMod s)) (a L w : ℕ) (hw : 1 ≤ w)
    (hfit : a+L ≤ s) (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+L)
    (solution : List GaussianInt) (hlen : solution.length = B.card)
    (v : HS 240 Q A U) (S : Stacks 240 A) (tail borrowed : List (Fin (A+4)))
    (hleft : ∀ i, S.L i = [])
    (hmul : ∀ i : Fin 64, S.R ⟨i.val,by omega⟩ = [])
    (hc : S.R 116 = List.replicate B.card tick) (hrows : (S.R 192).length = B.card)
    (hwidth : (S.R 160).length = w) (hs : (S.R 222).length = L)
    (hadv : S.R 239 = gatherControls A (originAdvances w 0 (packedBoundaryOrigins B a)++[0])++borrowed)
    (hsource : S.R 224 = cstream A w solution++tail)
    (hclean : ∀ i ∈ ([184,217,223,201,208,211,215,220,231,232,233,234,235,236,237] : List (Fin 240)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ sharedPageBoundaryPackedCost B.card w L ∧
      Exec body sharedPageBoundaryPacked (mk v S) n
        (mk v' {S with R := (Function.update S.R 132
          (cstream A w (packedInterval a L (boundarySolutionField B solution))++S.R 132))}) := by
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
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := sharedPageControlledPackedScatter_exec (body := body) s B a L w hw hfit hB G
    (fun i hi => boundarySolutionField_off B solution i hi) [] borrowed v₁ S₁
    (by simpa [S₁] using hs) (by simpa [S₁] using hwidth) (by simpa [S₁] using hc)
    (by simpa [S₁] using hadv) (by simp [S₁,natural]) hc₃
  refine ⟨v₃,n₁+n₃,hu₃.trans hu₁,?_,
    (Exec.seq he₁ he₃).cast rfl ?_⟩
  · dsimp only [sharedPageBoundaryPackedCost]
    omega
  · apply congrArg (mk v₃)
    exact scatter_restore S natural _ (hclean 237 (by simp))


/-- Packed physical recovery has the same boundary error as the solved list. -/
theorem boundarySolutionField_packed_error {s : ℕ} [NeZero s] (A q w a L : ℕ)
    (hA : 4 ≤ A) (hw : 0 < w) (hfit : a+L ≤ s)
    (B : Finset (ZMod s)) (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+L)
    (solution : List GaussianInt) (hlen : solution.length = B.card)
    (hwords : ∀ z ∈ solution, Fits w z) (tail : List (Fin (A+4)))
    (x : ZMod s → ℝ) (ε : ℝ)
    (herror : ∀ i < B.card, ‖value q (solution.getD i 0)-(x (bFoldAt s B i) : ℂ)‖ ≤ ε) :
    PhaseCellInterface.ErrorOn B
      (fun i => (packedIntervalRead q w a
        (cstream A w (packedInterval a L (boundarySolutionField B solution))++tail) i).re) x ε := by
  intro i hi
  dsimp only
  rw [packedIntervalRead_eq q w a L _ tail [] hfit i (hB i hi).1 (hB i hi).2,
    pairedCellRead_encodedField hA hw _ [] i
      (boundarySolutionField_fits w B solution hlen hwords i)]
  simpa only [Real.norm_eq_abs] using boundarySolutionField_error q B solution x ε herror i hi

theorem sharedPageBoundaryPacked_spec (hA : 4 ≤ A) (s : ℕ) [NeZero s]
    (B : Finset (ZMod s)) (a L w : ℕ) (hw : 1 ≤ w)
    (hfit : a+L ≤ s) (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+L)
    (solution : List GaussianInt) (hlen : solution.length = B.card)
    (v : HS 240 Q A U) (S : Stacks 240 A) (tail borrowed : List (Fin (A+4)))
    (hleft : ∀ i, S.L i = [])
    (hmul : ∀ i : Fin 64, S.R ⟨i.val,by omega⟩ = [])
    (hc : S.R 116 = List.replicate B.card tick) (hrows : (S.R 192).length = B.card)
    (hwidth : (S.R 160).length = w) (hs : (S.R 222).length = L)
    (hadv : S.R 239 = gatherControls A (originAdvances w 0 (packedBoundaryOrigins B a)++[0])++borrowed)
    (hsource : S.R 224 = cstream A w solution++tail)
    (hclean : ∀ i ∈ ([184,217,223,201,208,211,215,220,231,232,233,234,235,236,237] : List (Fin 240)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ sharedPageBoundaryPackedCost B.card w L ∧
      Exec body sharedPageBoundaryPacked (mk v S) n
        (mk v' {S with R := (Function.update S.R 132
          (cstream A w (packedInterval a L (boundarySolutionField B solution))++S.R 132))}) ∧
      ∀ (q : ℕ) (x : ZMod s → ℝ) (ε : ℝ),
        (∀ z ∈ solution, Fits w z) →
        (∀ i < B.card, ‖value q (solution.getD i 0)-(x (bFoldAt s B i) : ℂ)‖ ≤ ε) →
        PhaseCellInterface.ErrorOn B
          (fun i => (packedIntervalRead q w a
            (cstream A w (packedInterval a L (boundarySolutionField B solution))++S.R 132) i).re) x ε := by
  obtain ⟨v',n,hu,hn,he⟩ := sharedPageBoundaryPacked_exec (body := body) hA s B a L w hw
    hfit hB solution hlen v S tail borrowed hleft hmul hc hrows hwidth hs hadv hsource hclean
  refine ⟨v',n,hu,hn,he,?_⟩
  intro q x ε hwords herror
  exact boundarySolutionField_packed_error A q w a L hA (by omega) hfit B hB solution hlen
    hwords (S.R 132) x ε herror

theorem boundarySolutionField_packed_published_error {s : ℕ} [NeZero s] (A q w a L : ℕ)
    (hA : 4 ≤ A) (hw : 0 < w) (hfit : a+L ≤ s) (ha : a < s)
    (B : Finset (ZMod s)) (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+L)
    (solution : List GaussianInt) (hlen : solution.length = B.card)
    (hwords : ∀ z ∈ solution, Fits w z) (tail : List (Fin (A+4)))
    (x : ZMod s → ℝ) (ε : ℝ)
    (herror : ∀ i < B.card, ‖value q (solution.getD i 0)-(x (bFoldAt s B i) : ℂ)‖ ≤ ε) :
    PhaseCellInterface.ErrorOn B
      (publishedCellRead q w (a : ZMod s)
        (cstream A w (packedInterval a L (boundarySolutionField B solution))++tail)) x ε := by
  have hh := boundarySolutionField_packed_error A q w a L hA hw hfit B hB solution hlen hwords tail x ε herror
  intro i hi
  have he := hh i hi
  dsimp only at he
  rw [packedIntervalRead_re q w a ha] at he
  exact he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
