module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedResidualBatchWorkspace

/-! One batch step archives its borrowed RHS, solves on the shared page and archives the output in source order. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.BandFactor

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

theorem preparedResidualBatchStep_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (p u l target rhsExp : ℕ) {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hp : 2 ≤ p) (hlen : columns.length = B.card) :
    let bits := boundaryTableBits p target rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    let AZ := factorRankIntegerMatrix B W columns
    let Lc := naturalLineLc q K W B.card AZ
    let Uc := naturalLineUc q K W B.card AZ
    let rcs := naturalLineRcs q K W B.card AZ
    ColumnFamilyFormat w columns →
    StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card)
      (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^bits))
      (2+(B.card : ℝ)*(1/(2 : ℝ)^bits)) →
    ∀ (b : List GaussianInt), b.length = B.card →
    (∀ x ∈ b, |gv q x.re| ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp)
      (8*p+1) (couplingCountExponent p u) ∧ |gv q x.im| ≤
      (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u)) →
    ∀ (v : HS 234 Q A U) (S : Stacks 234 A) (tail : List (Fin (A+4))),
    let T := embStk preparedBoundaryBatchCoreReg S
    let σ := boundaryFactorState (embStk preparedBoundaryCoreReg T)
    (∀ i, (embStk preparedBoundaryCoreReg T).L i = []) →
    (∀ i : Fin 64, (embStk preparedBoundaryCoreReg T).R (boundaryFactorMulReg i) = []) →
    BoundarySolveReady σ q w W B.card →
    σ .bo = cstream A w (Lc.map colC).flatten →
    σ .hf = cstream A w (Uc.map colC).flatten →
    σ .df = cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt)) →
    (S.R 119).length = q → S.R 223 = [] → S.R 184 = [] → S.R 220 = [] → S.R 221 = [] →
    S.R 206 = [] → S.R 225 = [] → S.R 232 = [] → S.R 233 = [] →
    (S.R 231).length = B.card*w → S.R 226 = cstream A w b++tail →
    ∃ v' n, v'.user = v.user ∧ n ≤ preparedResidualBatchStepCost q w B.card W ∧
      Exec (embTab preparedBoundaryBatchCoreReg (embTab preparedBoundaryCoreReg body))
        (preparedResidualBatchStep hQ) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 226 tail)
          227 ((cstream A w b).reverse++S.R 227)) 228
            ((cstream A w ((bandSolveVec q W Lc Uc rcs (b.map (normalizeBoundaryWord q (q/2-1)))).map (unscaleBoundaryWord q))).reverse++S.R 228))}) := by
  dsimp only
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let K := factorNewtonSteps p q
  let AZ := factorRankIntegerMatrix B W columns
  let Lc := naturalLineLc q K W B.card AZ
  let Uc := naturalLineUc q K W B.card AZ
  let rcs := naturalLineRcs q K W B.card AZ
  intro hformat hstage b hb hbound v S tail hleft hmul hready hbo hhf hdf hmaster h223 h184 h220 h221 h206 h225 h232 h233 hclock hsource
  let raw := cstream A w b
  let ys := cstream A w ((bandSolveVec q W Lc Uc rcs (b.map (normalizeBoundaryWord q (q/2-1)))).map (unscaleBoundaryWord q))
  let outerBody := embTab preparedBoundaryBatchCoreReg (embTab preparedBoundaryCoreReg body)
  have hrawLen : raw.length = B.card*w := by simp [raw,hb]
  have hsolLen : ((bandSolveVec q W Lc Uc rcs (b.map (normalizeBoundaryWord q (q/2-1)))).map (unscaleBoundaryWord q)).length = B.card := by
    simpa only [List.length_map] using naturalLineSolve_length q K W B.card AZ
      (b.map (normalizeBoundaryWord q (q/2-1))) (by simp [hb])
  have hysLen : ys.length = B.card*w := by
    simp only [ys,length_cstream,hsolLen]
  obtain ⟨v₁,hu₁,he₁⟩ := copyPrefix_exec (body := outerBody) (count := 231) (src := 226) (dst := 206)
    (saved := 232) (tmp := 233) (by decide) v S raw tail hsource (hclock.trans hrawLen.symm) h232 h233
  let S₁ : Stacks 234 A := {S with R := Function.update S.R 206 raw}
  have he₁' : Exec outerBody (copyPrefix 231 226 206 232 233) (mk v S) (10*raw.length+10) (mk v₁ S₁) := by
    simpa only [h206,List.append_nil] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := transfer_exec (body := outerBody) (count := 231) (src := 226) (dst := 227)
    (tmp := 233) (by decide) v₁ S₁ raw tail (by simpa [S₁] using hsource)
    (by simpa [S₁] using hclock.trans hrawLen.symm) (by simpa [S₁] using h233)
  let S₂ : Stacks 234 A := {S₁ with R := (Function.update (Function.update S₁.R 226 tail) 227
    (raw.reverse++S₁.R 227))}
  let T := embStk preparedBoundaryBatchCoreReg S
  let T₂ := embStk preparedBoundaryBatchCoreReg S₂
  have hT₂ : T₂ = {T with R := Function.update T.R 206 raw} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    have h226 : preparedBoundaryBatchCoreReg i ≠ 226 := preparedBoundaryBatchCoreReg_off i 226 (by decide)
    have h227 : preparedBoundaryBatchCoreReg i ≠ 227 := preparedBoundaryBatchCoreReg_off i 227 (by decide)
    by_cases hi : i = 206
    · subst i; simp [T₂,T,S₂,S₁,embStk,preparedBoundaryBatchCoreReg]
    have h206' : preparedBoundaryBatchCoreReg i ≠ 206 := preparedBoundaryBatchCoreReg_injective.ne hi
    simp [T₂,T,S₂,S₁,embStk,h226,h227,h206',hi]
  have hproject : embStk preparedBoundaryCoreReg T₂ =
      {embStk preparedBoundaryCoreReg T with R := Function.update (embStk preparedBoundaryCoreReg T).R 206 raw} := by
    rw [hT₂]
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi : i = 206
    · subst i; simp [embStk,preparedBoundaryCoreReg]
    have hreg : preparedBoundaryCoreReg i ≠ 206 := preparedBoundaryCoreReg_injective.ne hi
    simp [embStk,hreg,hi]
  have hstate : boundaryFactorState (embStk preparedBoundaryCoreReg T₂) =
      Function.update (boundaryFactorState (embStk preparedBoundaryCoreReg T)) .vk raw := by
    rw [hproject,boundaryFactorState_update_rhs]
  have hleft₂ : ∀ i, (embStk preparedBoundaryCoreReg T₂).L i = [] := by simpa [hproject] using hleft
  have hmul₂ : ∀ i : Fin 64, (embStk preparedBoundaryCoreReg T₂).R (boundaryFactorMulReg i) = [] := by
    intro i
    have hi : boundaryFactorMulReg i ≠ 206 := by
      intro he
      have hh := congrArg (fun k : Fin 224 => k.val) he
      change i.val = 206 at hh
      omega
    simpa [hproject,hi] using hmul i
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := preparedResidualSolve_exec (body := body) hQ hA p u l target rhsExp B W columns hp hlen
    hformat hstage b hb hbound (embDn preparedBoundaryBatchCoreReg v₂) T₂ hleft₂ hmul₂
    (by rw [hstate]; exact hready.update_vk raw) (by rw [hstate]; rfl)
    (by rw [hstate]; exact hbo) (by rw [hstate]; exact hhf) (by rw [hstate]; exact hdf)
    (by simpa [T₂,S₂,S₁,embStk,preparedBoundaryBatchCoreReg] using hmaster)
    (by simpa [T₂,S₂,S₁,embStk,preparedBoundaryBatchCoreReg] using h223)
    (by simpa [T₂,S₂,S₁,embStk,preparedBoundaryBatchCoreReg] using h184)
    (by simpa [T₂,S₂,S₁,embStk,preparedBoundaryBatchCoreReg] using h220)
    (by simpa [T₂,S₂,S₁,embStk,preparedBoundaryBatchCoreReg] using h221)
    (by simpa [T₂,S₂,S₁,embStk,preparedBoundaryBatchCoreReg] using h225)
  obtain ⟨v₃',hv₃',hu₃',he₃'⟩ := exec_emb_ovr (ι := id) (body' := outerBody) preparedBoundaryBatchCoreReg_injective
    (fun _ => rfl) he₃ v₂ rfl S₂ rfl
  let S₃ : Stacks 234 A := {S₂ with R := Function.update (Function.update S₂.R 206 []) 224 (ys++S₂.R 224)}
  have he₃'' : Exec outerBody (embProg preparedBoundaryBatchCoreReg id (preparedResidualSolve hQ))
      (mk v₂ S₂) n₃ (mk v₃' S₃) := by
    convert he₃' using 1
    apply congrArg (mk v₃')
    symm
    let T₀ : Stacks 226 A := {T₂ with R := Function.update T₂.R 206 []}
    change embOvr preparedBoundaryBatchCoreReg ({T₀ with R := Function.update T₀.R 224 (ys++T₂.R 224)} : Stacks 226 A).get S₂ = S₃
    rw [embOvr_updR preparedBoundaryBatchCoreReg_injective]
    dsimp only [T₀]
    rw [embOvr_updR preparedBoundaryBatchCoreReg_injective,embOvr_stk]
    rfl
  obtain ⟨v₄,hu₄,he₄⟩ := transfer_exec (body := outerBody) (count := 231) (src := 224) (dst := 228)
    (tmp := 233) (by decide) v₃' S₃ ys (S.R 224) (by simp [S₃,S₂,S₁])
    (by simpa [S₃,S₂,S₁] using hclock.trans hysLen.symm) (by simpa [S₃,S₂,S₁] using h233)
  refine ⟨v₄,(10*raw.length+10)+((4*raw.length+4)+(n₃+(4*ys.length+4))),
    hu₄.trans (hu₃'.trans (hu₃.trans (hu₂.trans hu₁))),?_,(Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃'' he₄))).cast rfl ?_⟩
  · change (10*raw.length+10)+((4*raw.length+4)+(n₃+(4*ys.length+4))) ≤ preparedResidualBatchStepCost q w B.card W
    rw [hrawLen,hysLen]
    have hn₃' : n₃ ≤ preparedResidualSolveCost q w B.card W := hn₃
    dsimp only [preparedResidualBatchStepCost]
    nlinarith only [hn₃']
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h206' : i = 206 <;> by_cases h224 : i = 224 <;> by_cases h226 : i = 226 <;>
      by_cases h227 : i = 227 <;> by_cases h228 : i = 228 <;>
      simp [S₃,S₂,S₁,h206',h224,h226,h227,h228,h206,raw,ys] <;> rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
