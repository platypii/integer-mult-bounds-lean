module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySolveFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySolutionBounds

/-! A reusable boundary solve consumes one owned RHS, publishes its solution, and restores every prepared factor register. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.BandFactor

def preparedBoundaryCoreReg (i : Fin 224) : Fin 226 := ⟨i.val,by omega⟩

theorem preparedBoundaryCoreReg_injective : Function.Injective preparedBoundaryCoreReg := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 226 => k.val) h)

theorem preparedBoundaryCoreReg_private (i : Fin 224) :
    preparedBoundaryCoreReg i ≠ 224 ∧ preparedBoundaryCoreReg i ≠ 225 := by
  constructor <;> intro he <;> have hh := congrArg (fun k : Fin 226 => k.val) he <;>
    simp only [preparedBoundaryCoreReg] at hh <;> omega

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

noncomputable def preparedBoundarySolve (hQ : SS.states ≤ Q) : Pr P 226 Q A U :=
  .seq (embProg preparedBoundaryCoreReg id (boundaryFoldedSolve hQ))
    (.seq (moveR 217 225 id) (moveR 225 224 id))

def preparedBoundarySolveCost (w N W : ℕ) : ℕ :=
  8*N*w+4*W*w+12+bandLinePassCost w N W

theorem preparedBoundarySolve_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (∀ x ∈ b, |gv q x.re| ≤ 1/2 ∧ |gv q x.im| ≤ 1/2) →
    ∀ (v : HS 226 Q A U) (S : Stacks 226 A),
    let T := embStk preparedBoundaryCoreReg S
    let σ := boundaryFactorState T
    (∀ i, T.L i = []) → (∀ i : Fin 64, T.R (boundaryFactorMulReg i) = []) →
    BoundarySolveReady σ q w W B.card →
    σ .vk = cstream A w b →
    σ .bo = cstream A w (Lc.map colC).flatten →
    σ .hf = cstream A w (Uc.map colC).flatten →
    σ .df = cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt)) →
    S.R 225 = [] →
    ∃ v' n, v'.user = v.user ∧ n ≤ preparedBoundarySolveCost w B.card W ∧
      Exec (embTab preparedBoundaryCoreReg body) (preparedBoundarySolve hQ) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 206 []) 224
          (cstream A w (bandSolveVec q W Lc Uc rcs b)++S.R 224))}) := by
  dsimp only
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let K := factorNewtonSteps p q
  let AZ := factorRankIntegerMatrix B W columns
  let Lc := naturalLineLc q K W B.card AZ
  let Uc := naturalLineUc q K W B.card AZ
  let rcs := naturalLineRcs q K W B.card AZ
  intro hformat hstage b hb hbound v S hleft hmul hready hvk hbo hhf hdf h225
  let T := embStk preparedBoundaryCoreReg S
  let ys := bandSolveVec q W Lc Uc rcs b
  have hys : ys.length = B.card := naturalLineSolve_length q K W B.card AZ b hb
  obtain ⟨v₁,T₁,n₁,hu₁,hn₁,he₁,hinp,hout,hL,hlegacy,hframe,hpost⟩ :=
    boundary_foldedSolve_physical_exec (body := body) hQ hA p u l target rhsExp B W columns hp hlen
      hformat hstage (embDn preparedBoundaryCoreReg v) T hleft hmul hready b hb hbound hvk hbo hhf hdf
  have hT₁ : T₁ = {T with R := Function.update (Function.update T.R 206 []) 217 (cstream A w ys)} :=
    boundarySolve_frame_exact T T₁ _ hframe hlegacy hpost
  rw [hT₁] at he₁
  obtain ⟨v₁',hv₁',hu₁',he₁'⟩ := exec_emb_ovr (ι := id) (body' := embTab preparedBoundaryCoreReg body)
    preparedBoundaryCoreReg_injective (fun _ => rfl) he₁ v rfl S rfl
  let S₁ : Stacks 226 A := {S with R := Function.update (Function.update S.R 206 []) 217 (cstream A w ys)}
  have he₁'' : Exec (embTab preparedBoundaryCoreReg body) (embProg preparedBoundaryCoreReg id (boundaryFoldedSolve hQ))
      (mk v S) n₁ (mk v₁' S₁) := by
    convert he₁' using 1
    apply congrArg (mk v₁')
    symm
    let T₀ : Stacks 224 A := {T with R := Function.update T.R 206 []}
    change embOvr preparedBoundaryCoreReg ({T₀ with R := Function.update T₀.R 217 (cstream A w ys)} : Stacks 224 A).get S = S₁
    rw [embOvr_updR preparedBoundaryCoreReg_injective]
    dsimp only [T₀]
    rw [embOvr_updR preparedBoundaryCoreReg_injective,embOvr_stk]
    rfl
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec (embTab preparedBoundaryCoreReg body) 217 225 (by decide) id v₁' S₁
  let S₂ : Stacks 226 A := {S₁ with R := movedR S₁.R 217 225 id (S₁.R 217)}
  have h217 : S.R 217 = [] := hready.empty .dout (by simp [boundarySolveScratch])
  have h225' : S₂.R 225 = (cstream A w ys).reverse := by simp [S₂,S₁,movedR,h225]
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec (embTab preparedBoundaryCoreReg body) 225 224 (by decide) id v₂ S₂
  have hsize : (cstream A w ys).length = B.card*w := by simp [hys]
  refine ⟨v₃,n₁+((2*(S₁.R 217).length+2)+(2*(S₂.R 225).length+2)),
    hu₃.trans (hu₂.trans (hu₁'.trans hu₁)),?_,(Exec.seq he₁'' (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · change n₁+((2*(S₁.R 217).length+2)+(2*(S₂.R 225).length+2)) ≤ preparedBoundarySolveCost w B.card W
    have hn₁' : n₁ ≤ 4*B.card*w+4*W*w+8+bandLinePassCost w B.card W := hn₁
    simp only [S₁,Function.update_self,h225',List.length_reverse,hsize,preparedBoundarySolveCost]
    nlinarith only [hn₁']
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h206 : i = 206 <;> by_cases h217' : i = 217 <;> by_cases h224 : i = 224 <;>
      by_cases h225'' : i = 225 <;>
      simp [S₂,S₁,movedR,h206,h217',h224,h225'',h225,h217] <;> rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
