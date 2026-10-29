module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryFactorWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedResidualSolve
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Reuse the complete boundary numerical kernel beside retained packed geometry. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.BandFactor

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 242 Q A U}

noncomputable def packedPreparedResidualSolve (hQ : SS.states ≤ Q) : Pr P 242 Q A U :=
  embProg packedBoundaryFactorReg Empty.elim (preparedResidualSolve hQ)

theorem packedPreparedResidualSolve_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (∀ x ∈ b, |gv q x.re| ≤ (2 : ℝ)^couplingRowExponent rhsExp
      (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u) ∧
      |gv q x.im| ≤ (2 : ℝ)^couplingRowExponent rhsExp
      (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u)) →
    ∀ (v : HS 242 Q A U) (S : Stacks 242 A),
    let T := embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S)
    let σ := boundaryFactorState T
    (∀ i, T.L i = []) → (∀ i : Fin 64, T.R (boundaryFactorMulReg i) = []) →
    BoundarySolveReady σ q w W B.card →
    σ .vk = cstream A w b →
    σ .bo = cstream A w (Lc.map colC).flatten →
    σ .hf = cstream A w (Uc.map colC).flatten →
    σ .df = cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt)) →
    ((embStk packedBoundaryFactorReg S).R 119).length = q → (embStk packedBoundaryFactorReg S).R 223 = [] → (embStk packedBoundaryFactorReg S).R 184 = [] →
    (embStk packedBoundaryFactorReg S).R 220 = [] → (embStk packedBoundaryFactorReg S).R 221 = [] → (embStk packedBoundaryFactorReg S).R 225 = [] →
    ∃ v' n, v'.user = v.user ∧ n ≤ preparedResidualSolveCost q w B.card W ∧
      Exec body (packedPreparedResidualSolve hQ) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 143 []) 238
          (cstream A w ((bandSolveVec q W Lc Uc rcs (b.map (normalizeBoundaryWord q (q/2-1)))).map
            (unscaleBoundaryWord q))++S.R 238))}) := by
  dsimp only
  intro hformat hstage b hb hbound v S hleft hmul hready hvk hbo hhf hdf hmaster h223 h184 h220 h221 h225
  obtain ⟨v₁,n,hu₁,hn,he⟩ := preparedResidualSolve_exec
    (body := fun p : Empty => nomatch p) hQ hA p u l target rhsExp B W columns hp hlen
    hformat hstage b hb hbound (embDn packedBoundaryFactorReg v)
    (embStk packedBoundaryFactorReg S) hleft hmul hready hvk hbo hhf hdf
    hmaster h223 h184 h220 h221 h225
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    packedBoundaryFactorReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v₂,n,hu₂.trans hu₁,hn,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  rw [embOvr_updateR_updateR packedBoundaryFactorReg_injective]
  rfl

/-- Publication stays outside the reusable numerical core. -/
theorem packedPreparedResidualSolve_project {A : ℕ} (S : Stacks 242 A)
    (output : List (Fin (A+4))) :
    embStk packedBoundaryFactorReg
      {S with R := (Function.update (Function.update S.R 143 []) 238 (output++S.R 238))} =
      {embStk packedBoundaryFactorReg S with R :=
        (Function.update (Function.update (embStk packedBoundaryFactorReg S).R 206 []) 224
          (output++(embStk packedBoundaryFactorReg S).R 224))} := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi206 : i = 206
  · subst i; rfl
  by_cases hi224 : i = 224
  · subst i; rfl
  have h143 : packedBoundaryFactorReg i ≠ 143 := packedBoundaryFactorReg_injective.ne hi206
  have h238 : packedBoundaryFactorReg i ≠ 238 := packedBoundaryFactorReg_injective.ne hi224
  simp only [embStk,Function.comp_def,Function.update_of_ne h143,Function.update_of_ne h238,
    Function.update_of_ne hi206,Function.update_of_ne hi224]

/-- The retained factors and solve headers are ready for the next RHS. -/
theorem packedPreparedResidualSolve_ready {A q w W N : ℕ} (S : Stacks 242 A)
    (output : List (Fin (A+4)))
    (hready : BoundarySolveReady (boundaryFactorState
      (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S))) q w W N) :
    BoundarySolveReady (boundaryFactorState (embStk preparedBoundaryCoreReg
      (embStk packedBoundaryFactorReg
        {S with R := (Function.update (Function.update S.R 143 []) 238 (output++S.R 238))})))
      q w W N := by
  rw [packedPreparedResidualSolve_project]
  exact preparedBoundarySolve_ready _ _ hready

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
