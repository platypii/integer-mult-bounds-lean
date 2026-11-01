module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundarySolveWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySolvePushBounds

/-! Place the bounded retained-factor solve beside packed geometry and archives. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 242 Q A U}

theorem packedPreparedResidualSolve_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (p u l target rhsExp : ℕ) {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hp : 2 ≤ p) (hlen : columns.length = B.card)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) :
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
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        push.workspace q w B.card W) depth (packedPreparedResidualSolve hQ) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 143 []) 238
          (cstream A w ((bandSolveVec q W Lc Uc rcs (b.map (normalizeBoundaryWord q (q/2-1)))).map
            (unscaleBoundaryWord q))++S.R 238))}) := by
  dsimp only
  intro hformat hstage b hb hbound v S hleft hmul hready hvk hbo hhf hdf hmaster h223 h184 h220 h221 h225
  obtain ⟨v₁,n,hu₁,hn,he⟩ := preparedResidualSolve_exec_within
    (body := fun p : Empty => nomatch p) hQ hA p u l target rhsExp B W columns hp hlen
    push.normalize push.unscale push.reciprocal push.column
    push.normalize_push push.unscale_push push.reciprocal_push push.column_push
    hformat hstage b hb hbound (embDn packedBoundaryFactorReg v)
    (embStk packedBoundaryFactorReg S) hleft hmul hready hvk hbo hhf hdf
    hmaster h223 h184 h220 h221 h225
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    packedBoundaryFactorReg_injective (fun p => nomatch p) (he 0).toExec v rfl S rfl
  refine ⟨v₂,n,hu₂.trans hu₁,hn,?_⟩
  intro depth
  have ht := exec_emb_within_stock_of_exec (ι := Empty.elim) (body' := body)
    packedBoundaryFactorReg_injective (fun p => nomatch p) (he depth) v rfl S rfl he₂
  refine ht.cast rfl ?_
  apply congrArg (mk v₂)
  rw [embOvr_updateR_updateR packedBoundaryFactorReg_injective]
  rfl


theorem packedPreparedResidualSolve_bank_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (p u l target rhsExp : ℕ) {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hp : 2 ≤ p)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) :
    let bits := boundaryTableBits p target rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    let AZ := factorRankIntegerMatrix B W columns
    let Lc := naturalLineLc q K W B.card AZ
    let Uc := naturalLineUc q K W B.card AZ
    let rcs := naturalLineRcs q K W B.card AZ
    PreparedBoundaryColumns A p bits q w W B columns →
    ∀ (b : List GaussianInt), b.length = B.card →
    (∀ x ∈ b, |gv q x.re| ≤ (2 : ℝ)^couplingRowExponent rhsExp
      (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u) ∧
      |gv q x.im| ≤ (2 : ℝ)^couplingRowExponent rhsExp
      (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u)) →
    ∀ (v : HS 242 Q A U) (S : Stacks 242 A),
    let T := embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S)
    let σ := boundaryFactorState T
    PackedPreparedBank q w W B.card S →
    σ .vk = cstream A w b →
    PackedBoundaryFactorPages (cstream A w (Lc.map colC).flatten)
      (cstream A w (Uc.map colC).flatten)
      (cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt))) S →
    ∃ v' n, v'.user = v.user ∧ n ≤ preparedResidualSolveCost q w B.card W ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        push.workspace q w B.card W) depth (packedPreparedResidualSolve hQ) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 143 []) 238
          (cstream A w ((bandSolveVec q W Lc Uc rcs (b.map (normalizeBoundaryWord q (q/2-1)))).map
            (unscaleBoundaryWord q))++S.R 238))}) := by
  dsimp only
  intro hcolumns b hb hbound v S hbank hvk hpages
  exact packedPreparedResidualSolve_exec_within hQ hA p u l target rhsExp B W columns hp hcolumns.length push
    hcolumns.format hcolumns.stage b hb hbound v S hbank.workspace.left hbank.workspace.mul
    hbank.ready hvk hpages.lower hpages.upper hpages.reciprocal hbank.workspace.precision hbank.workspace.exponent
    hbank.workspace.scalar hbank.workspace.table hbank.workspace.padding hbank.workspace.swap

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
