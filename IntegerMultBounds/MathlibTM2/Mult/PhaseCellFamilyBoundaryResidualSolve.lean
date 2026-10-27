module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyBoundaryRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedBoundaryResidualSolve

/-! Execute the existing retained factor solve below the interior family. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.BandFactor

def familyBoundaryReg (i : Fin 240) : Fin 263 := familyInverseLegacyReg (couplingBoundaryReg i)

theorem familyBoundaryReg_injective : Function.Injective familyBoundaryReg :=
  familyInverseLegacyReg_injective.comp couplingBoundaryReg_injective

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 263 Q A U}

noncomputable def familyBoundaryResidualSolve (hQ : SS.states ≤ Q) : Pr P 263 Q A U :=
  embProg familyInverseLegacyReg Empty.elim (placedBoundaryResidualSolve (P := Empty) hQ)

theorem familyBoundaryResidualSolve_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    ∀ (v : HS 263 Q A U) (S : Stacks 263 A),
    let T := embStk preparedBoundaryCoreReg (embStk sharedPageSolveReg (embStk familyBoundaryReg S))
    let σ := boundaryFactorState T
    (∀ i, T.L i = []) → (∀ i : Fin 64, T.R (boundaryFactorMulReg i) = []) →
    BoundarySolveReady σ q w W B.card →
    σ .vk = cstream A w b →
    σ .bo = cstream A w (Lc.map colC).flatten →
    σ .hf = cstream A w (Uc.map colC).flatten →
    σ .df = cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt)) →
    (S.R 119).length = q → S.R 223 = [] → S.R 184 = [] →
    S.R 220 = [] → S.R 221 = [] → S.R 225 = [] →
    ∃ v' n, v'.user = v.user ∧ n ≤ preparedResidualSolveCost q w B.card W ∧
      Exec body (familyBoundaryResidualSolve hQ) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 206 []) 224
          (cstream A w ((bandSolveVec q W Lc Uc rcs (b.map (normalizeBoundaryWord q (q/2-1)))).map
            (unscaleBoundaryWord q))++S.R 224))}) := by
  dsimp only
  intro hformat hstage b hb hbound v S hleft hmul hready hvk hbo hhf hdf hmaster h223 h184 h220 h221 h225
  obtain ⟨vi,n,hu,hn,he⟩ := placedBoundaryResidualSolve_exec (body := fun p : Empty => nomatch p)
    hQ hA p u l target rhsExp B W columns hp hlen hformat hstage b hb hbound
    (embDn familyInverseLegacyReg v) (embStk familyInverseLegacyReg S)
    hleft hmul hready hvk hbo hhf hdf hmaster h223 h184 h220 h221 h225
  obtain ⟨v',hv',hu',he'⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    familyInverseLegacyReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v',n,hu'.trans hu,hn,he'.cast rfl ?_⟩
  apply congrArg (mk v')
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let K := factorNewtonSteps p q
  let AZ := factorRankIntegerMatrix B W columns
  let Lc := naturalLineLc q K W B.card AZ
  let Uc := naturalLineUc q K W B.card AZ
  let rcs := naturalLineRcs q K W B.card AZ
  let solution := (bandSolveVec q W Lc Uc rcs (b.map (normalizeBoundaryWord q (q/2-1)))).map (unscaleBoundaryWord q)
  change embOvr familyInverseLegacyReg
    ({ {embStk familyInverseLegacyReg S with R := Function.update (embStk familyInverseLegacyReg S).R 206 []}
      with R := (Function.update (Function.update (embStk familyInverseLegacyReg S).R 206 []) 224
        (cstream A w solution++S.R 224))} : Stacks 256 A).get S = _
  rw [embOvr_updR familyInverseLegacyReg_injective,embOvr_updR familyInverseLegacyReg_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
