module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageResidualSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedBoundaryRhs

/-! Execute the reusable normalized/unscaled solve under the shared caller's procedure table. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 256 Q A U}

noncomputable def placedBoundaryResidualSolve (hQ : SS.states ≤ Q) : Pr P 256 Q A U :=
  embProg couplingBoundaryReg Empty.elim (sharedPageResidualSolve (P := Empty) hQ)

theorem placedBoundaryResidualSolve_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    ∀ (v : HS 256 Q A U) (S : Stacks 256 A),
    let T := embStk preparedBoundaryCoreReg (embStk sharedPageSolveReg (embStk couplingBoundaryReg S))
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
      Exec body (placedBoundaryResidualSolve hQ) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 206 []) 224
          (cstream A w ((bandSolveVec q W Lc Uc rcs (b.map (normalizeBoundaryWord q (q/2-1)))).map
            (unscaleBoundaryWord q))++S.R 224))}) := by
  dsimp only
  intro hformat hstage b hb hbound v S hleft hmul hready hvk hbo hhf hdf hmaster h223 h184 h220 h221 h225
  obtain ⟨vi,n,hu,hn,he⟩ := sharedPageResidualSolve_exec (body := fun p : Empty => nomatch p)
    hQ hA p u l target rhsExp B W columns hp hlen hformat hstage b hb hbound
    (embDn couplingBoundaryReg v) (embStk couplingBoundaryReg S)
    hleft hmul hready hvk hbo hhf hdf hmaster h223 h184 h220 h221 h225
  obtain ⟨v',hv',hu',he'⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    couplingBoundaryReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v',n,hu'.trans hu,hn,he'.cast rfl ?_⟩
  apply congrArg (mk v')
  let T := embStk couplingBoundaryReg S
  let T₁ : Stacks 240 A := {T with R := Function.update T.R 206 []}
  change embOvr couplingBoundaryReg ({T₁ with R := Function.update T₁.R 224 _} : Stacks 240 A).get S = _
  rw [embOvr_updR couplingBoundaryReg_injective]
  dsimp only [T₁]
  rw [embOvr_updR couplingBoundaryReg_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
