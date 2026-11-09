module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedResidualBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicPreparedBoundaryColumns

/-! Reuse the existing prepared residual batch for the joint cyclic boundary bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.BandFactor
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

theorem cyclicPreparedResidualBatch_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (p u l target : ℕ) {s : ℕ} [NeZero s] (t a n : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hp : 2 ≤ p) :
    let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
    let W := 24*PhaseCellBand.width p u+1
    let bits := boundaryTableBits p target 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    let AZ := factorRankIntegerMatrix B W columns
    let Lc := naturalLineLc q K W B.card AZ
    let Uc := naturalLineUc q K W B.card AZ
    let rcs := naturalLineRcs q K W B.card AZ
    let solve := fun (b : List GaussianInt) => (bandSolveVec q W Lc Uc rcs
      (b.map (normalizeBoundaryWord q (q/2-1)))).map (unscaleBoundaryWord q)
    PreparedBoundaryColumns A p bits q w W B columns →
    ∀ (bs : List (List GaussianInt)), (∀ b ∈ bs, b.length = B.card) →
    (∀ b ∈ bs, ∀ x ∈ b, |gv q x.re| ≤ (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2)
      (8*p+1) (couplingCountExponent p u) ∧ |gv q x.im| ≤
      (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2) (8*p+1) (couplingCountExponent p u)) →
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
    S.R 206 = [] → S.R 225 = [] → S.R 227 = [] → S.R 228 = [] → S.R 230 = [] → S.R 231 = [] →
    S.R 232 = [] → S.R 233 = [] →
    (S.R 229).length = bs.length → S.R 226 = cstream A w bs.flatten++tail →
    ∃ v' n, v'.user = v.user ∧ n ≤ preparedResidualBatchCost q w B.card W bs.length ∧
      ExecWithin (embTab preparedBoundaryBatchCoreReg (embTab preparedBoundaryCoreReg body))
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
          preparedResidualBatchWorkspace (A := A) (U := U) P hQ q w B.card W bs.length) 0
        (preparedResidualBatch hQ) (mk v S) n
        (mk v' {S with R := Function.update S.R 224 (cstream A w (bs.map solve).flatten++S.R 224)}) := by
  dsimp only
  intro hprepared
  exact preparedResidualBatch_exec (body := body) hQ hA p u l target 2
    (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n)
    (24*PhaseCellBand.width p u+1) columns hp hprepared.length hprepared.format hprepared.stage

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
