module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedPreparedResidualSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloResidualNormalization
public import IntegerMultBounds.NLogN.PhaseCellBoundaryFold

/-! The actual halo residual supplies the complete numerical kernel's input bound. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 242 Q A U}

theorem packedHaloResidualSolve_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (p u l target rhsExp : ℕ) {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hp : 2 ≤ p) (hlen : columns.length = B.card)
    (a b cellTarget : ℕ) {t : ℕ} {α d : ℝ}
    (hst : s < t) (hαu : α^2 = (u : ℝ)) (hθ : 0 < (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hdom : DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ)))) :
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
    ∀ (C D : ZMod s → GaussianInt) (x : ZMod s → ℝ),
    (∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^rhsExp) →
    Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun i => (value q (C i)).re) →
    PhaseCellInterface.ErrorOn (haloInterior s t (PhaseCellBand.width p u) a b)
      (fun i => (value q (D i)).re) x (1/(2 : ℝ)^cellTarget) →
    let b := (bFoldOrder s B).map (fun i => realPartWord
      (couplingRowField (2^15*p) q t u (PhaseCellBand.width p u) a b false D C i))
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
  intro hformat hstage C D x hC hx herror v S hleft hmul hready hvk hbo hhf hdf hmaster h223 h184 h220 h221 h225
  apply packedPreparedResidualSolve_exec (body := body) hQ hA p u l target rhsExp B W columns hp hlen
    hformat hstage _ (by simp only [List.length_map,bFoldOrder_length]) ?_
    v S hleft hmul hready hvk hbo hhf hdf hmaster h223 h184 h220 h221 h225
  intro z hz
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hz
  have hn := haloResidual_norm_bound (by omega : 0 < p) hst hαu hθ hgap hbudget
    a b hdom C D hC x hx herror i
  exact ⟨(Complex.abs_re_le_norm _).trans hn,(Complex.abs_im_le_norm _).trans hn⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
