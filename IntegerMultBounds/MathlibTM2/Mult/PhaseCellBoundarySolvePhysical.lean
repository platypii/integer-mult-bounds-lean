module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySolveRuns
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorWorkspace

/-! Solve a gathered boundary RHS on the fixed physical factor bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.MathlibTM2.Mult.Sizes

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

noncomputable def boundaryFoldedSolve (hQ : SS.states ≤ Q) : Pr P 224 Q A U :=
  .seq (boundaryPadRhs boundaryFactorReg)
    (bandLinePassP boundaryFactorReg boundaryFactorMulReg_injective (by decide) hQ)

/-- The bounded gathered RHS is consumed and its solution written to the output port.
All legacy tapes, factor tables, masters and other factor-bank ports are preserved. -/
theorem boundary_foldedSolve_physical_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    ∀ (v : HS 224 Q A U) (S : Stacks 224 A),
    let σ := boundaryFactorState S
    (∀ i, S.L i = []) → (∀ i : Fin 64, S.R (boundaryFactorMulReg i) = []) →
    BoundarySolveReady σ q w W B.card →
    ∀ (b : List GaussianInt), b.length = B.card →
    (∀ a ∈ b, |gv q a.re| ≤ 1/2 ∧ |gv q a.im| ≤ 1/2) →
    σ .vk = cstream A w b →
    σ .bo = cstream A w (Lc.map colC).flatten →
    σ .hf = cstream A w (Uc.map colC).flatten →
    σ .df = cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt)) →
    ∃ v' S' n, v'.user = v.user ∧ n ≤ 4*B.card*w+4*W*w+8+bandLinePassCost w B.card W ∧
      Exec body (boundaryFoldedSolve hQ) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ i : Fin 154, S'.R (boundaryFactorLegacyReg i) = S.R (boundaryFactorLegacyReg i)) ∧
      RsbFr boundaryFactorReg S S' ∧
      boundaryFactorState S' = Function.update (Function.update σ .vk []) .dout
        (cstream A w (bandSolveVec q W Lc Uc rcs b)) := by
  dsimp only
  intro hformat hstage v S hleft hmul hready b hb hbin hvk hbo hhf hdf
  have hrun := boundary_foldedSolve_allocated_runs (body := body)
    boundaryFactorReg_injective boundaryFactorReg_disjoint boundaryFactorMulReg_injective
    (by decide) hQ hA p u l target rhsExp B W columns hp hlen hformat hstage
    (boundaryFactorState S) hready b hb hbin hvk hbo hhf hdf
  obtain ⟨v',S',n,hu,hn,he,hholds,hframe⟩ := hrun v S ⟨hleft,hmul⟩ (fun _ => rfl)
  obtain ⟨hinp,hout,hL,hlegacy⟩ := boundaryFactorFr_legacy hframe
  refine ⟨v',S',n,hu,hn,he,hinp,hout,hL,?_,hframe,funext hholds⟩
  intro i
  by_cases hi : i = 140
  · subst i
    exact hholds .src
  · exact hlegacy i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
