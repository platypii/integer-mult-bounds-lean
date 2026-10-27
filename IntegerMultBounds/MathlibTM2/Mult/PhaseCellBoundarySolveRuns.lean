module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryLineFits
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalLineTableFits
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySolveReady

/-! Execute the computed boundary triangular solve with every numerical fit premise derived. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.MathlibTM2.Mult.Sizes

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

/-- A gathered, scaled boundary RHS is solved by the actual padding and triangular
program. Matrix stability, generated precision and Newton count discharge every
coefficient and intermediate fit condition; the factor tables are preserved. -/
theorem boundary_foldedSolve_allocated_runs
    (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (p u l target rhsExp : ℕ) {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hp : 2 ≤ p)
    (hlen : columns.length = B.card) :
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
    ∀ (σ : RsbR → List (Fin (A+4))), BoundarySolveReady σ q w W B.card →
    ∀ (b : List GaussianInt), b.length = B.card →
    (∀ a ∈ b, |gv q a.re| ≤ 1/2 ∧ |gv q a.im| ≤ 1/2) →
    σ .vk = cstream A w b →
    σ .bo = cstream A w (Lc.map colC).flatten →
    σ .hf = cstream A w (Uc.map colC).flatten →
    σ .df = cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt)) →
    RsbRuns body rg ι (.seq (boundaryPadRhs rg) (bandLinePassP rg hι hT hQ)) σ
      (Function.update (Function.update σ .vk []) .dout
        (cstream A w (bandSolveVec q W Lc Uc rcs b)))
      (4*B.card*w+4*W*w+8+bandLinePassCost w B.card W) := by
  dsimp only
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let K := factorNewtonSteps p q
  let AZ := factorRankIntegerMatrix B W columns
  intro hformat hstage σ hready b hb hbin hvk hbo hhf hdf
  have hbits : 4*p+2*Nat.size B.card+36 ≤ q := factor_execution_bits p u l target rhsExp B.card
  have hw : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  have hwpos : 1 ≤ w := by omega
  have hq : 2 ≤ q := by omega
  have hA4 : 4 ≤ A := by omega
  have hstates := factorIntegerState_allocated_fits A p u l target rhsExp B W columns hA4 hp hlen
    hformat hstage
  rw [factorWindowIntegers_windowZ,factorInputIntegers_inputsZ] at hstates
  obtain ⟨hLc,hUc,hrcs⟩ := naturalLineTables_lengths q K W B.card AZ
  obtain ⟨hLl,hUl⟩ := naturalLineTables_widths q K W B.card AZ hq
    (factorRankIntegerMatrix_band A q w B W columns hlen hformat hA4 hwpos)
  obtain ⟨hfL,hfU,hfr⟩ := naturalLineTables_fits q w K W B.card AZ hstates
  have hfits := boundary_line_allocated_rhsFits A p u l target rhsExp B W columns hp hA4 hlen
    hformat hstage b hb hbin
  have hqw : q ≤ w := by omega
  exact boundary_foldedSolve_runs hrg hdisj hι hT hQ hA σ hready hwpos hqw
    _ _ _ hLc hUc hLl hUl hrcs b hb hfL hfU hfr
    hfits.forward hfits.backward hfits.output hvk hbo hhf hdf

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
