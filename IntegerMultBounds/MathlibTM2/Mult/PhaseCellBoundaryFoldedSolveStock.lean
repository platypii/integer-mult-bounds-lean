module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySolveRuns
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBandLinePassStock

/-! The gathered folded boundary solve reuses the complete triangular kernel's reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.Sizes
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

def boundarySolveWorkspace (R C w N W : ℕ) : ℕ :=
  2*realWeightWorkspace C w W+realWeightWorkspace R w 1+
    10000*(N+1)*(W+1)*(w+1)+2*(4*N*w+4*W*w+8)

theorem boundary_solve_runs_within (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q w W N : ℕ} (σ : RsbR → List (Fin (A+4))) (h : BoundarySolveReady σ q w W N)
    (hw : 1 ≤ w) (hq : q ≤ w)
    (Lc Uc : List (List ℤ)) (rcs : List ℤ)
    (hLc : Lc.length = N) (hUc : Uc.length = N)
    (hLl : ∀ c ∈ Lc, c.length = W) (hUl : ∀ c ∈ Uc, c.length = W)
    (hrcs : rcs.length = N) (b : List GaussianInt) (hb : b.length = N)
    (hfL : ∀ c ∈ Lc, ∀ x ∈ c, Fits w (⟨x,0⟩ : GaussianInt))
    (hfU : ∀ c ∈ Uc, ∀ x ∈ c, Fits w (⟨x,0⟩ : GaussianInt))
    (hfr : ∀ x ∈ rcs, Fits w (⟨x,0⟩ : GaussianInt))
    (hfit₁ : ∀ j < N, Fits w ((Mult.BandList.bandPend q Lc
      (b ++ List.replicate W 0) j).headD 0))
    (hfit₂ : ∀ j < N, Fits w ((Mult.BandList.bandPendB q Uc rcs
      ((Mult.BandList.fwdZC q Lc (b ++ List.replicate W 0)).reverse ++
        List.replicate W 0) j).headD 0))
    (hfit₃ : ∀ j < N, Fits w (tdivN q ((Mult.BandList.bandPendB q Uc rcs
      ((Mult.BandList.fwdZC q Lc (b ++ List.replicate W 0)).reverse ++
        List.replicate W 0) j).headD 0 * ⟨rcs.getD j 0,0⟩)))
    (hvk : σ .vk = cstream A w (b ++ List.replicate W 0))
    (hbo : σ .bo = cstream A w (Lc.map colC).flatten)
    (hhf : σ .hf = cstream A w (Uc.map colC).flatten)
    (hdf : σ .df = cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt)))
    (R C : ℕ)
    (hpushR : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg .hv .xa .hc)) ≤ R)
    (hpushC : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg .ya .xs .pr)) ≤ C) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι) (bandLinePassP rg hι hT hQ) σ
      (Function.update (Function.update σ .vk []) .dout
        (cstream A w (bandSolveVec q W Lc Uc rcs b))) (bandLinePassCost w N W) (2*realWeightWorkspace C w W+realWeightWorkspace R w 1+10000*(N+1)*(W+1)*(w+1)) := by
  apply band_linePass_runs_within (K := R) (L := C) hrg hdisj hι hT hQ hA σ h.ready hw hq
    Lc Uc rcs hLc hUc hLl hUl hrcs b hb hfL hfU hfr hfit₁ hfit₂ hfit₃ hvk hbo hhf hdf
  all_goals first
    | exact hpushR
    | exact hpushC
    | exact h.sn
    | exact h.m2n
    | exact h.mwn
    | exact h.empty _ (by simp [boundarySolveScratch])

/-- Pad and solve one gathered boundary RHS using the retained factors. -/
theorem boundary_foldedSolve_runs_within (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q w W N : ℕ} (σ : RsbR → List (Fin (A+4))) (h : BoundarySolveReady σ q w W N)
    (hw : 1 ≤ w) (hq : q ≤ w)
    (Lc Uc : List (List ℤ)) (rcs : List ℤ)
    (hLc : Lc.length = N) (hUc : Uc.length = N)
    (hLl : ∀ c ∈ Lc, c.length = W) (hUl : ∀ c ∈ Uc, c.length = W)
    (hrcs : rcs.length = N) (b : List GaussianInt) (hb : b.length = N)
    (hfL : ∀ c ∈ Lc, ∀ x ∈ c, Fits w (⟨x,0⟩ : GaussianInt))
    (hfU : ∀ c ∈ Uc, ∀ x ∈ c, Fits w (⟨x,0⟩ : GaussianInt))
    (hfr : ∀ x ∈ rcs, Fits w (⟨x,0⟩ : GaussianInt))
    (hfit₁ : ∀ j < N, Fits w ((Mult.BandList.bandPend q Lc
      (b ++ List.replicate W 0) j).headD 0))
    (hfit₂ : ∀ j < N, Fits w ((Mult.BandList.bandPendB q Uc rcs
      ((Mult.BandList.fwdZC q Lc (b ++ List.replicate W 0)).reverse ++
        List.replicate W 0) j).headD 0))
    (hfit₃ : ∀ j < N, Fits w (tdivN q ((Mult.BandList.bandPendB q Uc rcs
      ((Mult.BandList.fwdZC q Lc (b ++ List.replicate W 0)).reverse ++
        List.replicate W 0) j).headD 0 * ⟨rcs.getD j 0,0⟩)))
    (hvk : σ .vk = cstream A w b)
    (hbo : σ .bo = cstream A w (Lc.map colC).flatten)
    (hhf : σ .hf = cstream A w (Uc.map colC).flatten)
    (hdf : σ .df = cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt)))
    (R C : ℕ)
    (hpushR : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg .hv .xa .hc)) ≤ R)
    (hpushC : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg .ya .xs .pr)) ≤ C) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι) (.seq (boundaryPadRhs rg) (bandLinePassP rg hι hT hQ)) σ
      (Function.update (Function.update σ .vk []) .dout
        (cstream A w (bandSolveVec q W Lc Uc rcs b))) (4*N*w+4*W*w+8+bandLinePassCost w N W) (boundarySolveWorkspace R C w N W) := by
  let σ₁ := Function.update σ .vk (cstream A w (b ++ List.replicate W 0))
  have hpad := (boundary_padRhs_runs (body := body) hrg hdisj σ h b hb hvk).within_native
    (show mnNativePushBound 2 (boundaryPadRhs (P := P) (Q := Q) (A := A) (U := U) rg) by
      simp [boundaryPadRhs,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,
        whileR,peekR,mnNativePushBound,mnActPush])
  have hsolve := boundary_solve_runs_within (body := body) hrg hdisj hι hT hQ hA σ₁
    (h.update_vk _) hw hq Lc Uc rcs hLc hUc hLl hUl hrcs b hb hfL hfU hfr
    hfit₁ hfit₂ hfit₃ (by simp [σ₁])
    (by simpa [σ₁] using hbo) (by simpa [σ₁] using hhf) (by simpa [σ₁] using hdf) R C hpushR hpushC
  refine ((RsbRunsWithin.seq hdisj hpad hsolve).congr ?_).mono (le_refl _) ?_
  swap
  · unfold boundarySolveWorkspace
    omega
  funext r
  cases r <;> simp [σ₁]

theorem boundary_foldedSolve_allocated_runs_within
    (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (p u l target rhsExp : ℕ) {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hp : 2 ≤ p)
    (hlen : columns.length = B.card)
    (R C : ℕ)
    (hpushR : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg .hv .xa .hc)) ≤ R)
    (hpushC : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg .ya .xs .pr)) ≤ C) :
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
    RsbRunsWithin (body := body) (rg := rg) (ι := ι) (.seq (boundaryPadRhs rg) (bandLinePassP rg hι hT hQ)) σ
      (Function.update (Function.update σ .vk []) .dout
        (cstream A w (bandSolveVec q W Lc Uc rcs b)))
      (4*B.card*w+4*W*w+8+bandLinePassCost w B.card W) (boundarySolveWorkspace R C w B.card W) := by
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
  exact boundary_foldedSolve_runs_within hrg hdisj hι hT hQ hA σ hready hwpos hqw
    _ _ _ hLc hUc hLl hUl hrcs b hb hfL hfU hfr
    hfits.forward hfits.backward hfits.output hvk hbo hhf hdf R C hpushR hpushC

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
