module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryLineReciprocal
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTriangularBounds

/-! Component bounds for the actual Gaussian boundary solve, with allocated precision. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.BandList IntegerMultBounds.MathlibTM2.Mult.Sizes

theorem boundary_line_part (A p u l target rhsExp : ℕ) {s : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (W : ℕ) (columns : List (ZMod s → GaussianInt))
    (hp : 2 ≤ p) (hA : 4 ≤ A) (hlen : columns.length = B.card) :
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
    ∀ (π : GaussianInt → ℤ) (_hπ0 : π 0 = 0)
    (_hfwd : ∀ cs pend, (fwdZC q cs pend).map π = fwdZ q cs (pend.map π))
    (_hsolve : ∀ b, (bandSolveVec q W Lc Uc rcs b).map π = lineSolveZ q K W B.card AZ (b.map π))
    (_htd : ∀ z, π (tdivN q z) = (π z).tdiv (2^q))
    (_hmulr : ∀ z c, π (z * ⟨c,0⟩) = π z*c)
    (_hb : ∀ a ∈ b, |gv q (π a)| ≤ 1/2),
    (∀ j < B.card, |gv q (π ((bandPend q Lc (b ++ List.replicate W 0) j).headD 0))| ≤ 3*(8*p+1)+1) ∧
    (∀ j < B.card, |gv q (π ((bandPendB q Uc rcs
      ((fwdZC q Lc (b ++ List.replicate W 0)).reverse ++ List.replicate W 0) j).headD 0))| ≤ 4*(8*p+2)) ∧
    (∀ j < B.card, |gv q (π (tdivN q ((bandPendB q Uc rcs
      ((fwdZC q Lc (b ++ List.replicate W 0)).reverse ++ List.replicate W 0) j).headD 0 *
        ⟨rcs.getD j 0,0⟩)))| ≤ 8*p+1) ∧
    ∀ a ∈ bandSolveVec q W Lc Uc rcs b, |gv q (π a)| ≤ 8*p+1 := by
  dsimp only
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let K := factorNewtonSteps p q
  let AZ := factorRankIntegerMatrix B W columns
  let Lc := naturalLineLc q K W B.card AZ
  let Uc := naturalLineUc q K W B.card AZ
  let rcs := naturalLineRcs q K W B.card AZ
  intro hformat hstage b hb π hπ0 hfwd hsolve htd hmulr hbin
  have hbZ : (b.map π).length = B.card := by simp [hb]
  have hbound : ∀ i < B.card, |gv q ((b.map π).getD i 0)| ≤ 1/2 := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by simpa [hb] using hi),List.getElem_map]
    exact hbin _ (List.getElem_mem _)
  obtain ⟨hsolB,hfwdB⟩ := boundary_line_allocated_sizes A p u l target rhsExp B W columns hp hA hlen
    hformat hstage (b.map π) hbZ hbound
  obtain ⟨hLc,hUc,hrcs⟩ := naturalLineTables_lengths q K W B.card AZ
  change Lc.length = B.card at hLc
  change Uc.length = B.card at hUc
  change rcs.length = B.card at hrcs
  have hfl : (fwdZC q Lc (b ++ List.replicate W 0)).length = B.card := by
    rw [length_fwdZC q Lc _ (by simp only [List.length_append,List.length_replicate,hb]; omega),hLc]
  have hsl : (bandSolveVec q W Lc Uc rcs b).length = B.card := by
    rw [bandSolveVec,List.length_reverse,length_bwdZC q Uc rcs _ (by omega)
      (by simp [hfl]; omega),hUc]
  have hsolution : ∀ a ∈ bandSolveVec q W Lc Uc rcs b, |gv q (π a)| ≤ 8*p+1 := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem ha
    have h := hsolB i (by rw [hsl] at hi; exact hi)
    rw [← hsolve b,List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_map] at h
    exact h
  have hforward : ∀ j < B.card,
      |gv q (π ((fwdZC q Lc (b ++ List.replicate W 0)).getD j 0))| ≤ 3*(8*p+1)+1 := by
    intro j hj
    rw [proj_getD π hπ0,hfwd]
    simpa [Lc,naturalLineLc,hπ0] using hfwdB j hj
  have hrec := boundary_line_rcs_lower A p u l target rhsExp B W columns hp hA hlen hformat hstage
  obtain ⟨h₁,h₂,h₃⟩ := triangular_part_bounds q W B.card p Lc Uc rcs hLc hUc hrcs b hb
    π htd hmulr hforward hsolution hrec
  exact ⟨h₁,h₂,h₃,hsolution⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
