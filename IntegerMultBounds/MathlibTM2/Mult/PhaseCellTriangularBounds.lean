module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalLineTables

/-! Backward heads are controlled by the computed solution and positive reciprocals. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.BandList IntegerMultBounds.MathlibTM2.Mult.Sizes

/-- A structural bound for either component of arbitrary Gaussian triangular passes. -/
theorem triangular_part_bounds (q W N p : ℕ) (Lc Uc : List (List ℤ)) (rcs : List ℤ)
    (hLc : Lc.length = N) (hUc : Uc.length = N) (hrcs : rcs.length = N)
    (b : List GaussianInt) (hb : b.length = N)
    (π : GaussianInt → ℤ)
    (htd : ∀ z, π (tdivN q z) = (π z).tdiv (2^q))
    (hmulr : ∀ z c, π (z * ⟨c,0⟩) = π z*c)
    (hforward : ∀ j < N, |gv q (π ((fwdZC q Lc (b ++ List.replicate W 0)).getD j 0))| ≤ 3*(8*p+1)+1)
    (hsolution : ∀ a ∈ bandSolveVec q W Lc Uc rcs b, |gv q (π a)| ≤ 8*p+1)
    (hrec : ∀ j < N, 1/4 ≤ gv q (rcs.getD j 0)) :
    (∀ j < N, |gv q (π ((bandPend q Lc (b ++ List.replicate W 0) j).headD 0))| ≤ 3*(8*p+1)+1) ∧
    (∀ j < N, |gv q (π ((bandPendB q Uc rcs
      ((fwdZC q Lc (b ++ List.replicate W 0)).reverse ++ List.replicate W 0) j).headD 0))| ≤ 4*(8*p+2)) ∧
    ∀ j < N, |gv q (π (tdivN q ((bandPendB q Uc rcs
      ((fwdZC q Lc (b ++ List.replicate W 0)).reverse ++ List.replicate W 0) j).headD 0 *
        ⟨rcs.getD j 0,0⟩)))| ≤ 8*p+1 := by
  let pend := b ++ List.replicate W (0 : GaussianInt)
  have hplen : pend.length = N+W := by simp [pend,hb]
  have hfwdC := fwdZC_eq_bandOut q Lc pend (by rw [hLc,hplen]; omega)
  have hfwdlen : (fwdZC q Lc pend).length = N := by rw [hfwdC]; simp [length_bandOut,hLc]
  let pend' := (fwdZC q Lc pend).reverse ++ List.replicate W (0 : GaussianInt)
  have hplen' : pend'.length = N+W := by simp [pend',hfwdlen]
  have hbwdC := bwdZC_eq_bandOutB q Uc rcs pend' (by rw [hUc,hplen']; omega) (by rw [hUc,hrcs])
  have hsolvlen : (bandSolveVec q W Lc Uc rcs b).length = N := by
    rw [bandSolveVec,List.length_reverse,length_bwdZC q Uc rcs _ (by omega)
      (by change Uc.length ≤ pend'.length; rw [hUc,hplen']; omega),hUc]
  have hsolrev : bwdZC q Uc rcs pend' = (bandSolveVec q W Lc Uc rcs b).reverse := by
    simp only [bandSolveVec,List.reverse_reverse]
    rfl
  have hout : ∀ j < N, tdivN q ((bandPendB q Uc rcs pend' j).headD 0 * ⟨rcs.getD j 0,0⟩) =
      (bwdZC q Uc rcs pend').getD j 0 := by
    intro j hj
    rw [hbwdC,bandOutB_rev_getD q Uc rcs pend' _ j (by rw [hUc]; exact hj)]
  have houtB : ∀ j < N, |gv q (π (tdivN q ((bandPendB q Uc rcs pend' j).headD 0 *
      ⟨rcs.getD j 0,0⟩)))| ≤ 8*p+1 := by
    intro j hj
    rw [hout j hj,hsolrev,List.getD_eq_getElem _ _ (by simpa [hsolvlen] using hj)]
    exact hsolution _ (List.mem_reverse.mp (List.getElem_mem _))
  refine ⟨fun j hj => ?_, fun j hj => ?_,houtB⟩
  · rw [← bandOut_rev_getD q Lc pend N j hj,← hLc,← hfwdC]
    exact hforward j hj
  · have h := houtB j hj
    rw [htd,hmulr] at h
    let z := π ((bandPendB q Uc rcs pend' j).headD 0)
    have hr := hrec j hj
    have e := rdP_mul_grid q z (rcs.getD j 0)
    have herr := rdP_err q (gv q z*gv q (rcs.getD j 0))
    change |gv q ((z*rcs.getD j 0).tdiv (2^q))| ≤ 8*p+1 at h
    simp only [gv] at h hr herr e ⊢
    rw [← e] at h
    have hη1 : (1 : ℝ)/2^q ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact one_le_pow₀ (by norm_num)
    have h1 : |(z : ℝ)/2^q*(((rcs.getD j 0 : ℤ) : ℝ)/2^q)| ≤ 8*p+2 := by
      have := abs_sub_abs_le_abs_sub ((z : ℝ)/2^q*(((rcs.getD j 0 : ℤ) : ℝ)/2^q))
        (rdP q ((z : ℝ)/2^q*(((rcs.getD j 0 : ℤ) : ℝ)/2^q)))
      rw [abs_sub_comm] at this
      linarith
    rw [abs_mul,abs_of_pos (by linarith : (0 : ℝ) < ((rcs.getD j 0 : ℤ) : ℝ)/2^q)] at h1
    have h0 := abs_nonneg ((z : ℝ)/2^q)
    change |(z : ℝ)/2^q| ≤ 4*(8*p+2)
    nlinarith

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
