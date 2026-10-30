module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySolutionField
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryUnscale
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundarySolveWorkspace

/-! The computed, unscaled real boundary field fits the existing recovery word
width. Prove the magnitude structurally over an arbitrary solved list first. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN.PhaseCellMatrix

theorem boundarySolutionField_unscaled_magnitude {s : ℕ} [NeZero s]
    (p q : ℕ) (hpq : p ≤ q/2) (B : Finset (ZMod s)) (zs : List GaussianInt)
    (hlen : zs.length = B.card) (hbound : ∀ z ∈ zs, |gv q z.re| ≤ 8*p+1) :
    ∀ i, ‖value q (boundarySolutionField B (zs.map (unscaleBoundaryWord q)) i)‖ ≤ (2 : ℝ)^(q+6) := by
  have hpPow : (p : ℝ) ≤ (2 : ℝ)^p := by exact_mod_cast (Nat.lt_two_pow_self (n := p)).le
  have hone : (1 : ℝ) ≤ 2^p := one_le_pow₀ (by norm_num)
  have hcoeff : 8*(p : ℝ)+1 ≤ (2 : ℝ)^(p+4) := by
    rw [pow_add]
    norm_num
    linarith
  have hgrid (a : ℤ) : gv q (a*(2 : ℤ)^(q/2+1)) = gv q a*(2 : ℝ)^(q/2+1) := by
    simp [gv]
    ring
  intro i
  by_cases hi : i ∈ B
  · have hpos : bFoldPos s B i < zs.length := by rw [hlen]; exact bFoldPos_lt s B i hi
    rw [boundarySolutionField,ite_eq_left hi,value_realPartWord_norm,
      List.getD_eq_getElem _ _ (by simpa using hpos),List.getElem_map]
    change |gv q (unscaleBoundaryWord q zs[bFoldPos s B i]).re| ≤ (2 : ℝ)^(q+6)
    rw [unscaleBoundaryWord,mul_real_re,hgrid,abs_mul,abs_of_pos (show 0 < (2 : ℝ)^(q/2+1) by positivity)]
    calc
      |gv q zs[bFoldPos s B i].re| * (2 : ℝ)^(q/2+1) ≤
          (2 : ℝ)^(p+4)*(2 : ℝ)^(q/2+1) :=
        mul_le_mul_of_nonneg_right ((hbound _ (List.getElem_mem hpos)).trans hcoeff) (by positivity)
      _ = (2 : ℝ)^(p+4+(q/2+1)) := (pow_add _ _ _).symm
      _ ≤ (2 : ℝ)^(q+6) := pow_le_pow_right₀ (by norm_num) (by omega)
  · rw [boundarySolutionField_off B _ i hi]
    have hz : value q (0 : GaussianInt) = (0 : ℂ) := by apply Complex.ext <;> simp [value]
    rw [hz,norm_zero]
    positivity

/-- Derive recovery magnitude for the actual allocated, normalized boundary solve. -/
theorem boundarySolutionField_allocated_magnitude (A p u l target rhsExp : ℕ)
    {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (W : ℕ) (columns : List (ZMod s → GaussianInt))
    (hp : 2 ≤ p) (hA : 4 ≤ A) :
    let bits := boundaryTableBits p target rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    let AZ := factorRankIntegerMatrix B W columns
    PreparedBoundaryColumns A p bits q w W B columns →
    ∀ b : List GaussianInt, b.length = B.card →
    (∀ z ∈ b, |gv q z.re| ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp)
        (8*p+1) (couplingCountExponent p u) ∧
      |gv q z.im| ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp)
        (8*p+1) (couplingCountExponent p u)) →
    ∀ i, ‖value q (boundarySolutionField B
      ((bandSolveVec q W (naturalLineLc q K W B.card AZ) (naturalLineUc q K W B.card AZ)
        (naturalLineRcs q K W B.card AZ) (b.map (normalizeBoundaryWord q (q/2-1)))).map
          (unscaleBoundaryWord q)) i)‖ ≤ (2 : ℝ)^(q+6) := by
  dsimp only
  intro hcolumns b hb hbound
  let q := executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target rhsExp B.card) 2) 2
  let K := factorNewtonSteps p q
  let AZ := factorRankIntegerMatrix B W columns
  let bs := b.map (normalizeBoundaryWord q (q/2-1))
  obtain ⟨hq,heven,-,-⟩ := boundary_normalization_precision p u l target rhsExp B.card
  change 2 ≤ q at hq
  change q%2 = 0 at heven
  have hbin : ∀ z ∈ bs, |gv q z.re| ≤ 1/2 ∧ |gv q z.im| ≤ 1/2 := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
    exact normalizeBoundaryWord_bound q (q/2) (q/2-1) (by omega) x
      (boundary_residual_normalization_bound p u l target rhsExp B.card x (hbound x hx))
  have hbs : bs.length = B.card := by simp [bs,hb]
  have hsol := boundary_line_allocated_solution_bounds A p u l target rhsExp B W columns hp hA
    hcolumns.length hcolumns.format hcolumns.stage bs hbs hbin
  apply boundarySolutionField_unscaled_magnitude p q ?_ B _
    (naturalLineSolve_length q K W B.card AZ bs hbs) (fun z hz => (hsol z hz).1)
  dsimp [q,executionPrecision,executionExponent,inputExponent]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
