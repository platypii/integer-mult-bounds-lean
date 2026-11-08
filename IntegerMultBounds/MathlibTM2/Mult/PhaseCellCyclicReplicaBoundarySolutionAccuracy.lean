module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicBoundarySolutionAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaResidualAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaBoundaryFormat

/-! One accurate cyclic factor page solves every cached replica's boundary RHS.
The existing single-system estimate is instantiated structurally at an arbitrary row. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem cyclicReplicaBoundary_solution_accuracy (A p u l target a n : ℕ)
    {s t : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (ha : a < s) (hn : n ≤ s) (hA : 4 ≤ A) :
    let band := PhaseCellBand.width p u
    let B := cyclicPrincipalBoundary s t band a n
    let V := cyclicPrincipalVertices s a n
    let I := cyclicPrincipalInterior s t band a n
    let bits := boundaryTableBits p target 2 B.card
    let cellTarget := initialSchurTarget p u bits 2
    let q := executionPrecision p l cellTarget 2
    let w := executionWidth p l cellTarget 2
    let W := 24*band+1
    let K := factorNewtonSteps p q
    ∀ (Fs : List (ZMod s → GaussianInt))
      (hF : ∀ F ∈ Fs, ∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2)
      (Cs Ds : List (ZMod s → GaussianInt)),
    Cs.length = Fs.length → Ds.length = Fs.length →
    (∀ j : Fin Cs.length, ReplicaCouplingResidualSpec
      (axis.cyclicLeftReplicaProblem cellTarget 2 a n ha Fs hF)
      (Fs.length-1-j.val) (Cs[j.val]'j.isLt)) →
    (∀ j : Fin Ds.length, ReplicaCouplingResidualSpec
      (axis.cyclicRightReplicaProblem cellTarget 2 a n hn Fs hF)
      (Fs.length-1-j.val) (Ds[j.val]'j.isLt)) →
    ∀ columns : List (ZMod s → GaussianInt),
    PreparedBoundaryColumns A p bits q w W B columns →
    ColumnFamilyAccurate A q w B (SchurDominance.run (realMatrix s t p u) V I.toList).1
      (1/(2 : ℝ)^bits) columns →
    ∀ j : Fin Fs.length, ∀ x : ZMod s → ℝ,
    let rhs := fun k => (value q (Fs.reverse.getD (Fs.length-1-j.val) (fun _ => 0) k)).re
    Solves (realMatrix s t p u) V x rhs →
    let AZ := factorRankIntegerMatrix B W columns
    let row := cyclicReplicaBoundaryRow t band a n (Cs.getD j.val (fun _ => 0)) (Ds.getD j.val (fun _ => 0))
    let solution := (bandSolveVec q W (naturalLineLc q K W B.card AZ)
      (naturalLineUc q K W B.card AZ) (naturalLineRcs q K W B.card AZ)
      (row.map (normalizeBoundaryWord q (q/2-1)))).map (unscaleBoundaryWord q)
    solution.length = B.card ∧ ∀ i < B.card,
      ‖value q (solution.getD i 0)-(x (bFoldAt s B i) : ℂ)‖ ≤ 3/(2 : ℝ)^target ∧
      ‖value q (solution.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p 2 := by
  dsimp only
  let band := PhaseCellBand.width p u
  let B := cyclicPrincipalBoundary s t band a n
  let bits := boundaryTableBits p target 2 B.card
  let cellTarget := initialSchurTarget p u bits 2
  let q := executionPrecision p l cellTarget 2
  intro Fs hF Cs Ds hCs hDs hC hD columns hprepared hcolumns
  obtain ⟨R,hR,herror⟩ := cyclicReplicaResiduals_accurate axis cellTarget 2 a n ha hn Fs hF Cs Ds hCs hDs
    (replicaCouplingResiduals_accurate _ axis.hp axis.hpacket Cs hCs hC)
    (replicaCouplingResiduals_accurate _ axis.hp axis.hpacket Ds hDs hD)
  have hp : 0 < p := by have := axis.hp; omega
  have hp8 : (0 : ℝ) < 8*(p : ℝ) := by
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp
    positivity
  have hbudget : 8*(p : ℝ)*haloResidualError p u q 2 cellTarget ≤
      1/(2 : ℝ)^(recoveryTarget p bits+2) := by
    simpa only [haloResidualError] using initialResidual_error_budget p u l bits 2 hp
  intro j x hx
  have hjC : j.val < Cs.length := by rw [hCs]; exact j.isLt
  have hjD : j.val < Ds.length := by rw [hDs]; exact j.isLt
  have hCmem : Cs.getD j.val (fun _ => 0) ∈ Cs := by
    rw [List.getD_eq_getElem _ _ hjC]; exact List.getElem_mem hjC
  have hDmem : Ds.getD j.val (fun _ => 0) ∈ Ds := by
    rw [List.getD_eq_getElem _ _ hjD]; exact List.getElem_mem hjD
  have hCnorm : ∀ i, ‖value q (Cs.getD j.val (fun _ => 0) i)‖ ≤
      (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2) (8*p+1) (couplingCountExponent p u) :=
    replicaCouplingResiduals_sharp_norm (axis.cyclicLeftReplicaProblem cellTarget 2 a n ha Fs hF)
      Cs hCs hC _ hCmem
  have hDnorm : ∀ i, ‖value q (Ds.getD j.val (fun _ => 0) i)‖ ≤
      (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2) (8*p+1) (couplingCountExponent p u) :=
    replicaCouplingResiduals_sharp_norm (axis.cyclicRightReplicaProblem cellTarget 2 a n hn Fs hF)
      Ds hDs hD _ hDmem
  have hsolve := cyclicBoundary_solution_accuracy A p u l target a n axis ha hn hA columns hprepared hcolumns
    (cyclicReplicaResidualField a n (Cs.getD j.val (fun _ => 0)) (Ds.getD j.val (fun _ => 0))) R x
    (fun k => (value q (Fs.reverse.getD (Fs.length-1-j.val) (fun _ => 0) k)).re)
    hR hx
    (by intro i _
        apply (Complex.abs_re_le_norm _).trans
        exact (axis.cyclicLeftReplicaProblem cellTarget 2 a n ha Fs hF).rhs_bound
          (Fs.length-1-j.val) (by change Fs.length-1-j.val < Fs.length; have := j.isLt; omega) i)
    (by intro i _
        rw [cyclicReplicaResidualField,value_realPartWord_norm]
        apply (Complex.abs_re_le_norm _).trans
        split <;> first | exact hCnorm i | exact hDnorm i)
    (by intro i _; rfl)
    (by intro i hi
        apply (le_div_iff₀ hp8).mpr
        have hscaled := mul_le_mul_of_nonneg_left (herror j i hi) hp8.le
        simpa only [mul_comm] using hscaled.trans hbudget)
  simpa only [cyclicReplicaBoundaryRow,bFoldOrder,List.map_map,Function.comp_def,cyclicReplicaResidualField] using hsolve

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
