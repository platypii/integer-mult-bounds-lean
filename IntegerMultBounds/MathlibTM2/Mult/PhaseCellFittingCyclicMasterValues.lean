module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaProblems
public import IntegerMultBounds.NLogN.PhaseCellCyclicPrincipalGeometry
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRecoveryMasterValues
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInversePrecisionSetup

/-! Reuse the executed ordinary inverse-master generator for fitting cyclic
callbacks. The joint boundary is the physical interval boundary. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem RecoveryAxisBounds.fittingCyclicLeftMasterValues
    {p l s t u : ℕ} [NeZero s] {α d : ℝ} (axis : RecoveryAxisBounds s t p u l α d)
    (target a n : ℕ) (ha : a < s) (hfit : a+n ≤ s) :
    let N := (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card
    let stage := initialSchurTarget p u
      (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N) 2
    ∀ (Fs : List (ZMod s → GaussianInt))
      (hF : ∀ F ∈ Fs, ∀ i, ‖value (executionPrecision p l stage 2) (F i)‖ ≤ (2 : ℝ)^2),
      recoveryMasterValues (axis.cyclicLeftReplicaProblem stage 2 a n ha Fs hF) =
        inverseMasterValues p u l target s t a (a+n) := by
  dsimp only
  intro Fs hF
  let stage := initialSchurTarget p u
    (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
      (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2
  change masterHeaderValues (2^15*p) (executionStagePrecision p l stage 2+1)
    (executionPrecision p l stage 2) l s t u (PhaseCellBand.width p u) a (a+min n (s-a)) = _
  have hmin : min n (s-a) = n := by omega
  rw [hmin]
  unfold inverseMasterValues
  dsimp only [stage]
  rw [cyclicPrincipalBoundary_of_fits t (PhaseCellBand.width p u) a n ha hfit]
  simp only [executionStagePrecision,executionPrecision,←inverseExecutionExponent_eq]
  rfl

/-- The empty right piece shares all eight numerical/dimension masters. Its
two physical endpoints are zero, so it needs no second scalar generation. -/
theorem RecoveryAxisBounds.fittingCyclicRightMasterValues
    {p l s t u : ℕ} [NeZero s] {α d : ℝ} (axis : RecoveryAxisBounds s t p u l α d)
    (stage a n : ℕ) (ha : a < s) (hn : n ≤ s) (hfit : a+n ≤ s)
    (Fs : List (ZMod s → GaussianInt))
    (hF : ∀ F ∈ Fs, ∀ i, ‖value (executionPrecision p l stage 2) (F i)‖ ≤ (2 : ℝ)^2) (i : Fin 10) :
    recoveryMasterValues (axis.cyclicRightReplicaProblem stage 2 a n hn Fs hF) i =
      if i.val < 8 then recoveryMasterValues (axis.cyclicLeftReplicaProblem stage 2 a n ha Fs hF) i else 0 := by
  change masterHeaderValues (2^15*p) (executionStagePrecision p l stage 2+1)
      (executionPrecision p l stage 2) l s t u (PhaseCellBand.width p u) 0 (0+(n-min n (s-a))) i =
    if i.val < 8 then masterHeaderValues (2^15*p) (executionStagePrecision p l stage 2+1)
      (executionPrecision p l stage 2) l s t u (PhaseCellBand.width p u) a (a+min n (s-a)) i else 0
  have hempty : n-min n (s-a) = 0 := by omega
  rw [hempty]
  fin_cases i <;> rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
