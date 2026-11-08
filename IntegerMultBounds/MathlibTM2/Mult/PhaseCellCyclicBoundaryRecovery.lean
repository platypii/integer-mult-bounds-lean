module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryPasses
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryAccuracy

/-! The executed recovery archive has the target accuracy for the original cyclic system. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

theorem cyclicBoundaryRecovery_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {s t p u l a n : ℕ} [NeZero s] {alpha gap : ℝ}
    (axis : RecoveryAxisBounds s t p u l alpha gap) (ha : a < s) (hn : n ≤ s) (target : ℕ) :
    let band := PhaseCellBand.width p u
    let B := cyclicPrincipalBoundary s t band a n
    let solveTarget := boundaryRecoveryTarget p target
    let bits := boundaryTableBits p solveTarget 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ∀ (rhs : ZMod s → GaussianInt) (solution : List GaussianInt),
    let Y := boundarySolutionField B solution
    (∀ i, ‖value q (rhs i)‖ ≤ (2 : ℝ)^2) →
    (∀ i < B.card, ‖value q (solution.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p 2) →
    ∀ (v : HS 148 Q A U) (S : Stacks 148 A) (tail sourceTail : List (Fin (A+4))),
    LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u band 0 0 (cstream A w (chirpLine s rhs)++tail) (embStk componentReg S) →
    (S.R 144).length = a → (S.R 145).length = a+min n (s-a) →
    (S.R 146).length = n-min n (s-a) →
    (∀ k ∈ ([(127 : Fin 148),138,141,142,143]), S.R k = []) →
    S.R 132 = cstream A w (chirpLine s Y)++sourceTail →
    ∃ v' m, ∃ D E : ZMod s → GaussianInt,
      v'.user = v.user ∧
      m ≤ archivedWindowedRecoveryCost p l s t u (recoveryTarget p bits) 2 (stableInteriorExponent p 2) a (a+min n (s-a))+
        archivedWindowedRecoveryCost p l s t u (recoveryTarget p bits) 2 (stableInteriorExponent p 2) 0 (n-min n (s-a)) ∧
      Exec (embTab componentReg (embTab groupReg body)) (cyclicRecoveryPasses hR hQ) (mk v S) m
        (mk v' {S with R := (Function.update S.R 147
          (cstream A w (chirpLine s E)++(cstream A w (chirpLine s D)++S.R 147)))}) ∧
      ∀ x : ZMod s → ℝ,
        SchurDominance.Solves (realMatrix s t p u) (cyclicPrincipalVertices s a n) x
          (fun i => (value q (rhs i)).re) →
        (∀ i < B.card, ‖value q (solution.getD i 0)-(x (bFoldAt s B i) : ℂ)‖ ≤ 3/(2 : ℝ)^solveTarget) →
        PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
          (SchurDominance.glue (cyclicPrincipalInterior s t band a n)
            (fun i => if i ∈ haloInterior s t band a (a+min n (s-a)) then (value q (D i)).re else (value q (E i)).re)
            (fun i => (value q (Y i)).re)) x (1/(2 : ℝ)^target) := by
  dsimp only
  intro rhs solution hrhs hmag v S tail sourceTail hready haSrc hleftEnd hrightEnd hfresh hsource
  let band := PhaseCellBand.width p u
  let B := cyclicPrincipalBoundary s t band a n
  let bits := boundaryTableBits p (boundaryRecoveryTarget p target) 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let Y := boundarySolutionField B solution
  have hY := boundarySolutionField_magnitude q (stableInteriorExponent p 2) B solution hmag
  obtain ⟨v',m,D,E,xI,yI,hv,hm,he,hnorm,hxI,hyI,hD,hE,hsolve,herror⟩ := cyclicRecoveryPasses_spec
    (body := body) (target := recoveryTarget p bits) (rhsExp := 2) (boundaryExp := stableInteriorExponent p 2)
    hR hQ hA axis ha hn Y rhs hrhs hY v S tail sourceTail hready haSrc hleftEnd hrightEnd hfresh hsource
  refine ⟨v',m,D,E,hv,hm,he,?_⟩
  intro x hx hboundary
  have h := cyclicRecovery_solution_target axis ha hn target rhs hrhs solution D E x
    (fun i => if i ∈ haloInterior s t band a (a+min n (s-a)) then xI i else yI i)
    hmag hboundary hx (by simpa only [apply_ite,bits,B,band,Y,initialSchurTarget] using hsolve)
    (by simpa only [apply_ite,bits,B,band,initialSchurTarget] using herror)
  simpa only [apply_ite] using h

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
