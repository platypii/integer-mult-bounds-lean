module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicBoundaryRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedResidualLift
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

noncomputable def physicalCyclicBoundaryRecovery (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 224 Q A U :=
  embProg boundaryFactorLegacyReg id (embProg tableReg id (embProg boundaryArithmeticReg id (cyclicRecoveryPasses hR hQ)))

theorem physicalCyclicBoundaryRecovery_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    ∀ (v : HS 224 Q A U) (S : Stacks 224 A) (tail sourceTail : List (Fin (A+4))),
    LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u band 0 0 (cstream A w (chirpLine s rhs)++tail) (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S)))) →
    (S.R 144).length = a → (S.R 145).length = a+min n (s-a) →
    (S.R 146).length = n-min n (s-a) →
    (∀ k ∈ ([(127 : Fin 224),138,141,142,143]), S.R k = []) →
    S.R 132 = cstream A w (chirpLine s Y)++sourceTail →
    ∃ v' m, ∃ D E : ZMod s → GaussianInt,
      v'.user = v.user ∧
      m ≤ archivedWindowedRecoveryCost p l s t u (recoveryTarget p bits) 2 (stableInteriorExponent p 2) a (a+min n (s-a))+
        archivedWindowedRecoveryCost p l s t u (recoveryTarget p bits) 2 (stableInteriorExponent p 2) 0 (n-min n (s-a)) ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) (physicalCyclicBoundaryRecovery hR hQ) (mk v S) m
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
  let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let bits := boundaryTableBits p (boundaryRecoveryTarget p target) 2 B.card
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let E₀ := embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S))
  obtain ⟨v₁,m,D,E,hv₁,hm,he,haccuracy⟩ := cyclicBoundaryRecovery_spec (body := body)
    hR hQ hA axis ha hn target rhs solution hrhs hmag
    (embDn boundaryArithmeticReg (embDn tableReg (embDn boundaryFactorLegacyReg v))) E₀ tail sourceTail
    hready haSrc hleftEnd hrightEnd
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
        simpa [E₀,embStk,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using hfresh _ (by simp)) hsource
  let archive := cstream A w (chirpLine s E)++(cstream A w (chirpLine s D)++S.R 147)
  have he₁ : Exec (embTab componentReg (embTab groupReg body)) (cyclicRecoveryPasses hR hQ)
      (mk (embDn boundaryArithmeticReg (embDn tableReg (embDn boundaryFactorLegacyReg v))) E₀) m
      (mk v₁ {E₀ with R := Function.update (Function.update E₀.R 147 archive) 147 archive}) := by
    simpa [Function.update_idem,archive,w,bits,B,E₀,embStk,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using he
  obtain ⟨v₂,hv₂,he₂⟩ := exec_emb_two_outputs boundaryArithmeticReg boundaryArithmeticReg_injective
    (embTab componentReg (embTab groupReg body)) (cyclicRecoveryPasses hR hQ)
    (embDn tableReg (embDn boundaryFactorLegacyReg v)) (embStk tableReg (embStk boundaryFactorLegacyReg S))
    v₁ m 147 147 archive archive hv₁ he₁
  obtain ⟨v₃,hv₃,he₃⟩ := exec_emb_two_outputs tableReg tableReg_injective
    (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))
    (embProg boundaryArithmeticReg id (cyclicRecoveryPasses hR hQ))
    (embDn boundaryFactorLegacyReg v) (embStk boundaryFactorLegacyReg S) v₂ m 147 147 archive archive hv₂ he₂
  obtain ⟨v₄,hv₄,he₄⟩ := exec_emb_two_outputs boundaryFactorLegacyReg boundaryFactorLegacyReg_injective
    (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
    (embProg tableReg id (embProg boundaryArithmeticReg id (cyclicRecoveryPasses hR hQ)))
    v S v₃ m 147 147 archive archive hv₃ he₃
  refine ⟨v₄,m,D,E,hv₄,hm,?_,haccuracy⟩
  simpa [Function.update_idem,physicalCyclicBoundaryRecovery,boundaryFactorLegacyReg,archive,w,bits,B] using he₄

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
