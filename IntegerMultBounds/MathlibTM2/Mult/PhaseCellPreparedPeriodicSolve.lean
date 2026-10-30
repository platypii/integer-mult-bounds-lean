module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPeriodicProducerPreparation

/-! The actual full-line preparation, residual producer and boundary solve are
one execution. No intermediate producer-readiness premise is supplied by callers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open ScalarPlacement IntegerMultBounds.MathlibTM2.Node
variable {A Q : ℕ} {P U : Type} {body : P → Pr P 242 Q A U}

theorem preparedPeriodicSolve_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (p u l target : ℕ) {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hp : 2 ≤ p)
    (stage V t band : ℕ) (C R : ZMod s → GaussianInt) {α d : ℝ}
    (hBset : B = haloBoundary s t band 0 s) (hst : s < t) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p) :
    let bits := boundaryTableBits p target 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    let AZ := factorRankIntegerMatrix B W columns
    let Lc := naturalLineLc q K W B.card AZ
    let Uc := naturalLineUc q K W B.card AZ
    let rcs := naturalLineRcs q K W B.card AZ
    PreparedBoundaryColumns A p bits q w W B columns →
    2*band+1 ≤ 2^couplingCountExponent p u →
    (∀ j, ‖value q (R j)‖ ≤ (2 : ℝ)^2) →
    (∀ j ∈ haloInterior s t band 0 s, ‖value q (C j)‖ ≤ (2 : ℝ)^stableInteriorExponent p 2) →
    let rhs := (bFoldOrder s B).map (couplingRowField (2^15*p) q t u band 0 s false C R)
    ∀ (v : HS 242 Q A U) (S : Stacks 242 A),
    ∀ rhsTail : List (Fin (A+4)),
    let e : Fin 168 → Fin 242 := Fin.castLE (by decide)
    let T := periodicPreparedProducerBank p q s t u band S
    let F := embOvr e (ScalarPlacement.periodicBoundaryResult (embStk e T) V s t band 0 s w
      (ScalarPlacement.guardedCouplingRowField (2^15*p) q t u band 0 s false C R)
      (couplingRowField (2^15*p) q t u band 0 s false C R) rhsTail).get T
    let G := {F with R := (Function.update (Function.update F.R 143 []) 238
          (cstream A w ((bandSolveVec q W Lc Uc rcs (rhs.map (normalizeBoundaryWord q (q/2-1)))).map
            (unscaleBoundaryWord q))++F.R 238))}
    PackedHaloBetweenInputs (2^15*p) stage q l s t u band 0 s V w W B.card (extendStacks (by decide) S) →
    band ≤ s →
    8*(t+1)^2+4*band+8 < 2^V →
    (s+2*band)+s < 2^V →
    S.R 132 = cstream A w (chirpLine s C) →
    S.R 93 = cstream A w (packedInterval 0 s R)++rhsTail →
    S.R 160 = [] →
    PackedBoundaryFactorPages (cstream A w (Lc.map colC).flatten)
      (cstream A w (Uc.map colC).flatten)
      (cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt))) S →
    ∃ v' n, v'.user = v.user ∧ n ≤ periodicProducerPreparationCost p q s t u band V+(periodicProducerCost p q w s t u band 0 s V+preparedResidualSolveCost q w B.card W) ∧
      Exec body (.seq periodicPrepareProducer (.seq (embProg e Empty.elim (.seq (.seq (.seq ScalarPlacement.prepareFullLineRibbon
        (ScalarPlacement.completedGatheredFeedCouplingInterval hQ false)) (uclear 160)) packedBoundaryData))
        (packedPreparedResidualSolve hQ))) (mk v S) n
        (mk v' G) ∧ PackedPreparedBank q w W B.card G ∧
      PackedBoundaryFactorPages (cstream A w (Lc.map colC).flatten)
        (cstream A w (Uc.map colC).flatten)
        (cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt))) G ∧
      PeriodicProducerInput p q w t u band 0 s V C R [] rhsTail (S.R 110)
        (embStk (Fin.castLE (by decide : 168 ≤ 242)) T) := by
  dsimp only
  intro hcolumns hcount hR hC v S rhsTail hbetween hband hwide hfitV hsource hrhs h160 hpages
  let bits := boundaryTableBits p target 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  have hw : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  have hprep := periodicPrepareProducer_exec (body := body) (p := p) (q := q) (stage := stage) (l := l) (W := W) (N := B.card) (by omega) (by omega) hst hband hwide hfitV C R rhsTail v S
    (by simpa only [← hw] using hbetween) (by simpa only [← hw] using hsource)
    (by simpa only [← hw] using hrhs) h160
  simp only [← hw] at hprep
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hin,hbankT,hpagesT⟩ := hprep
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂,hbankG,hpagesG⟩ := periodicProducerSolve_exec (body := body)
    hQ hA p u l target B W columns hp V t band 0 s C R hBset hst hαu hθ hgap hbudget
    hcolumns hcount hR hC v₁ (periodicPreparedProducerBank p q s t u band S) rhsTail [] (S.R 110)
    hin hbankT (hpagesT _ _ _ hpages)
  exact ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂,hbankG,hpagesG,hin⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
