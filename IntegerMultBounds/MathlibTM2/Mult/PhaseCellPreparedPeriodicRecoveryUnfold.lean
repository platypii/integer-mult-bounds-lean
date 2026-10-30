module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedPeriodicSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryRecoveryUnfold

/-! Execute the computed periodic boundary solve and unfold its actual solution.
The recovery workspace is allocated as a blank extension of the solver bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open ScalarPlacement IntegerMultBounds.MathlibTM2.Node
variable {A Q : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

theorem preparedPeriodicRecoveryUnfold_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    ∀ (v : HS 248 Q A U) (S : Stacks 242 A),
    ∀ rhsTail : List (Fin (A+4)),
    let e : Fin 168 → Fin 242 := Fin.castLE (by decide)
    let T := periodicPreparedProducerBank p q s t u band S
    let F := embOvr e (ScalarPlacement.periodicBoundaryResult (embStk e T) V s t band 0 s w
      (ScalarPlacement.guardedCouplingRowField (2^15*p) q t u band 0 s false C R)
      (couplingRowField (2^15*p) q t u band 0 s false C R) rhsTail).get T
    let solution := (bandSolveVec q W Lc Uc rcs (rhs.map (normalizeBoundaryWord q (q/2-1)))).map
      (unscaleBoundaryWord q)
    let G := {F with R := (Function.update (Function.update F.R 143 []) 238
      (cstream A w solution++F.R 238))}
    let H := extendStacks (by decide : 242 ≤ 248) G
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
    ∃ v' n, v'.user = v.user ∧
      n ≤ (periodicProducerPreparationCost p q s t u band V+
        (periodicProducerCost p q w s t u band 0 s V+preparedResidualSolveCost q w B.card W))+
        (moveCountedLineCost B.card w+(generatedBoundaryUnfoldCost B.card w+B.card*(12*w+9)+12)) ∧
      Exec body (.seq (embProg (Fin.castLE (by decide : 242 ≤ 248)) Empty.elim
        (.seq periodicPrepareProducer (.seq (embProg e Empty.elim (.seq (.seq (.seq prepareFullLineRibbon
          (completedGatheredFeedCouplingInterval hQ false)) (uclear 160)) packedBoundaryData))
          (packedPreparedResidualSolve hQ)))) packedBoundarySolutionUnfold)
        (mk v (extendStacks (by decide : 242 ≤ 248) S)) n
        (mk v' {H with R := (Function.update (Function.update (Function.update H.R 238 (F.R 238)) 231 [])
          245 (cstream A w ((bOrder s B).map (boundarySolutionField B solution))))}) ∧
      PackedPreparedBank q w W B.card G := by
  dsimp only
  intro hcolumns hcount hR hC v S rhsTail hbetween hband hwide hfitV hsource hrhs h160 hpages
  let bits := boundaryTableBits p target 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let K := factorNewtonSteps p q
  let AZ := factorRankIntegerMatrix B W columns
  let rhs := (bFoldOrder s B).map (couplingRowField (2^15*p) q t u band 0 s false C R)
  let solution := (bandSolveVec q W (naturalLineLc q K W B.card AZ) (naturalLineUc q K W B.card AZ)
    (naturalLineRcs q K W B.card AZ) (rhs.map (normalizeBoundaryWord q (q/2-1)))).map (unscaleBoundaryWord q)
  let T := periodicPreparedProducerBank p q s t u band S
  let e : Fin 168 → Fin 242 := Fin.castLE (by decide)
  let F := embOvr e (periodicBoundaryResult (embStk e T) V s t band 0 s w
    (guardedCouplingRowField (2^15*p) q t u band 0 s false C R)
    (couplingRowField (2^15*p) q t u band 0 s false C R) rhsTail).get T
  let G : Stacks 242 A := {F with R := (Function.update (Function.update F.R 143 []) 238
    (cstream A w solution++F.R 238))}
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hbank,_⟩ := preparedPeriodicSolve_exec
    (body := fun f : Empty => nomatch f) hQ hA p u l target B W columns hp stage V t band C R
    hBset hst hαu hθ hgap hbudget hcolumns hcount hR hC
    (embDn (Fin.castLE (by decide : 242 ≤ 248)) v) S rhsTail hbetween hband hwide hfitV hsource hrhs h160 hpages
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_extendStacks (body' := body) (ι := Empty.elim)
    (by decide : 242 ≤ 248) (fun f => nomatch f) he₁ v rfl
  have hlen : solution.length = B.card := by
    simpa only [solution,List.length_map] using naturalLineSolve_length q K W B.card AZ
      (rhs.map (normalizeBoundaryWord q (q/2-1))) (by simp [rhs,bFoldOrder_length])
  have hcountF : F.R 116 = List.replicate B.card tick := by
    have hinj : Function.Injective e := by
      intro i j he
      exact Fin.ext (congrArg (fun k : Fin 242 => k.val) he)
    have hh := embOvr_get hinj (periodicBoundaryResult (embStk e T) V s t band 0 s w
      (guardedCouplingRowField (2^15*p) q t u band 0 s false C R)
      (couplingRowField (2^15*p) q t u band 0 s false C R) rhsTail).get T (.rt 116)
    change F.R 116 = ((periodicBoundaryResult (embStk e T) V s t band 0 s w
      (guardedCouplingRowField (2^15*p) q t u band 0 s false C R)
      (couplingRowField (2^15*p) q t u band 0 s false C R) rhsTail).R 116).map id at hh
    simpa [periodicBoundaryResult,hBset] using hh
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := preparedBoundaryRecoveryUnfold_exec (body := body) (by omega)
    q w W B solution hlen (F.R 238) v₂ G hbank (by simp [G])
    (by simpa [G] using hcountF) (by simp [G])
  exact ⟨v₃,n₁+n₃,hu₃.trans (hu₂.trans hu₁),Nat.add_le_add hn₁ hn₃,Exec.seq he₂ he₃,hbank⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
