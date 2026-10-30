module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedPeriodicRecoveryUnfold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPeriodicPreparationFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPeriodicBoundaryPublish

/-! Execute the periodic solve, inverse fold and full boundary-field publication.
All publication conditions follow from the actual computed endpoint. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open ScalarPlacement IntegerMultBounds.MathlibTM2.Node
variable {A Q : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

noncomputable def preparedPeriodicRecoveryField (hQ : SS.states ≤ Q) : Pr P 248 Q A U :=
  .seq (.seq (embProg (Fin.castLE (by decide : 242 ≤ 248)) Empty.elim
    (.seq periodicPrepareProducer (.seq (embProg (Fin.castLE (by decide : 168 ≤ 242)) Empty.elim
      (.seq (.seq (.seq prepareFullLineRibbon (completedGatheredFeedCouplingInterval hQ false))
        (uclear 160)) packedBoundaryData)) (packedPreparedResidualSolve hQ)))) packedBoundarySolutionUnfold)
    periodicBoundaryPublish

theorem preparedPeriodicRecoveryField_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    let U := {H with R := (Function.update (Function.update (Function.update H.R 238 (F.R 238)) 231 [])
      245 (cstream A w ((bOrder s B).map (boundarySolutionField B solution))))}
    ∃ v' n, v'.user = v.user ∧
      n ≤ ((periodicProducerPreparationCost p q s t u band V+
        (periodicProducerCost p q w s t u band 0 s V+preparedResidualSolveCost q w B.card W))+
        (moveCountedLineCost B.card w+(generatedBoundaryUnfoldCost B.card w+B.card*(12*w+9)+12)))+
        ((6*s+11*V+6)+(s*(6*w+10)+6)) ∧
      Exec body (preparedPeriodicRecoveryField hQ) (mk v (extendStacks (by decide : 242 ≤ 248) S)) n
        (mk v' {U with R := (Function.update (Function.update (Function.update U.R
          246 (List.replicate s tick)) 245 []) 132
          (cstream A w (packedInterval 0 s (boundarySolutionField B solution))))}) := by
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
  let J := periodicBoundaryResult (embStk e T) V s t band 0 s w
    (guardedCouplingRowField (2^15*p) q t u band 0 s false C R)
    (couplingRowField (2^15*p) q t u band 0 s false C R) rhsTail
  let F := embOvr e J.get T
  let G : Stacks 242 A := {F with R := (Function.update (Function.update F.R 143 []) 238
    (cstream A w solution++F.R 238))}
  let H := extendStacks (by decide : 242 ≤ 248) G
  let U : Stacks 248 A := {H with R := (Function.update (Function.update (Function.update H.R 238 (F.R 238))
    231 []) 245 (cstream A w ((bOrder s B).map (boundarySolutionField B solution))))}
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hbank⟩ := preparedPeriodicRecoveryUnfold_exec (body := body)
    hQ hA p u l target B W columns hp stage V t band C R hBset hst hαu hθ hgap hbudget
    hcolumns hcount hR hC v S rhsTail hbetween hband hwide hfitV hsource hrhs h160 hpages
  change PackedPreparedBank q w W B.card G at hbank
  have hinj : Function.Injective e := by
    intro i j he
    exact Fin.ext (congrArg (fun k : Fin 242 => k.val) he)
  have hread (i : Fin 168) : F.R (e i) = J.R i := by
    have hh := embOvr_get hinj J.get T (.rt i)
    change F.R (e i) = (J.R i).map id at hh
    simpa only [List.map_id] using hh
  have h165S : S.R 165 = binSyms V s := by
    have hh := hbetween.headers.geometry.count
    simpa [embStk,packedRecoveryRuntimeReg,extendStacks,Nat.sub_zero] using hh
  have h165F : F.R 165 = binSyms V s := by
    change F.R (e 165) = _
    rw [hread]
    have hh := periodicBoundaryResult_frame (embStk e T) V s t band 0 s w
      (guardedCouplingRowField (2^15*p) q t u band 0 s false C R)
      (couplingRowField (2^15*p) q t u band 0 s false C R) rhsTail 165 (by decide)
    change J.R 165 = T.R 165 at hh
    rw [hh]
    exact (periodicPreparedProducerBank_base p q t u band S 165 (by decide) (by decide)).trans h165S
  have hmaskF : F.R 167 = couplingSourceIntervalMaskSymbols true A s t band 0 s 0 s := by
    change F.R (e 167) = _
    rw [hread]
    simp [J,periodicBoundaryResult]
  have h132F : F.R 132 = [] := by
    change F.R (e 132) = _
    rw [hread]
    have hh := periodicBoundaryResult_frame (embStk e T) V s t band 0 s w
      (guardedCouplingRowField (2^15*p) q t u band 0 s false C R)
      (couplingRowField (2^15*p) q t u band 0 s false C R) rhsTail 132 (by decide)
    change J.R 132 = T.R 132 at hh
    exact hh.trans (periodicPreparedProducerBank_archive p q t u band S)
  have hlow (i : Fin 64) : G.R ⟨i.val,by omega⟩ = [] := by
    have hi := i.isLt
    simpa [embStk,preparedBoundaryCoreReg,packedBoundaryFactorReg,boundaryFactorMulReg,Fin.ext_iff,
      show i.val ≠ 140 by omega,show i.val ≠ 143 by omega,
      show i.val ≠ 206 by omega,show i.val < 154 by omega] using hbank.workspace.mul i
  have hclean : ∀ k ∈ ([0,1,2,246,242,243,244] : List (Fin 248)), U.R k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [U,H,extendStacks] using hlow 0
    · simpa [U,H,extendStacks] using hlow 1
    · simpa [U,H,extendStacks] using hlow 2
    all_goals simp [U,H,extendStacks]
  have hN : U.R 165 = binSyms V s := by simpa [U,H,G,extendStacks] using h165F
  have hmask : U.R 167 = couplingSourceIntervalMaskSymbols true A s t band 0 s 0 s := by
    simpa [U,H,G,extendStacks] using hmaskF
  have hw : (U.R 174).length = w := by
    have hh := packedBoundaryRecovery_width hbank.ready
    change (G.R 174).length = w at hh
    simpa [U,H,extendStacks] using hh
  have harchive : U.R 132 = [] := by simpa [U,H,G,extendStacks] using h132F
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := periodicBoundaryPublish_exec (body := body) hst (by omega) V band w (by omega)
    (boundarySolutionField B solution) (by
      intro i hi
      exact boundarySolutionField_off B solution i (by simpa only [hBset] using hi)) v₁ U hN hw
    (by simp [U,hBset]) hmask hclean
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  simp only [harchive,List.append_nil]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
