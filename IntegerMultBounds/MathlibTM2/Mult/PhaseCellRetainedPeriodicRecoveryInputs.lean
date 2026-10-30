module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedPeriodicRecoveryField
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPeriodicRetainedRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPeriodicRawFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryRhsInput

/-! Retain the RHS, execute the periodic boundary solve and publication, then
restore the original RHS for recovery and release the consumed count and mask. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open ScalarPlacement IntegerMultBounds.MathlibTM2.Node
variable {A Q : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

noncomputable def retainedPeriodicRecoveryInputs (hQ : SS.states ≤ Q) : Pr P 248 Q A U :=
  .seq (embProg (Fin.castLE (by decide : 242 ≤ 248)) Empty.elim periodicRetainRhs)
    (.seq (preparedPeriodicRecoveryField hQ) packedRecoveryRhsInput)

theorem retainedPeriodicRecoveryInputs_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    let S₀ := {S with R := Function.update S.R 110 (cstream A w (packedInterval 0 s R)++S.R 110)}
    let e : Fin 168 → Fin 242 := Fin.castLE (by decide)
    let T := periodicPreparedProducerBank p q s t u band S₀
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
    let Z := {U with R := (Function.update (Function.update (Function.update U.R
      246 (List.replicate s tick)) 245 []) 132
      (cstream A w (packedInterval 0 s (boundarySolutionField B solution))))}
    let D := {Z with R := (Function.update (Function.update (Function.update
      (Function.update (Function.update Z.R 110 (cstream A w (packedInterval 0 s R)++S.R 110))
        93 (cstream A w (packedInterval 0 s R)++Z.R 93)) 116 []) 167 []) 246 [])}
    ∃ v' n, v'.user = v.user ∧ n ≤ copyCountedLineCost s w+(((periodicProducerPreparationCost p q s t u band V+
        (periodicProducerCost p q w s t u band 0 s V+preparedResidualSolveCost q w B.card W))+
        (moveCountedLineCost B.card w+(generatedBoundaryUnfoldCost B.card w+B.card*(12*w+9)+12)))+
        ((6*s+11*V+6)+(s*(6*w+10)+6))+packedRecoveryRhsInputCost s B.card w) ∧
      Exec body (retainedPeriodicRecoveryInputs hQ) (mk v (extendStacks (by decide : 242 ≤ 248) S)) n
        (mk v' D) ∧ D.R 110 = cstream A w (packedInterval 0 s R)++S.R 110 := by
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
  let words := cstream A w (packedInterval 0 s R)
  let S₀ : Stacks 242 A := {S with R := Function.update S.R 110 (words++S.R 110)}
  let T := periodicPreparedProducerBank p q s t u band S₀
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
  let Z : Stacks 248 A := {U with R := (Function.update (Function.update (Function.update U.R
    246 (List.replicate s tick)) 245 []) 132 (cstream A w (packedInterval 0 s (boundarySolutionField B solution))))}
  have hlen : words.length = s*w := by simp [words,packedInterval]
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hbetween₀,hpages₀⟩ := periodicRetainRhs_exec
    (body := fun f : Empty => nomatch f) words rhsTail hlen
    (embDn (Fin.castLE (by decide : 242 ≤ 248)) v) S hbetween hrhs
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_extendStacks (body' := body) (ι := Empty.elim)
    (by decide : 242 ≤ 248) (fun f => nomatch f) he₁ v rfl
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := preparedPeriodicRecoveryField_exec (body := body)
    hQ hA p u l target B W columns hp stage V t band C R hBset hst hαu hθ hgap hbudget
    hcolumns hcount hR hC v₂ S₀ rhsTail hbetween₀ hband hwide hfitV
    (by simpa [S₀] using hsource) (by simpa [S₀] using hrhs) (by simpa [S₀] using h160)
    (hpages₀ _ _ _ hpages)
  have hinj : Function.Injective e := by
    intro i j he; exact Fin.ext (congrArg (fun k : Fin 242 => k.val) he)
  have hh := embOvr_get hinj J.get T (.rt 110)
  change F.R 110 = (J.R 110).map id at hh
  have h110F : F.R 110 = cstream A w (packedInterval 0 s
      (guardedCouplingRowField (2^15*p) q t u band 0 s false C R))++T.R 110 := by
    simpa [J,periodicBoundaryResult,fullLineCouplingResult,completedCouplingIntervalR,embStk,e] using hh
  have h110T : T.R 110 = words++S.R 110 := by
    rw [periodicPreparedProducerBank_raw]
    rfl
  have h110Z : Z.R 110 = F.R 110 := by simp [Z,U,H,G,extendStacks]
  have hqueue : Z.R 110 = cstream A w (packedInterval 0 s
      (guardedCouplingRowField (2^15*p) q t u band 0 s false C R))++(words++S.R 110) := by
    rw [h110Z,h110F,h110T]
  have hbankS := hbetween.bank
  simp only [packedBoundaryRecoveryBase,embStk_extendStacks] at hbankS
  have h174F : F.R 174 = S.R 174 := by
    change (embOvr e J.get T).R 174 = _
    rw [embOvr_prefix_right (by decide : 168 ≤ 242) J T 174 (by decide)]
    exact (periodicPreparedProducerBank_base p q t u band S₀ 174 (by decide) (by decide)).trans (by simp [S₀])
  have hwidth : (Z.R 174).length = w := by
    have hh := packedBoundaryRecovery_width hbankS.ready
    have hz : Z.R 174 = S.R 174 := by
      simpa [Z,U,H,G,extendStacks] using h174F
    rw [hz]
    exact hh
  have hcountZ : Z.R 116 = List.replicate B.card tick := by
    have hh := embOvr_get hinj J.get T (.rt 116)
    change F.R 116 = (J.R 116).map id at hh
    have hf : F.R 116 = List.replicate B.card tick := by simpa [J,periodicBoundaryResult,hBset] using hh
    simpa [Z,U,H,G,extendStacks] using hf
  have hmaskZ : Z.R 167 = couplingSourceIntervalMaskSymbols true A s t band 0 s 0 s := by
    have hh := embOvr_get hinj J.get T (.rt 167)
    change F.R 167 = (J.R 167).map id at hh
    have hf : F.R 167 = couplingSourceIntervalMaskSymbols true A s t band 0 s 0 s := by
      simpa [J,periodicBoundaryResult] using hh
    simpa [Z,U,H,G,extendStacks] using hf
  have hclean : ∀ k ∈ ([247,242,243,244] : List (Fin 248)), Z.R k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> simp [Z,U,H,extendStacks]
  obtain ⟨v₄,n₄,hu₄,hn₄,he₄⟩ := packedRecoveryRhsInput_exec (body := body) s B.card w
    (cstream A w (packedInterval 0 s (guardedCouplingRowField (2^15*p) q t u band 0 s false C R)))
    words (S.R 110) (by simp [packedInterval]) hlen v₃ Z
    (by simp [Z]) hwidth (by rw [hcountZ]; simp)
    (by rw [hmaskZ]; exact couplingSourceIntervalMaskSymbols_length _ _ _ _ _ _ _ _ _) hqueue hclean
  refine ⟨v₄,n₁+(n₃+n₄),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    Nat.add_le_add hn₁ (Nat.add_le_add hn₃ hn₄),Exec.seq he₂ (Exec.seq he₃ he₄),?_⟩
  simp

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
