module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaExportedBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaBoundarySolutionAccuracy

/-! Cached residual certificates feed one executed export/factor/solve chain.
Both original RHS queues and cached banks survive for the recovery passes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open CyclicReplicaPlacement
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

noncomputable def cyclicReplicaConsumerBatch (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 834 Q A U :=
  .seq cyclicReplicaConsumerExport (embProg factorReg id (constructedCyclicResidualBatch hR hQ))

theorem cyclicReplicaConsumerBatch_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a n : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (ha : a < s) (hn : n ≤ s) :
    let band := PhaseCellBand.width p u
    let B := cyclicPrincipalBoundary s t band a n
    let bits := boundaryTableBits p target 2 B.card
    let cellTarget := initialSchurTarget p u bits 2
    let q := executionPrecision p l cellTarget 2
    let w := executionWidth p l cellTarget 2
    ∀ (Fs : List (ZMod s → GaussianInt))
      (hF : ∀ F ∈ Fs, ∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2),
    let H := axis.cyclicLeftReplicaProblem cellTarget 2 a n ha Fs hF
    let K := axis.cyclicRightReplicaProblem cellTarget 2 a n hn Fs hF
    ∀ (leftBuffers rightBuffers : ReplicaLoopBuffers A) (S₀ S₁ : Stacks 834 A)
      (Cs Ds : List (ZMod s → GaussianInt)) (v : HS 834 Q A U)
      (S : Stacks 834 A) (raw : Stacks 234 A) (tail pageTail : List (Fin (A+4))),
    CachedReplicaPassPost H left leftBuffers S₀ S Cs →
    CachedReplicaPassPost K right rightBuffers S₁ S Ds →
    CyclicResidualBatchInput p l s t u target a n tail pageTail raw →
    S.inp = raw.inp → S.out = raw.out → (embStk factorReg S).L = raw.L →
    (∀ k : Fin 234, k ≠ 170 → k ≠ 173 → S.R (factorReg k) = raw.R k) →
    (∀ k ∈ [(130 : Fin 234),168,169,171,172,174,175,229], S.R (factorReg k) = []) →
    S.R (factorReg 170) = couplingSourceIntervalMaskSymbols true A s t band
      a (a+min n (s-a)) a (min n (s-a)) →
    S.R (factorReg 173) = couplingSourceIntervalMaskSymbols true A s t band
      0 (n-min n (s-a)) 0 (n-min n (s-a)) →
    (∀ r : Fin 180, r.val < 80 → S.R (factorReg (cyclicResidualRowsReg r)) = []) →
    (∀ r ∈ [(134 : Fin 180),135,136,137,143,174,175,176,177,178],
      S.R (factorReg (cyclicResidualRowsReg r)) = []) →
    let rows := (Cs.zip Ds).map (fun z => cyclicReplicaBoundaryRow t band a n z.1 z.2)
    let E := cyclicReplicaConsumerExportState S (cstream A w rows.flatten)
    let T := embStk factorReg E
    let W := 24*band+1
    let iterations := factorNewtonSteps p q
    let consumerCost := ((4*(H.Fs.length+H.wordWidth+H.span*H.wordWidth+K.span*K.wordWidth)+17)+
      (4*(H.Fs.length*(H.span*H.wordWidth)+K.Fs.length*(K.span*K.wordWidth))+8))+
      exportCyclicResidualRowsCost H.Fs.length n B.card H.wordWidth
    ∃ v' page steps, ∃ columns : List (ZMod s → GaussianInt),
      let σ := boundaryFactorState (embStk preparedBoundaryCoreReg (embStk preparedBoundaryBatchCoreReg page))
      let AZ := factorRankIntegerMatrix B W columns
      let solve := fun (b : List GaussianInt) => (bandSolveVec q W (naturalLineLc q iterations W B.card AZ)
        (naturalLineUc q iterations W B.card AZ) (naturalLineRcs q iterations W B.card AZ)
        (b.map (normalizeBoundaryWord q (q/2-1)))).map (unscaleBoundaryWord q)
      let F : Stacks 234 A := {page with R := (Function.update page.R 224
        (cstream A w (rows.map solve).flatten++page.R 224))}
      v'.user = v.user ∧ steps ≤ consumerCost+(constructedCyclicFactorCost p u l s t a n target 2+
        preparedResidualBatchCost q w B.card W Fs.length) ∧
      Exec (embTab factorReg (embTab preparedBoundaryBatchCoreReg (embTab preparedBoundaryCoreReg
        (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
          (embTab componentReg (embTab groupReg body))))))))
        (cyclicReplicaConsumerBatch hR hQ) (mk v S) steps
        (mk v' (embOvr factorReg F.get E)) ∧
      PreparedBoundaryColumns A p bits q w W B columns ∧
      ColumnFamilyAccurate A q w B
        (SchurDominance.run (realMatrix s t p u) (cyclicPrincipalVertices s a n)
          (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n).toList).1 (1/(2 : ℝ)^bits) columns ∧
      BoundarySolveReady σ q w W B.card ∧
      σ .bo = cstream A w ((naturalLineLc q iterations W B.card AZ).map colC).flatten ∧
      σ .hf = cstream A w ((naturalLineUc q iterations W B.card AZ).map colC).flatten ∧
      σ .df = cstream A w ((naturalLineRcs q iterations W B.card AZ).map fun x => (⟨x,0⟩ : GaussianInt)) ∧
      (∀ b ∈ rows, (solve b).length = B.card ∧ ∀ z ∈ solve b, Fits w z) ∧
      boundaryFactorState (embStk preparedBoundaryCoreReg (embStk preparedBoundaryBatchCoreReg F)) = σ ∧
      page.inp = T.inp ∧ page.out = T.out ∧ page.L = T.L ∧
      page.R 224 = T.R 224 ∧ (∀ k : Fin 234, 226 ≤ k.val → page.R k = T.R k) ∧
      (∀ k : Fin 834, (∀ j, factorReg j ≠ k) →
        (embOvr factorReg F.get E).L k = E.L k ∧ (embOvr factorReg F.get E).R k = E.R k) ∧
      embStk left.coupling.bank (embOvr factorReg F.get E) = embStk left.coupling.bank S ∧
      embStk right.coupling.bank (embOvr factorReg F.get E) = embStk right.coupling.bank S ∧
      ReplicaRecoveryRhsHeaders H left.plan.gather leftBuffers (embOvr factorReg F.get E) ∧
      ReplicaRecoveryRhsHeaders K right.plan.gather rightBuffers (embOvr factorReg F.get E) ∧
      (∀ j : Fin Fs.length, ∀ x : ZMod s → ℝ,
        SchurDominance.Solves (realMatrix s t p u) (cyclicPrincipalVertices s a n) x
          (fun k => (value q (Fs.reverse.getD (Fs.length-1-j.val) (fun _ => 0) k)).re) →
        let solution := solve (rows.getD j.val [])
        solution.length = B.card ∧ ∀ i < B.card,
          ‖value q (solution.getD i 0)-(x (bFoldAt s B i) : ℂ)‖ ≤ 3/(2 : ℝ)^target ∧
          ‖value q (solution.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p 2) ∧
      ∃ R : (ZMod s → ℝ) → ZMod s → ℝ,
        (∀ rhs, SchurDominance.Solves (realMatrix s t p u) (cyclicPrincipalInterior s t band a n) (R rhs) rhs) ∧
        ∀ j : Fin Fs.length, ∀ i ∈ B,
          |(value q (cyclicReplicaResidualField a n (Cs.getD j.val (fun _ => 0))
            (Ds.getD j.val (fun _ => 0)) i)).re-
            SchurDominance.residual (realMatrix s t p u) (cyclicPrincipalInterior s t band a n) R
              (fun k => (value q (Fs.reverse.getD (Fs.length-1-j.val) (fun _ => 0) k)).re) i| ≤
            haloResidualError p u q 2 cellTarget := by
  dsimp only
  let band := PhaseCellBand.width p u
  let B := cyclicPrincipalBoundary s t band a n
  let bits := boundaryTableBits p target 2 B.card
  let cellTarget := initialSchurTarget p u bits 2
  let q := executionPrecision p l cellTarget 2
  let w := executionWidth p l cellTarget 2
  intro Fs hF
  let H := axis.cyclicLeftReplicaProblem cellTarget 2 a n ha Fs hF
  let K := axis.cyclicRightReplicaProblem cellTarget 2 a n hn Fs hF
  intro leftBuffers rightBuffers S₀ S₁ Cs Ds v S raw tail pageTail hl hr factory
    hin hout hL hRframe hblank hleftMask hrightMask hwork hfresh
  let rows := (Cs.zip Ds).map (fun z => cyclicReplicaBoundaryRow t band a n z.1 z.2)
  let E := cyclicReplicaConsumerExportState S (cstream A w rows.flatten)
  let native := embTab factorReg (embTab preparedBoundaryBatchCoreReg (embTab preparedBoundaryCoreReg
    (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
      (embTab componentReg (embTab groupReg body)))))))
  have hcount : (S.R (factorReg 116)).length = B.card := by
    rw [hRframe 116 (by decide) (by decide)]
    exact factory.rows
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁,hbankL,hbankR,hrhsL,hrhsR⟩ := cyclicReplicaConsumerExport_exec
    (body := native) axis.hst (by omega) H K leftBuffers rightBuffers S₀ S₁ Cs Ds v S hl hr
    band a n ha hn rfl rfl rfl rfl rfl rfl hblank hleftMask hrightMask hcount hwork hfresh
  have hw : H.wordWidth = w := rfl
  have he₁' : Exec native cyclicReplicaConsumerExport (mk v S) m₁ (mk v₁ E) := by
    simpa only [cyclicReplicaBoundaryRows_stream,hw,E,rows] using he₁
  have hbankL' : embStk left.coupling.bank E = embStk left.coupling.bank S := by
    simpa only [cyclicReplicaBoundaryRows_stream,hw,E,rows] using hbankL
  have hbankR' : embStk right.coupling.bank E = embStk right.coupling.bank S := by
    simpa only [cyclicReplicaBoundaryRows_stream,hw,E,rows] using hbankR
  have hrhsL' : ReplicaRecoveryRhsHeaders H left.plan.gather leftBuffers E := by
    simpa only [cyclicReplicaBoundaryRows_stream,hw,E,rows] using hrhsL
  have hrhsR' : ReplicaRecoveryRhsHeaders K right.plan.gather rightBuffers E := by
    simpa only [cyclicReplicaBoundaryRows_stream,hw,E,rows] using hrhsR
  obtain ⟨hlen,hrows,hreal,hbound⟩ := cyclicReplicaBoundaryRows_format axis cellTarget 2 a n ha hn
    Fs hF Cs Ds hl.length hr.length hl.residual hr.residual
  have hrowsLen : rows.length = Fs.length := hlen
  have hcounter : (S.R (left.plan.gather 121)).length = rows.length := by
    rw [hrowsLen]
    exact hl.recoveryRhs.count
  obtain ⟨vf,page,m₂,columns,hu₂,hm₂,he₂,hprepared,hacc,hsolve,hbo,hhf,hdf,hformat,hfactor,
    hinp,houtp,hleft,h224,hprivate,hframe⟩ := cyclicReplicaExportedBatch_spec (body := body)
    hR hQ hA axis ha hn v₁ S raw tail pageTail factory hin hout hL hRframe
    rows hrows hbound hcounter (hblank 229 (by simp))
  let W := 24*band+1
  let iterations := factorNewtonSteps p q
  let AZ := factorRankIntegerMatrix B W columns
  let solve (b : List GaussianInt) :=
    (bandSolveVec q W (naturalLineLc q iterations W B.card AZ)
      (naturalLineUc q iterations W B.card AZ) (naturalLineRcs q iterations W B.card AZ)
      (b.map (normalizeBoundaryWord q (q/2-1)))).map (unscaleBoundaryWord q)
  let F : Stacks 234 A := {page with R := (Function.update page.R 224
    (cstream A w (rows.map solve).flatten++page.R 224))}
  let G := embOvr factorReg F.get E
  have hpass (k : Fin 834) (hk : left.Owns k ∨ right.Owns k) : G.L k = E.L k ∧ G.R k = E.R k := by
    apply hframe
    intro j he
    rcases hk with hk | hk
    · exact (factor_disjoint j).1 (he.symm ▸ hk)
    · exact (factor_disjoint j).2 (he.symm ▸ hk)
  have hbankLG : embStk left.coupling.bank G = embStk left.coupling.bank E := by
    refine Stacks.ext hinp houtp ?_ ?_
    · funext i; exact (hpass _ (Or.inl (.bank i))).1
    · funext i; exact (hpass _ (Or.inl (.bank i))).2
  have hbankRG : embStk right.coupling.bank G = embStk right.coupling.bank E := by
    refine Stacks.ext hinp houtp ?_ ?_
    · funext i; exact (hpass _ (Or.inr (.bank i))).1
    · funext i; exact (hpass _ (Or.inr (.bank i))).2
  refine ⟨vf,page,m₁+m₂,columns,hu₂.trans hu₁,?_,Exec.seq he₁' he₂,
    hprepared,hacc,hsolve,hbo,hhf,hdf,hformat,hfactor,hinp,houtp,hleft,h224,hprivate,hframe,
    hbankLG.trans hbankL',hbankRG.trans hbankR',?_,?_,?_,?_⟩
  · exact Nat.add_le_add hm₁ (by simpa only [hrowsLen] using hm₂)
  · exact ReplicaRecoveryRhsHeaders.of_frame H left.plan.gather leftBuffers E G hrhsL'
      (fun i => (hpass _ (Or.inl (.gather i))).2)
  · exact ReplicaRecoveryRhsHeaders.of_frame K right.plan.gather rightBuffers E G hrhsR'
      (fun i => (hpass _ (Or.inr (.gather i))).2)

  · intro j x hx
    have hjC : j.val < Cs.length := by rw [hl.length]; exact j.isLt
    have hjD : j.val < Ds.length := by rw [hr.length]; exact j.isLt
    have hrow : rows.getD j.val [] = cyclicReplicaBoundaryRow t band a n
        (Cs.getD j.val (fun _ => 0)) (Ds.getD j.val (fun _ => 0)) :=
      cyclicReplicaBoundaryRows_getD t band a n j.val Cs Ds hjC hjD
    have haccuracy := cyclicReplicaBoundary_solution_accuracy A p u l target a n axis ha hn (by omega)
      Fs hF Cs Ds hl.length hr.length hl.residual hr.residual columns hprepared hacc j x hx
    rw [← hrow] at haccuracy
    exact haccuracy
  · exact cyclicReplicaResiduals_accurate axis cellTarget 2 a n ha hn Fs hF Cs Ds hl.length hr.length
      hl.accurate hr.accurate

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
