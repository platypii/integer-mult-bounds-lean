module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaConsumerBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedCyclicReplicaProducer
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicResidualConsumerWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaBoundarySolutionAccuracy

/-! Original RHS inputs execute both cached passes, generate masks, export
residual rows and share one factor factory across all boundary solves. -/
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

noncomputable def cachedCyclicReplicaBatch (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 834 Q A U :=
  .seq (cachedReplicaPassMasks left right (factorReg 170) (factorReg 173) hR hQ)
    (cyclicReplicaConsumerBatch hR hQ)

theorem cachedCyclicReplicaBatch_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a n : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (ha : a < s) (hn : n ≤ s)
    (hleftRoom : min n (s-a)+PhaseCellBand.width p u ≤ s)
    (hrightRoom : n-min n (s-a)+PhaseCellBand.width p u ≤ s) :
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
    ∀ (leftBuffers rightBuffers : ReplicaLoopBuffers A) (v : HS 834 Q A U)
      (S : Stacks 834 A) (tail pageTail : List (Fin (A+4))),
    CachedReplicaPassInput H left leftBuffers S → CachedReplicaPassInput K right rightBuffers S →
    CyclicResidualBatchInput p l s t u target a n tail pageTail (embStk factorReg S) →
    S.R (factorReg 226) = [] → S.R (factorReg 229) = [] →
    ∃ (mid producer : Stacks 834 A) (Cs Ds : List (ZMod s → GaussianInt))
      (v' : HS 834 Q A U) (page : Stacks 234 A) (steps : ℕ) (columns : List (ZMod s → GaussianInt)),
    let producerCost := (cachedReplicaPassCost H+cachedReplicaPassCost K)+
      (placedReplicaBoundaryMaskCost H+placedReplicaBoundaryMaskCost K)
    let rows := (Cs.zip Ds).map (fun z => cyclicReplicaBoundaryRow t band a n z.1 z.2)
    let E := cyclicReplicaConsumerExportState producer (cstream A w rows.flatten)
    let T := embStk factorReg E
    let W := 24*band+1
    let iterations := factorNewtonSteps p q
    let consumerCost := ((4*(H.Fs.length+H.wordWidth+H.span*H.wordWidth+K.span*K.wordWidth)+17)+
      (4*(H.Fs.length*(H.span*H.wordWidth)+K.Fs.length*(K.span*K.wordWidth))+8))+
      exportCyclicResidualRowsCost H.Fs.length n B.card H.wordWidth
      let σ := boundaryFactorState (embStk preparedBoundaryCoreReg (embStk preparedBoundaryBatchCoreReg page))
      let AZ := factorRankIntegerMatrix B W columns
      let solve := fun (b : List GaussianInt) => (bandSolveVec q W (naturalLineLc q iterations W B.card AZ)
        (naturalLineUc q iterations W B.card AZ) (naturalLineRcs q iterations W B.card AZ)
        (b.map (normalizeBoundaryWord q (q/2-1)))).map (unscaleBoundaryWord q)
      let F : Stacks 234 A := {page with R := (Function.update page.R 224
        (cstream A w (rows.map solve).flatten++page.R 224))}
      CachedReplicaPassPost H left leftBuffers S producer Cs ∧
      CachedReplicaPassPost K right rightBuffers mid producer Ds ∧
      v'.user = v.user ∧ steps ≤ producerCost+(consumerCost+(constructedCyclicFactorCost p u l s t a n target 2+
        preparedResidualBatchCost q w B.card W Fs.length)) ∧
      Exec (embTab factorReg (embTab preparedBoundaryBatchCoreReg (embTab preparedBoundaryCoreReg
        (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
          (embTab componentReg (embTab groupReg body))))))))
        (cachedCyclicReplicaBatch hR hQ) (mk v S) steps
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
      embStk left.coupling.bank (embOvr factorReg F.get E) = embStk left.coupling.bank producer ∧
      embStk right.coupling.bank (embOvr factorReg F.get E) = embStk right.coupling.bank producer ∧
      ReplicaRecoveryRhsHeaders H left.plan.gather leftBuffers (embOvr factorReg F.get E) ∧
      ReplicaRecoveryRhsHeaders K right.plan.gather rightBuffers (embOvr factorReg F.get E) ∧
      NativeBoundaryUnfoldWorkspace B.card F ∧
      BoundaryProjectionFrame Fs.length F ∧
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
  intro leftBuffers rightBuffers v S tail pageTail leftInputs rightInputs factory h226 h229
  let native := embTab factorReg (embTab preparedBoundaryBatchCoreReg (embTab preparedBoundaryCoreReg
    (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
      (embTab componentReg (embTab groupReg body)))))))
  obtain ⟨hblank,h170,h173,hwork,hfresh⟩ := factory.consumerWorkspace h226 h229
  obtain ⟨v₁,mid,producer,m₁,Cs,Ds,hu₁,hm₁,he₁,hl,hr,hmaskL,hmaskR,hin,hout,hL,hRframe⟩ :=
    cachedCyclicReplicaProducer_exec (body := native) axis cellTarget a n ha hn hleftRoom hrightRoom
      hR hQ hA Fs hF leftBuffers rightBuffers v S leftInputs rightInputs h170 h173
  have hblank' : ∀ k ∈ [(130 : Fin 234),168,169,171,172,174,175,229],
      producer.R (factorReg k) = [] := by
    intro k hk
    have h170 : k ≠ 170 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h173 : k ≠ 173 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (hRframe k h170 h173).trans (hblank k hk)
  have hwork' : ∀ r : Fin 180, r.val < 80 →
      producer.R (factorReg (cyclicResidualRowsReg r)) = [] := by
    intro r hr80
    have hv : (cyclicResidualRowsReg r).val < 80 ∨ (cyclicResidualRowsReg r).val = 226 := by
      have h179 : r ≠ 179 := by intro he; have hv := congrArg Fin.val he; simp at hv; omega
      by_cases h6 : r = 6
      · right; simp [cyclicResidualRowsReg,h6]
      · left; simpa only [cyclicResidualRowsReg,ite_eq_right h6,ite_eq_right h179] using hr80
    have h170 : cyclicResidualRowsReg r ≠ 170 := by
      intro he; have heval := congrArg Fin.val he; simp at heval; omega
    have h173 : cyclicResidualRowsReg r ≠ 173 := by
      intro he; have heval := congrArg Fin.val he; simp at heval; omega
    exact (hRframe _ h170 h173).trans (hwork r hr80)
  have hfresh' : ∀ r ∈ [(134 : Fin 180),135,136,137,143,174,175,176,177,178],
      producer.R (factorReg (cyclicResidualRowsReg r)) = [] := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact (hRframe _ (by decide) (by decide)).trans (hfresh _ (by simp))
  obtain ⟨vf,page,m₂,columns,hu₂,hm₂,he₂,hprepared,hacc,hsolve,hbo,hhf,hdf,hformat,hfactor,
    hinp,houtp,hleft,h224,hprivate,hframe,hbankL,hbankR,hrhsL,hrhsR,hworkspace,hprojection,haccuracy,hresidual⟩ :=
    cyclicReplicaConsumerBatch_spec (body := body) hR hQ hA axis ha hn Fs hF
      leftBuffers rightBuffers S mid Cs Ds v₁ producer (embStk factorReg S) tail pageTail hl hr
      factory hin hout hL hRframe hblank' hmaskL hmaskR hwork' hfresh'
  exact ⟨mid,producer,Cs,Ds,vf,page,m₁+m₂,columns,hl,hr,hu₂.trans hu₁,
    Nat.add_le_add hm₁ hm₂,Exec.seq he₁.toExec he₂,hprepared,hacc,hsolve,hbo,hhf,hdf,hformat,hfactor,
    hinp,houtp,hleft,h224,hprivate,hframe,hbankL,hbankR,hrhsL,hrhsR,hworkspace,hprojection,haccuracy,hresidual⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
