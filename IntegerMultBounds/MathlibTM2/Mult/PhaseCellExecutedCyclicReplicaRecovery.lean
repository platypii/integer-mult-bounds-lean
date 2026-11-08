module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedCyclicReplicaRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBatchInputData

/-! Ordinary original-RHS inputs execute the cached boundary caller and recovery
coupling. The caller's own solved rows supply all recovery format/control facts. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open CyclicReplicaPlacement
local notation "extendCaller" => CyclicRecoveryPlacement.extend
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def CyclicBoundaryRowsAccurate {s : ℕ} [NeZero s] (p t u a n q target : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (solutions : List (List GaussianInt)) : Prop :=
  let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  ∀ j : Fin Fs.length, ∀ x : ZMod s → ℝ,
    SchurDominance.Solves (realMatrix s t p u) (cyclicPrincipalVertices s a n) x
      (fun k => (value q (Fs.reverse.getD (Fs.length-1-j.val) (fun _ => 0) k)).re) →
    let solution := solutions.getD j.val []
    solution.length = B.card ∧ ∀ i < B.card,
      ‖value q (solution.getD i 0)-(x (bFoldAt s B i) : ℂ)‖ ≤ 3/(2 : ℝ)^target ∧
      ‖value q (solution.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p 2

noncomputable def cachedCyclicReplicaBoundaryBill {s : ℕ} [NeZero s] (H K : ReplicaHaloProblem s)
    (p u l t a n target q w N W replicas : ℕ) : ℕ :=
  ((cachedReplicaPassCost H+cachedReplicaPassCost K)+
    (placedReplicaBoundaryMaskCost H+placedReplicaBoundaryMaskCost K))+
    ((((4*(H.Fs.length+H.wordWidth+H.span*H.wordWidth+K.span*K.wordWidth)+17)+
      (4*(H.Fs.length*(H.span*H.wordWidth)+K.Fs.length*(K.span*K.wordWidth))+8))+
      exportCyclicResidualRowsCost H.Fs.length n N H.wordWidth)+
      (constructedCyclicFactorCost p u l s t a n target 2+preparedResidualBatchCost q w N W replicas))

theorem executedCyclicReplicaRecovery_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    ∀ (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2),
    let H := axis.cyclicLeftReplicaProblem cellTarget 2 a n ha Fs hF
    let K := axis.cyclicRightReplicaProblem cellTarget 2 a n hn Fs hF
    ∀ (leftBuffers rightBuffers : ReplicaLoopBuffers A) (z : HS 840 Q A U)
      (S : Stacks 834 A) (tail pageTail : List (Fin (A+4))),
    CachedReplicaPassInput H left leftBuffers S → CachedReplicaPassInput K right rightBuffers S →
    CyclicResidualBatchInput p l s t u target a n tail pageTail (embStk factorReg S) →
    S.R (factorReg 226) = [] → S.R (factorReg 229) = [] →
    ∃ (solutions : List (List GaussianInt)) (zf : HS 840 Q A U) (X : Stacks 840 A)
      (steps : ℕ) (savedL savedR pageL pageR : List (Fin (A+4))),
      let rows := cyclicBoundaryRecoveryRows B solutions Fs
      solutions.length = Fs.length ∧
      (∀ solution ∈ solutions, solution.length = B.card ∧ ∀ y ∈ solution, Fits w y) ∧
      CyclicBoundaryRowsAccurate p t u a n q target Fs solutions ∧
      (∀ solution ∈ solutions, ∀ i < B.card,
        ‖value q (solution.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p 2) ∧ zf.user = z.user ∧
      steps ≤ cachedCyclicReplicaBoundaryBill H K p u l t a n target q w B.card (24*band+1) Fs.length+
        solvedCyclicRecoveryCost H K Fs.length B.card n w ∧
      Exec (embTab extendCaller (cyclicReplicaCallerBody body)) (cachedCyclicReplicaRecovery hR hQ)
        (mk z (extendStacks (by decide : 834 ≤ 840) S)) steps (mk zf X) ∧
      X.R (CyclicRecoveryPlacement.bank 228) = [] ∧
      X.R (CyclicRecoveryPlacement.leftJob.coupling.bank 110) = rows.reverse.flatMap (cyclicRecoveryOutputL H)++leftBuffers.rhsTail ∧
      X.R (CyclicRecoveryPlacement.rightJob.coupling.bank 110) = rows.reverse.flatMap (cyclicRecoveryOutputR K)++rightBuffers.rhsTail ∧
      X.R (CyclicRecoveryPlacement.leftJob.plan.gather 125) = rows.reverse.flatMap (fun row => cyclicRecoveryField H row.1)++savedL ∧
      X.R (CyclicRecoveryPlacement.rightJob.plan.gather 125) = rows.reverse.flatMap (fun row => cyclicRecoveryField K row.1)++savedR ∧
      CachedRecoveryCouplingReady H (rows.reverse.flatMap (cyclicRecoveryOutputL H)++leftBuffers.rhsTail)
        pageL (embStk CyclicRecoveryPlacement.leftJob.coupling.bank X) ∧
      CachedRecoveryCouplingReady K (rows.reverse.flatMap (cyclicRecoveryOutputR K)++rightBuffers.rhsTail)
        pageR (embStk CyclicRecoveryPlacement.rightJob.coupling.bank X) ∧
      ReplicaRecoveryRhsHeaders H CyclicRecoveryPlacement.leftJob.plan.gather leftBuffers X ∧
      ReplicaRecoveryRhsHeaders K CyclicRecoveryPlacement.rightJob.plan.gather rightBuffers X := by
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
  intro leftBuffers rightBuffers z S tail pageTail inputsL inputsR factory h226 h229
  obtain ⟨mid,producer,Cs,Ds,vf,page,m₀,columns,postL,postR,hu₀,hm₀,he₀,hprepared,hacc,hsolve,hbo,hhf,hdf,
    hformat,hfactor,hinp,houtp,hleft,h224,hprivate,hframe,hbankL,hbankR,hrhsL,hrhsR,hworkspace,hprojection,haccuracy,hresidual⟩ :=
    cachedCyclicReplicaBatch_spec (body := body) hR hQ hA axis ha hn hleftRoom hrightRoom
      Fs hF leftBuffers rightBuffers (embDn extendCaller z) S tail pageTail inputsL inputsR factory h226 h229
  let rows := (Cs.zip Ds).map (fun pair => cyclicReplicaBoundaryRow t band a n pair.1 pair.2)
  let E := cyclicReplicaConsumerExportState producer (cstream A w rows.flatten)
  let W := 24*band+1
  let iterations := factorNewtonSteps p q
  let AZ := factorRankIntegerMatrix B W columns
  let solve := fun (b : List GaussianInt) => (bandSolveVec q W (naturalLineLc q iterations W B.card AZ)
    (naturalLineUc q iterations W B.card AZ) (naturalLineRcs q iterations W B.card AZ)
    (b.map (normalizeBoundaryWord q (q/2-1)))).map (unscaleBoundaryWord q)
  let F : Stacks 234 A := {page with R := Function.update page.R 224 (cstream A w (rows.map solve).flatten++page.R 224)}
  let G := embOvr factorReg F.get E
  let solutions := rows.map solve
  have hHF : H.Fs = Fs := rfl
  have hKF : K.Fs = Fs := rfl
  have hCs : Cs.length = Fs.length := by
    have hh : Cs.length = H.Fs.length := postL.length
    simpa only [hHF] using hh
  have hDs : Ds.length = Fs.length := by
    have hh : Ds.length = K.Fs.length := postR.length
    simpa only [hKF] using hh
  have hrows : rows.length = Fs.length := by simp only [rows,List.length_map,List.length_zip,hCs,hDs,Nat.min_self]
  have hlen : solutions.length = Fs.length := by simpa only [solutions,List.length_map] using hrows
  have hformats : ∀ solution ∈ solutions, solution.length = B.card ∧ ∀ y ∈ solution, Fits w y := by
    intro solution hs
    obtain ⟨row,hr,rfl⟩ := List.mem_map.mp hs
    exact hformat row hr
  have hview : embStk factorReg G = F := embStk_ovr factorReg_injective _ _
  have hsource : G.R (factorReg 224) = solutions.flatMap (cstream A w)++page.R 224 := by
    have hh := congrArg (fun T : Stacks 234 A => T.R 224) hview
    simpa only [F,solutions,Function.update_self,cstream_flatten,List.flatMap_def,embStk,Function.comp_apply] using hh
  have hcore : embStk (Fin.castLE (by decide : 224 ≤ 234)) F =
      embStk preparedBoundaryCoreReg (embStk preparedBoundaryBatchCoreReg F) := by
    refine Stacks.ext rfl rfl ?_ ?_ <;> funext i <;> rfl
  have hready : BoundarySolveReady (boundaryFactorState (embStk (Fin.castLE (by decide : 224 ≤ 234))
      (embStk factorReg G))) q w W B.card := by
    rw [hview,hcore]
    exact hfactor.symm ▸ hsolve
  have hboundary : CyclicBoundaryRowsAccurate p t u a n q target Fs solutions := by
    change CyclicBoundaryRowsAccurate p t u a n q target Fs (rows.map solve)
    dsimp only [CyclicBoundaryRowsAccurate]
    intro j x hx
    have hj : j.val < rows.length := by rw [hrows]; exact j.isLt
    have hget : (rows.map solve).getD j.val [] = solve (rows.getD j.val []) := by
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hj),List.getD_eq_getElem _ _ hj]
      simp only [List.getElem_map]
    rw [hget]
    exact haccuracy j x hx
  have hmag : ∀ solution ∈ solutions, ∀ i < B.card,
      ‖value q (solution.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p 2 := by
    intro solution hs i hi
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hs
    have hjF : j < Fs.length := by simpa only [hlen] using hj
    have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by have := axis.hp; omega)
    obtain ⟨x,hx⟩ := SchurDominance.solves_exists (realMatrix s t p u) (cyclicPrincipalVertices s a n)
      (1/(8*(p : ℝ))) (by positivity)
      (SchurDominance.dominates_mono _ Finset.univ _ _ (Finset.subset_univ _) axis.hdom)
      (fun k => (value q (Fs.reverse.getD (Fs.length-1-j) (fun _ => 0) k)).re)
    have hh := (hboundary ⟨j,hjF⟩ x hx).2 i hi
    simpa only [List.getD_eq_getElem _ _ hj] using hh.2
  obtain ⟨zf,X,m,hu,hm,he,hclock,hcursor⟩ := cachedCyclicReplicaRecovery_exec body H K t band a n q w W
    axis.hst ha hn rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl solutions Fs hHF hKF hlen hformats hR hQ hA
    hleftRoom hrightRoom leftBuffers rightBuffers S S mid producer G Cs Ds (embDn extendCaller z) vf m₀
    he₀ hu₀ postL postR hbankL hbankR hrhsL hrhsR (page.R 224)
    (by rw [hview]; exact hworkspace) hready hsource (by rw [hview]; exact hprojection) z rfl
  refine ⟨solutions,zf,X,m,_,_,_,_,hlen,hformats,hboundary,hmag,hu,?_,he,hclock,?_,?_,hcursor.archiveL,hcursor.archiveR,
    hcursor.cacheL,hcursor.cacheR,hcursor.headersL,hcursor.headersR⟩
  · have hbill : m₀ ≤ cachedCyclicReplicaBoundaryBill H K p u l t a n target q w B.card W Fs.length := hm₀
    exact hm.trans (Nat.add_le_add_right hbill _)
  · have hh := hcursor.cacheL.ready.source
    change X.R (CyclicRecoveryPlacement.leftJob.coupling.bank 110) =
      (cyclicBoundaryRecoveryRows B solutions Fs).reverse.flatMap (cyclicRecoveryOutputL H)++leftBuffers.rhsTail at hh
    exact hh
  · have hh := hcursor.cacheR.ready.source
    change X.R (CyclicRecoveryPlacement.rightJob.coupling.bank 110) =
      (cyclicBoundaryRecoveryRows B solutions Fs).reverse.flatMap (cyclicRecoveryOutputR K)++rightBuffers.rhsTail at hh
    exact hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
