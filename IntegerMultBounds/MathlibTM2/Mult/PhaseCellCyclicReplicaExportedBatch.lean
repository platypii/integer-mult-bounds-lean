module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaConsumerFactoryInput

/-! Execute one factor factory and all residual solves on the actual exported
packet state. Factory prerequisites come from the original raw bank. -/
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

theorem cyclicReplicaExportedBatch_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a n : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (ha : a < s) (hn : n ≤ s)
    (v : HS 834 Q A U) (S : Stacks 834 A) (raw : Stacks 234 A)
    (tail pageTail : List (Fin (A+4)))
    (factory : CyclicResidualBatchInput p l s t u target a n tail pageTail raw)
    (hin : S.inp = raw.inp) (hout : S.out = raw.out) (hL : (embStk factorReg S).L = raw.L)
    (hRframe : ∀ k : Fin 234, k ≠ 170 → k ≠ 173 → S.R (factorReg k) = raw.R k)
    (bs : List (List GaussianInt))
    (hrowsB : ∀ b ∈ bs, b.length = (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card)
    (hbound : ∀ b ∈ bs, ∀ z ∈ b,
      |gv (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2) z.re| ≤ (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2) (8*p+1) (couplingCountExponent p u) ∧
      |gv (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2) z.im| ≤ (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2) (8*p+1) (couplingCountExponent p u))
    (hcount : (S.R (left.plan.gather 121)).length = bs.length)
    (h229 : S.R (factorReg 229) = []) :
    let E := cyclicReplicaConsumerExportState S
      (cstream A (executionWidth p l (initialSchurTarget p u (boundaryTableBits p target 2
        (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2) bs.flatten)
    let T := embStk factorReg E
    let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
    let bits := boundaryTableBits p target 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let W := 24*PhaseCellBand.width p u+1
    let K := factorNewtonSteps p q
    ∃ v' page steps, ∃ columns : List (ZMod s → GaussianInt),
      let σ := boundaryFactorState (embStk preparedBoundaryCoreReg (embStk preparedBoundaryBatchCoreReg page))
      let AZ := factorRankIntegerMatrix B W columns
      let solve := fun (b : List GaussianInt) => (bandSolveVec q W (naturalLineLc q K W B.card AZ)
        (naturalLineUc q K W B.card AZ) (naturalLineRcs q K W B.card AZ)
        (b.map (normalizeBoundaryWord q (q/2-1)))).map (unscaleBoundaryWord q)
      let F : Stacks 234 A := {page with R := (Function.update page.R 224
        (cstream A w (bs.map solve).flatten++page.R 224))}
      v'.user = v.user ∧ steps ≤ constructedCyclicFactorCost p u l s t a n target 2+
        preparedResidualBatchCost q w B.card W bs.length ∧
      Exec (embTab factorReg (embTab preparedBoundaryBatchCoreReg (embTab preparedBoundaryCoreReg
        (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
          (embTab componentReg (embTab groupReg body))))))))
        (embProg factorReg id (constructedCyclicResidualBatch hR hQ)) (mk v E) steps
        (mk v' (embOvr factorReg F.get E)) ∧
      PreparedBoundaryColumns A p bits q w W B columns ∧
      ColumnFamilyAccurate A q w B
        (SchurDominance.run (realMatrix s t p u) (cyclicPrincipalVertices s a n)
          (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n).toList).1 (1/(2 : ℝ)^bits) columns ∧
      BoundarySolveReady σ q w W B.card ∧
      σ .bo = cstream A w ((naturalLineLc q K W B.card AZ).map colC).flatten ∧
      σ .hf = cstream A w ((naturalLineUc q K W B.card AZ).map colC).flatten ∧
      σ .df = cstream A w ((naturalLineRcs q K W B.card AZ).map fun x => (⟨x,0⟩ : GaussianInt)) ∧
      (∀ b ∈ bs, (solve b).length = B.card ∧ ∀ z ∈ solve b, Fits w z) ∧
      boundaryFactorState (embStk preparedBoundaryCoreReg (embStk preparedBoundaryBatchCoreReg F)) = σ ∧
      page.inp = T.inp ∧ page.out = T.out ∧ page.L = T.L ∧
      page.R 224 = T.R 224 ∧ (∀ k : Fin 234, 226 ≤ k.val → page.R k = T.R k) ∧
      (∀ k : Fin 834, (∀ j, factorReg j ≠ k) →
        (embOvr factorReg F.get E).L k = E.L k ∧ (embOvr factorReg F.get E).R k = E.R k) := by
  dsimp only
  let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let bits := boundaryTableBits p target 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let E := cyclicReplicaConsumerExportState S (cstream A w bs.flatten)
  let T := embStk factorReg E
  let native := embTab preparedBoundaryBatchCoreReg (embTab preparedBoundaryCoreReg
    (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
      (embTab componentReg (embTab groupReg body))))))
  have inputs : CyclicResidualBatchInput p l s t u target a n tail pageTail T :=
    cyclicReplicaConsumerExport_factoryInput S raw _ factory hin hout hL hRframe
  have hcopy := unaryCopiesR_at (fun k => (S.R k).length) S.R
    cyclicReplicaConsumerHeaderCopies (by decide)
    (left.plan.gather 121,factorReg 229) (by simp [cyclicReplicaConsumerHeaderCopies])
  have hcopyCount : ((cyclicReplicaConsumerHeaderState S).R (factorReg 229)).length = bs.length := by
    simpa only [cyclicReplicaConsumerHeaderState,hcount,h229,List.append_nil,List.length_replicate]
      using congrArg List.length hcopy
  have hmove := congrArg (fun R => R.R 229)
    (cyclicReplicaArchiveHandoff_factor (cyclicReplicaConsumerHeaderState S))
  have hinstalled : ((cyclicReplicaConsumerState S).R (factorReg 229)).length = bs.length := by
    have hh : (cyclicReplicaConsumerState S).R (factorReg 229) =
        (cyclicReplicaConsumerHeaderState S).R (factorReg 229) := by
      simpa only [cyclicReplicaConsumerState,embStk,Function.comp_apply,
        Function.update_of_ne (by decide : (229 : Fin 234) ≠ 172),
        Function.update_of_ne (by decide : (229 : Fin 234) ≠ 169)] using hmove
    rw [hh]
    exact hcopyCount
  have hcounter : (T.R 229).length = bs.length := by
    have hp := cyclicReplicaConsumerExportState_factor S (cstream A w bs.flatten)
    have hh := congrArg (fun R => (R.R 229).length) hp
    simpa only [T,E,embStk,Function.comp_apply] using hh.trans hinstalled
  have hsource : T.R 226 = cstream A w bs.flatten++[] := by
    have hp := cyclicReplicaConsumerExportState_factor S (cstream A w bs.flatten)
    have hh := congrArg (fun R => R.R 226) hp
    simpa [exportedCyclicResidualRows,cyclicResidualRowsRetired] using hh
  obtain ⟨vi,page,m,columns,hui,hm,hei,hprepared,hacc,hsolve,hbo,hhf,hdf,hformat,hfactor,
    hinp,houtp,hleft,h224,hprivate⟩ := constructedCyclicResidualBatch_spec (body := body)
    hR hQ hA axis ha hn (embDn factorReg v) T tail pageTail
    inputs.rows inputs.pageWidth inputs.page inputs.arithmetic inputs.origin inputs.leftEnd inputs.rightEnd
    (inputs.fresh 141 (by simp)) (inputs.fresh 142 (by simp))
    (inputs.fresh 0 (by simp)) (inputs.fresh 139 (by simp))
    (inputs.fresh 127 (by simp)) (inputs.fresh 138 (by simp))
    (inputs.fresh 143 (by simp)) (inputs.fresh 147 (by simp))
    (inputs.fresh 151 (by simp)) (inputs.fresh 152 (by simp)) (inputs.fresh 153 (by simp))
    inputs.left inputs.new bs hrowsB hbound []
    (inputs.privateFresh 225 (by simp)) (inputs.privateFresh 227 (by simp))
    (inputs.privateFresh 228 (by simp)) (inputs.privateFresh 230 (by simp))
    (inputs.privateFresh 231 (by simp)) (inputs.privateFresh 232 (by simp))
    (inputs.privateFresh 233 (by simp)) hcounter hsource
  obtain ⟨vf,_,hu,he⟩ := exec_emb_ovr (body := native) (body' := embTab factorReg native)
    (ι := id) factorReg_injective (by intro f; rfl) hei v rfl E rfl
  exact ⟨vf,page,m,columns,hu.trans hui,hm,he,hprepared,hacc,hsolve,hbo,hhf,hdf,hformat,
    hfactor,hinp,houtp,hleft,h224,hprivate,fun _ hk => embOvr_off _ _ hk⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
