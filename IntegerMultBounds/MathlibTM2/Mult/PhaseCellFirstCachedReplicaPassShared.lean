module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedCachedReplicaInteriorCoupling
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryBatchSharedBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryPeripheralReady

/-! Execute the first interior/coupling pass and derive the retained shared bank.
The residual archive, factors and recovery workspace come from the same trace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 392 Q A U}

def firstCachedReplicaPassTime {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) : ℕ :=
  (allocateZeroLineCost H.Fs.length (H.span*H.wordWidth)+
        (placedHaloLengthKeysCost s H.t H.band H.origin (H.origin+H.span) H.metadataWidth+
          (((haloLengthKeys s H.t H.band H.origin (H.origin+H.span)).map (fun L => H.keyCost L+3)).sum+2)))+
        realReplicaRowsCost H.Fs.length (H.span*H.wordWidth)+reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth)+releasedRetiredCachedReplicaCouplingCost H

theorem firstCachedReplicaPass_shared_exec (H : ReplicaHaloProblem s) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hspan : H.span+H.band ≤ s) (horigin : H.origin < s)
    (R K : ℕ)
    (hpushR : mnProgPush (rpProg (P := Empty) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R)
    (hpushK : mnProgPush (cmulBlock cr (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr)) ≤ K)
    (hpad : 2*((s/(H.t-s)+1)-2*H.band) ≤ 2^H.l+1)
    (buffers : ReplicaLoopBuffers A) (v : HS 392 Q A U) (S : Stacks 392 A)
    (headers : ReplicaLoopHeaders H replicaRecoveryBatchInterior.gather buffers S)
    (hbank : embStk weightCacheCoreReg (embStk replicaRecoveryBatchInterior.solver S) =
      releasedCellBank [] buffers.rhsTail buffers.solverOutputTail S.inp S.out)
    (hcache : S.R (replicaRecoveryBatchInterior.solver 117) = buffers.cacheTail)
    (hsolverFresh : ∀ k ∈ [(118 : Fin 121),119,120], S.R (replicaRecoveryBatchInterior.solver k) = [])
    (hinput : S.inp = buffers.input) (houtputStream : S.out = buffers.output)
    (hsaved : embStk replicaRecoveryBatchInterior.gather S = buffers.savedGather)
    (hkeys : S.R (replicaRecoveryBatchInterior.gather 87) = buffers.keyTail) (hdst : S.R 247 = buffers.accumulatorTail)
    (h86 : S.R (replicaRecoveryBatchInterior.gather 86) = []) (h119 : S.R (replicaRecoveryBatchInterior.gather 119) = []) (depth : ℕ)
    (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (hblank : ∀ k ∈ ([(145 : Fin 168),146,147,148,149,151,154,155,156,157,163,164,165]), S.R (replicaRecoveryBatchCoupling.bank k) = [])
    (hfresh : ∀ k ∈ [(127 : Fin 168),135,139,140,143,158,166,167], S.R (replicaRecoveryBatchCoupling.bank k) = [])
    (target : ℕ) (columns : List (ZMod s → GaussianInt))
    (hfactor : ReplicaBoundaryFactorData H target columns (embStk replicaRecoveryBoundaryFactoryReg S))
    (hwork : ReplicaFactoryWorkspace (embStk replicaRecoveryBoundaryFactoryReg S))
    (hmasters : CouplingMasterHeaders (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span)
      (embStk replicaRecoveryBatchCoupling.bank S))
    (hstage : (S.R (replicaRecoveryBatchCoupling.bank 118)).length = H.stage+1)
    (hlevel : (S.R (replicaRecoveryBatchCoupling.bank 120)).length = H.l)
    (hprivate : ∀ k : Fin 248, 242 ≤ k.val →
      S.L (replicaRecoveryPreparationNativeReg k) = [] ∧ S.R (replicaRecoveryPreparationNativeReg k) = [])
    (h159 : S.R (replicaRecoveryBatchCoupling.bank 159) = [])
    (h161 : S.R (replicaRecoveryBatchCoupling.bank 161) = []) :
    ∃ v' F m, ∃ Ds : List (ZMod s → GaussianInt), v'.user = v.user ∧
      m ≤ firstCachedReplicaPassTime H ∧
      Exec body (initializedCachedReplicaInteriorCoupling replicaRecoveryBatchCoupling 247 248 hR hQ) (mk v S) m (mk v' F) ∧
      Ds.length = H.Fs.length ∧ F.R 125 = Ds.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D)) ∧
      (∀ j : Fin Ds.length, ReplicaCouplingResidualSpec H (H.Fs.length-1-j.val) (Ds[j.val]'j.isLt)) ∧
      ReplicaBoundaryFactorData H target columns (embStk replicaRecoveryBoundaryFactoryReg F) ∧
      ReplicaRecoverySharedBank H (12*H.band+1) (embStk replicaRecoveryPreparationNativeReg F) ∧
      ReplicaRecoveryRhsHeaders H replicaRecoveryBatchInterior.gather buffers F ∧
      F.R 247 = buffers.accumulatorTail ∧ F.R 248 = S.R 248 ∧
      (embStk weightCacheCoreReg (embStk replicaRecoveryBatchInterior.solver F)).L =
        (embStk weightCacheCoreReg (embStk replicaRecoveryBatchInterior.solver S)).L ∧
      (∀ k, (∀ i, replicaRecoveryBatchInterior.gather i ≠ k) →
        (∀ i, replicaRecoveryBatchInterior.solver i ≠ k) → (247 : Fin 392) ≠ k → F.L k = S.L k) ∧
      (∀ k, (∀ i, replicaRecoveryBatchCoupling.bank i ≠ k) →
        (∀ i, replicaRecoveryBatchInterior.gather i ≠ k) →
        (∀ i, replicaRecoveryBatchInterior.solver i ≠ k) →
        (247 : Fin 392) ≠ k → (248 : Fin 392) ≠ k → F.R k = S.R k) ∧
      ReplicaRecoveryPeripheralReady H buffers {F with R := Function.update F.R 125 []} ∧
      F.R (replicaRecoveryPreparationCallerWorkerReg 93) = buffers.solverOutputTail ∧
      F.R (replicaRecoveryPreparationCallerWorkerReg 110) = buffers.rhsTail ∧
      (∀ k : Fin 168, 117 ≤ k.val → k ∉ replicaCouplingSetupPorts →
        F.R (replicaRecoveryBatchCoupling.bank k) = S.R (replicaRecoveryBatchCoupling.bank k)) ∧
      releaseReplicaCouplingNativeCost (embStk replicaRecoveryPreparationNativeReg F) ≤
        replicaCouplingNativeCleanupBound (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
          H.origin (H.origin+H.span) := by
  have hg (k : Fin 126) : replicaRecoveryBatchInterior.gather k ≠ (247 : Fin 392) ∧
      replicaRecoveryBatchInterior.gather k ≠ (248 : Fin 392) := by
    constructor <;> intro he <;> have hv := congrArg Fin.val he <;>
      change k.val = _ at hv <;> have hk := k.isLt <;> omega
  have hb (k : Fin 168) : replicaRecoveryBatchCoupling.bank k ≠ (247 : Fin 392) ∧
      replicaRecoveryBatchCoupling.bank k ≠ (248 : Fin 392) := by
    rw [replicaRecoveryBatchCoupling_bank]
    have hh := replicaRecoveryPreparationCallerReg_gap (Fin.castLE (by decide : 168 ≤ 258) k)
    constructor <;> intro he <;> have hv := congrArg Fin.val he <;>
      change (replicaRecoveryPreparationCallerReg (Fin.castLE (by decide : 168 ≤ 258) k)).val = _ at hv <;> omega
  have hs (k : Fin 121) : replicaRecoveryBatchInterior.solver k ≠ (247 : Fin 392) ∧
      replicaRecoveryBatchInterior.solver k ≠ (248 : Fin 392) := by
    constructor <;> intro he <;> have hv := congrArg Fin.val he <;>
      change 126+k.val = _ at hv <;> have hk := k.isLt <;> omega
  have h136 : S.R (replicaRecoveryBatchCoupling.bank 136) = [] := by
    have hh := hwork.scratch 136 (by simp [replicaFactoryScratchPorts])
    norm_num only [embStk_R,replicaRecoveryBoundaryFactoryReg,replicaRecoveryBatchCoupling_bank,Fin.castLE] at hh ⊢
    exact hh
  obtain ⟨v',F,m,Ds,hu,hm,he,h122,hout,hrhs,hready,hmeta,hinFinal,houtFinal,hgatherLeft,hgatherR,hcacheFinal,hfreshSolver,hnative,hleft,hright,
    hlen,harchive,hgood,hpage,hcount,hrows,hfreshF,hbounds,haccurate,hcounter,hcleanup,hshare,hretained,hrhsHeaders⟩ :=
    initializedCachedReplicaInteriorCoupling_exec (body := body) H replicaRecoveryBatchCoupling 247 248
      (fun k => (hg k).1) (fun k => (hg k).2) (fun k => (hb k).1) (fun k => (hb k).2)
      (fun k => (hs k).1) (fun k => (hs k).2) (by decide) hR hQ hA hspan horigin R K hpushR hpushK
      hpad buffers v S headers hbank hcache hsolverFresh hinput houtputStream hsaved hkeys hdst h86 h119 depth
      hp hwidth hblank hfresh h136 h159 h161
  obtain ⟨hdata,hshared⟩ := hfactor.batch_first_pass_shared_bank H target columns buffers.rhsTail
    hnative hleft hright hready hshare hwork (hretained hmasters hstage hlevel) hprivate hfreshF hrows hpage hcount
  have h93 : F.R (replicaRecoveryPreparationCallerWorkerReg 93) = buffers.solverOutputTail := by
    rw [replicaRecoveryBatchCoupling_native_view F] at hcounter
    have hh := congrFun hcounter 93
    simpa [counterR,cr,OutputPlacement.code,replicaCouplingUnaryBank,unaryCopiesR,replicaCouplingHeaderCopies,releasedCellBank,embStk,replicaRecoveryPreparationNativeReg,Function.update_apply,Fin.ext_iff] using hh
  have h110 : F.R (replicaRecoveryPreparationCallerWorkerReg 110) = buffers.rhsTail := by
    rw [replicaRecoveryBatchCoupling_native_view F] at hready
    exact hready.source
  have hcleanupF : releaseReplicaCouplingNativeCost (embStk replicaRecoveryPreparationNativeReg F) ≤
      replicaCouplingNativeCleanupBound (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
        H.origin (H.origin+H.span) := by
    apply releaseReplicaCouplingNativeCost_le_of_generated _ (2^15*H.p) H.precision H.wordWidth
      s H.t H.u H.band H.origin (H.origin+H.span) buffers.rhsTail buffers.solverOutputTail S.inp S.out
    rw [replicaRecoveryBatchCoupling_native_view F] at hcounter
    intro i
    exact congrFun hcounter i
  refine ⟨v',F,m,Ds,hu,hm,he,hlen,harchive,hgood,hdata,hshared,hrhsHeaders,hout,hrhs,hnative,hleft,hright,?_,h93,h110,hshare,hcleanupF⟩
  have hgClear (k : Fin 126) :
      ({F with R := Function.update F.R 125 []} : Stacks 392 A).R (replicaRecoveryBatchInterior.gather k) =
        S.R (replicaRecoveryBatchInterior.gather k) := by
    by_cases hk : k = 125
    · subst k
      change Function.update F.R 125 [] 125 = S.R 125
      rw [Function.update_self]
      exact (headers.fresh 125 (by simp)).symm
    · change Function.update F.R 125 [] (replicaRecoveryBatchInterior.gather k) = _
      rw [Function.update_of_ne (by
        intro he
        exact hk (Fin.ext (congrArg (fun j : Fin 392 => j.val) he)))]
      exact hgatherR k hk
  constructor
  · exact headers.of_frame (fun k _ _ => hgClear k)
  · change Function.update F.R 125 [] (replicaRecoveryBatchInterior.solver 117) = buffers.cacheTail
    rw [Function.update_of_ne (by decide)]
    exact hcacheFinal
  · intro k hk
    change Function.update F.R 125 [] (replicaRecoveryBatchInterior.solver k) = []
    have hneq : replicaRecoveryBatchInterior.solver k ≠ (125 : Fin 392) := by
      intro he
      have hv := congrArg Fin.val he
      change 126+k.val = 125 at hv
      omega
    rw [Function.update_of_ne hneq]
    exact hfreshSolver k hk
  · exact hinFinal.trans hinput
  · exact houtFinal.trans houtputStream
  · exact (hgClear 87).trans hkeys
  · change Function.update F.R 125 [] 247 = _
    rw [Function.update_of_ne (by decide : (247 : Fin 392) ≠ 125)]
    exact hout
  · exact (hgClear 86).trans h86
  · exact (hgClear 119).trans h119

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
