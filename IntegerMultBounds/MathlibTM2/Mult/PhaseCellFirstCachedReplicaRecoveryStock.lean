module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFirstCachedReplicaPassSharedStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFirstCachedReplicaRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleasedPreparedCachedReplicaRecoveryStock

/-! Execute the first pass and cached recovery on the same retained factor bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 392 Q A U}

noncomputable def firstCachedReplicaRecoveryWorkspace (H J : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c M R K : ℕ) : ℕ :=
  initializedCachedReplicaInteriorWorkspace (A := A) (U := U) H hQ R K M+
    preparedCachedBatchedReplicaRecoveryWorkspace H J hQ push c M R K

theorem firstCachedReplicaRecovery_exec_within (H : ReplicaHaloProblem s) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c : ℕ)
    (hpush : mnNativePushBound c (replicaBoundaryRhs (P := Empty) (Q := Q) (A := A) (U := U)))
    (M : ℕ) (hpushM : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ M)
    (X : ℕ → ZMod s → ℝ)
    (hX : ∀ r < H.Fs.length, Solves (realMatrix s H.t H.p H.u) (haloVertices s H.origin (H.origin+H.span)) (X r)
      (fun i => (value H.precision (H.Fs.reverse.getD r (fun _ => 0) i)).re))
    (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card)
    (hleftShared : ∀ i : Fin 242, S.L (replicaRecoveryPreparationCallerWorkerReg (Fin.castLE (by decide : 242 ≤ 257) i)) =
      S.L (replicaRecoveryPreparationCallerWorkerReg (Fin.castLE (by decide : 255 ≤ 257) (replicaBoundaryPhaseReg i))))
    (hblankSetup : ∀ i : Fin 255, 248 ≤ i.val → S.R (replicaRecoverySetupWorkerReg i) = [])
    (h159 : S.R (recoveryMaskCallerReg 159) = []) (h161 : S.R (recoveryMaskCallerReg 161) = [])
    (hcount : (S.R 390).length = H.Fs.length) (h391 : S.R 391 = []) (h248 : S.R 248 = []) :
    ∃ B : ReplicaRecoveryBatch H target X, ∃ Ds : List (ZMod s → GaussianInt), ∃ v' G n outputs,
      Ds.length = H.Fs.length ∧ v'.user = v.user ∧ n ≤ firstCachedReplicaRecoveryTime H (B.problem htarget) ∧
      List.Forall₂ (ReplicaRecoveryAssemblyOutput B Ds) (List.finRange H.Fs.length) outputs ∧
      G.R 257 = S.R (replicaRecoveryPreparationCallerWorkerReg 125) ∧ G.R 247 = buffers.accumulatorTail ∧
      G.R 391 = outputs.reverse.flatten ∧
      ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          firstCachedReplicaRecoveryWorkspace H (B.problem htarget) hQ push c M R K)
        depth (firstCachedReplicaRecovery hR hQ) (mk v S) n (mk v' G) ∧ (G.inp = buffers.input ∧ G.out = buffers.output) := by
  obtain ⟨v₁,J,n₁,residuals,hu₁,hn₁,he₁,hlen,harchive,hgood,hfactorJ,hshared,hrhsHeaders,h247,h248J,
    hnativeL,hleftFrame,hrightFrame,hperipheral,h93,h110,hshare,hcleanup⟩ :=
    firstCachedReplicaPass_shared_exec_within (body := body) H hR hQ M hpushM hA hspan horigin R K hpushR hpushK hpad buffers v S
      headers hbank hcache hsolverFresh hinput houtputStream hsaved hkeys hdst h86 h119 depth hp hwidth
      hblank hfresh target columns hfactor hwork hmasters hstage hlevel hprivate
      (by simpa only [replicaRecoveryBatchCoupling_bank,recoveryMaskCallerReg] using h159)
      (by simpa only [replicaRecoveryBatchCoupling_bank,recoveryMaskCallerReg] using h161)
  have hworkerL := replicaRecoveryBatchCoupling_worker_left_restored hnativeL hleftFrame
  have hhigh (k : Fin 392) (hk : 300 ≤ k.val) : J.R k = S.R k := by
    apply hrightFrame
    · intro i he
      have hv := congrArg Fin.val he
      have hb := ReplicaCouplingPlacement.reindex_bank replicaRecoveryCallerCoupling
        (Fin.castLE (by decide : 389 ≤ 392)) (Fin.castLE_injective _) i
      change replicaRecoveryBatchCoupling.bank i = Fin.castLE (by decide : 389 ≤ 392) (replicaRecoveryCallerCoupling.bank i) at hb
      have hc := ReplicaCouplingPlacement.reindex_bank ReplicaCouplingPlacement.standard
        (Fin.castLE (by decide : 300 ≤ 389)) (Fin.castLE_injective _) i
      change replicaRecoveryCallerCoupling.bank i = Fin.castLE (by decide : 300 ≤ 389) (ReplicaCouplingPlacement.standard.bank i) at hc
      rw [hb,hc] at hv
      change (ReplicaCouplingPlacement.standard.bank i).val = k.val at hv
      have hi := (ReplicaCouplingPlacement.standard.bank i).isLt
      omega
    · intro i he
      have hv := congrArg Fin.val he
      change i.val = k.val at hv
      have hi := i.isLt
      omega
    · intro i he
      have hv := congrArg Fin.val he
      change 126+i.val = k.val at hv
      have hi := i.isLt
      omega
    · intro he; have hv := congrArg Fin.val he; change 247 = k.val at hv; omega
    · intro he; have hv := congrArg Fin.val he; change 248 = k.val at hv; omega
  have hleftSharedJ (i : Fin 242) : J.L (replicaRecoveryPreparationCallerWorkerReg (Fin.castLE (by decide : 242 ≤ 257) i)) =
      J.L (replicaRecoveryPreparationCallerWorkerReg (Fin.castLE (by decide : 255 ≤ 257) (replicaBoundaryPhaseReg i))) :=
    (congrFun hworkerL _).trans ((hleftShared i).trans (congrFun hworkerL _).symm)
  have hblankSetupJ (i : Fin 255) (hi : 248 ≤ i.val) : J.R (replicaRecoverySetupWorkerReg i) = [] := by
    have hh := replicaRecoveryBatchCoupling_factor_extension_frame hrightFrame
      (Fin.castLE (by decide : 255 ≤ 257) i) (by change 168 ≤ i.val; omega)
    have hs := hblankSetup i hi
    rw [replicaRecoverySetupWorkerReg_eq] at hs ⊢
    exact hh.trans hs
  have h159J : J.R (recoveryMaskCallerReg 159) = [] := by
    have hh := hshare 159 (by decide) (by decide)
    norm_num only [replicaRecoveryBatchCoupling_bank,Fin.castLE] at hh
    exact hh.trans h159
  have h161J : J.R (recoveryMaskCallerReg 161) = [] := by
    have hh := hshare 161 (by decide) (by decide)
    norm_num only [replicaRecoveryBatchCoupling_bank,Fin.castLE] at hh
    exact hh.trans h161
  have h167J : J.R (replicaRecoveryPreparationCallerWorkerReg 167) = [] := by
    have hh := hshare 167 (by decide) (by decide)
    norm_num only [replicaRecoveryBatchCoupling_bank,Fin.castLE] at hh
    exact hh.trans (hwork.scratch 167 (by decide))
  have hleftJ (i : Fin 117) : J.L (replicaRecoveryPreparationCallerReg (Fin.castLE (by decide : 117 ≤ 258) i)) = [] := by
    have hh := hbank
    rw [replicaRecoveryBatchCoupling_native_view S] at hh
    have hs := congrArg (fun Z : Stacks 117 A => Z.L i) hh
    exact (congrFun hworkerL (Fin.castLE (by decide : 117 ≤ 257) i)).trans hs
  have h125J : J.R (replicaRecoveryPreparationCallerWorkerReg 125) = S.R (replicaRecoveryPreparationCallerWorkerReg 125) := by
    have hh := hshare 125 (by decide) (by decide)
    norm_num only [replicaRecoveryBatchCoupling_bank,Fin.castLE] at hh
    exact hh
  obtain ⟨B,Ds,v',G,n₂,outputs,hlenD,hu₂,hn₂,hcert,h257,hout,houtput,he₂,hstreams⟩ :=
    releasedPreparedCachedReplicaRecovery_exec_within (body := body) H target hR hQ hA hp hwidth hspan hpad htarget
      columns push c hpush M hpushM X hX R K hpushR hpushK buffers v₁ J hrhsHeaders
      ((hhigh 391 (by decide)).trans h391) residuals hlen harchive hgood hfactorJ hleftSharedJ hshared h167J
      hrhsHeaders.volume hblankSetupJ hperipheral h159J h161J
      (by rw [hhigh 390 (by decide)]; exact hcount) hleftJ h93 h110 (h248J.trans h248) depth
  refine ⟨B,Ds,v',G,n₁+n₂,outputs,hlenD,hu₂.trans hu₁,?_,hcert,h257.trans h125J,hout,houtput,?trace,hstreams⟩
  · have add_cost (a b c d x y z : ℕ) (hx : x ≤ a) (hy : y ≤ z+b+c) (hz : z ≤ d) :
        x+y ≤ a+(d+b+c) := by omega
    exact add_cost _ _ _ _ _ _ _ hn₁ hn₂ hcleanup
  case trace =>
    exact mn_seq_within_add
      (a := initializedCachedReplicaInteriorWorkspace (A := A) (U := U) H hQ R K M)
      (b := preparedCachedBatchedReplicaRecoveryWorkspace H (B.problem htarget) hQ push c M R K) he₁ he₂

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
