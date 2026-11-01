module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedReplicaBoundaryFactory
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedReplicaInteriorRecoveryExec

/-! Execute generated shared factor setup and all-replica interior/coupling/
recovery from ordinary gather headers and initially blank numerical storage. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 389 Q A U}

theorem ReplicaFactoryWorkspace.native_bank {A q w W N : ℕ} {S : Stacks 242 A}
    (h : ReplicaFactoryWorkspace S) (hbank : PackedPreparedBank q w W N S) :
    embStk (Fin.castLE (by decide : 117 ≤ 242)) S = releasedCellBank [] [] [] S.inp S.out := by
  refine Stacks.ext rfl rfl ?_ ?_ <;> funext i
  · exact hbank.workspace.left_low ⟨i.val,by have hi := i.isLt; omega⟩
  · have hz : (releasedCellBank (A := A) [] [] [] S.inp S.out).R i = [] := by simp [releasedCellBank]
    exact (h.native i).trans hz.symm

theorem replicaRecoveryCallerFactoryReg_solver_reserved (i : Fin 242) (j : Fin 121) (hj : 117 ≤ j.val) :
    replicaRecoveryCallerFactoryReg i ≠ replicaRecoveryCallerInterior.solver j := by
  by_cases hi : i.val < 117
  · have hp : replicaRecoveryCallerFactoryReg i =
        replicaRecoveryCallerInterior.solver (weightCacheCoreReg ⟨i.val,hi⟩) := by
      have hh := replicaRecoveryCallerCoupling.bank_native (⟨i.val,hi⟩ : Fin 117)
      rw [replicaRecoveryCallerCoupling_bank] at hh
      exact hh
    rw [hp]
    intro he
    have hv := congrArg (fun k : Fin 121 => k.val) (replicaRecoveryCallerInterior.solver_injective he)
    change i.val = j.val at hv
    omega
  · have hb := replicaRecoveryCallerWorkerReg_high (Fin.castLE (by decide : 242 ≤ 255) i) (by change 117 ≤ i.val; omega)
    intro he
    have hv := congrArg (fun k : Fin 389 => k.val) he
    change (replicaRecoveryCallerWorkerReg (Fin.castLE (by decide) i)).val = 126+j.val at hv
    have hlt := j.isLt
    omega

noncomputable def generatedReplicaRecovery (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 389 Q A U :=
  .seq (generatedReplicaBoundaryFactory hR hQ) (initializedReplicaInteriorRecovery hR hQ)

noncomputable def generatedReplicaRecoveryCost (H : ReplicaHaloProblem s) (target : ℕ) :=
  generatedReplicaBoundaryFactoryCost H target+initializedReplicaInteriorRecoveryCost H target

theorem generatedReplicaRecovery_exec (H : ReplicaHaloProblem s)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (hspan : H.span+H.band ≤ s) (horigin : H.origin < s)
    (hpad : 2*((s/(H.t-s)+1)-2*H.band) ≤ 2^H.l+1)
    (target : ℕ)
    (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card)
    (X : ℕ → ZMod s → ℝ)
    (hX : ∀ r < H.Fs.length, Solves (realMatrix s H.t H.p H.u) (haloVertices s H.origin (H.origin+H.span)) (X r)
      (fun i => (value H.precision (H.Fs.reverse.getD (H.Fs.length-1-r) (fun _ => 0) i)).re))
    (buffers : ReplicaLoopBuffers A) (v : HS 389 Q A U) (S : Stacks 389 A)
    (headers : ReplicaLoopHeaders H replicaRecoveryCallerInterior.gather buffers S)
    (hraw : buffers.rhsTail = []) (hresult : buffers.solverOutputTail = [])
    (hcache : S.R (replicaRecoveryCallerInterior.solver 117) = buffers.cacheTail)
    (hsolverFresh : ∀ k ∈ [(118 : Fin 121),119,120], S.R (replicaRecoveryCallerInterior.solver k) = [])
    (hinput : S.inp = buffers.input) (houtput : S.out = buffers.output)
    (hsaved : embStk replicaRecoveryCallerInterior.gather S = buffers.savedGather)
    (hkeys : S.R (replicaRecoveryCallerInterior.gather 87) = buffers.keyTail)
    (hdst : S.R 247 = buffers.accumulatorTail)
    (h86 : S.R (replicaRecoveryCallerInterior.gather 86) = []) (h119 : S.R 119 = [])
    (hblank : ∀ i, S.R (replicaRecoveryCallerFactoryReg i) = [])
    (hleft : ∀ i, S.L (replicaRecoveryCallerFactoryReg i) = [])
    (hprivateLeft : ∀ k : Fin 255, 242 ≤ k.val → S.L (replicaRecoveryCallerWorkerReg k) = [])
    (hprivate : ∀ k : Fin 255, 242 ≤ k.val → S.R (replicaRecoveryCallerWorkerReg k) = [])
    (hqueue : S.R 388 = []) (hcontroller : S.R 387 = []) :
    ∃ v' G n, ∃ columns : List (ZMod s → GaussianInt), v'.user = v.user ∧ n ≤ generatedReplicaRecoveryCost H target ∧
      Exec body (generatedReplicaRecovery hR hQ) (mk v S) n (mk v' G) ∧
      G.R 387 = [] ∧ (G.R 121).length = H.Fs.length ∧ G.R 125 = [] ∧ G.R 388 = [] ∧
      RecoveredReplicaArchive H target X [] (embStk replicaRecoveryCallerWorkerReg G) ∧
      ReplicaRecoveryCoreReady H (12*H.band+1) (embStk replicaRecoveryCallerNativeReg G) ∧
      ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg (embStk replicaRecoveryCallerWorkerReg G)) ∧
      ReplicaBoundaryFactorData H target columns (embStk replicaRecoveryCallerFactoryReg G) := by
  obtain ⟨v₁,F,n₁,columns,hu₁,hn₁,he₁,hdata,hmasters,hstage,hlevel,hgeometry,hgather,hinp,hout,hoff,hwork,_⟩ :=
    generatedReplicaBoundaryFactory_exec (body := body) H target hR hQ hA hp hwidth hpad htarget
      buffers v S headers h119 hblank hleft
  have hg (k : Fin 126) : F.R (replicaRecoveryCallerInterior.gather k) = S.R (replicaRecoveryCallerInterior.gather k) :=
    congrArg (fun B : Stacks 126 A => B.R k) hgather
  have hheaders : ReplicaLoopHeaders H replicaRecoveryCallerInterior.gather buffers F :=
    headers.of_frame (by intro k _ _; exact hg k)
  have hbank : embStk weightCacheCoreReg (embStk replicaRecoveryCallerInterior.solver F) =
      releasedCellBank [] buffers.rhsTail buffers.solverOutputTail F.inp F.out := by
    rw [replicaRecoveryCallerCoupling_native_view,hraw,hresult]
    exact hwork.native_bank hdata.bank
  have hbankView : embStk (Fin.castLE (by decide : 168 ≤ 242)) (embStk replicaRecoveryCallerFactoryReg F) =
      embStk replicaRecoveryCallerCoupling.bank F := replicaRecoveryCallerCoupling_runtime_view F
  have hscratch (k : Fin 168) (hk : Fin.castLE (by decide : 168 ≤ 242) k ∈ replicaFactoryScratchPorts) :
      F.R (replicaRecoveryCallerCoupling.bank k) = [] := by
    have hh := congrArg (fun B : Stacks 168 A => B.R k) hbankView
    exact hh.symm.trans (hwork.scratch _ hk)
  have hprivateOff (k : Fin 255) (hk : 242 ≤ k.val) (i : Fin 242) :
      replicaRecoveryCallerFactoryReg i ≠ replicaRecoveryCallerWorkerReg k := by
    intro he
    have hv := congrArg (fun k : Fin 255 => k.val) (replicaRecoveryCallerWorkerReg_injective he)
    change i.val = k.val at hv
    have hi := i.isLt
    omega
  have hqueueOff (k : Fin 259) (hk : 242 ≤ k.val) (i : Fin 242) :
      replicaRecoveryCallerFactoryReg i ≠ replicaRecoveryCallerReg k := by
    intro he
    have hv := congrArg (fun k : Fin 259 => k.val) (replicaRecoveryCallerReg_injective he)
    change i.val = k.val at hv
    have hi := i.isLt
    omega
  obtain ⟨v',G,n₂,hu₂,hn₂,he₂,h387,h121,h125,h388,harchive,hcore,hphysical,hdataG⟩ :=
    initializedReplicaInteriorRecovery_exec (body := body) H hR hQ hA hp hwidth hspan horigin hpad target columns
      htarget X hX buffers v₁ F hheaders hbank
      ((hoff _ (fun i => replicaRecoveryCallerFactoryReg_solver_reserved i 117 (by decide))).2.trans hcache)
      (by intro k hk
          have hb : 117 ≤ k.val := by
            simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hk
            norm_num at hk
            omega
          exact (hoff _ (fun i => replicaRecoveryCallerFactoryReg_solver_reserved i k hb)).2.trans (hsolverFresh k hk))
      (hinp.trans hinput) (hout.trans houtput) (hgather.trans hsaved)
      ((hg 87).trans hkeys)
      ((hoff _ (fun i => (replicaRecoveryCallerReg_outputs_disjoint _).1)).2.trans hdst)
      ((hg 86).trans h86) ((hg 119).trans h119) hdata hmasters hstage hlevel
      (by
        intro k hk
        apply hgeometry k
        simp only [replicaFactoryGeometryPorts,couplingIntervalPorts,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hk ⊢
        norm_num at hk ⊢
        omega)
      (by
        intro k hk
        apply hscratch k
        simp only [replicaFactoryScratchPorts,List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hk ⊢
        norm_num at hk ⊢
        omega)
      (hscratch 138 (by decide))
      (by
        intro k hk
        apply hwork.scratch
        simp only [replicaFactoryScratchPorts,List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hk ⊢
        norm_num at hk ⊢
        omega)
      hwork.maskLeft
      (by intro k hk; exact (hoff _ (hprivateOff k hk)).1.trans (hprivateLeft k hk))
      (by intro k hk; exact (hoff _ (hprivateOff k hk)).2.trans (hprivate k hk))
      ((hoff _ (hqueueOff 258 (by decide))).2.trans hqueue)
      ((hoff _ (hqueueOff 255 (by decide))).2.trans hcontroller)
  have htail : (embStk replicaRecoveryCallerReg F).R 125 = [] := hscratch 125 (by decide)
  rw [htail] at harchive
  exact ⟨v',G,n₁+n₂,columns,hu₂.trans hu₁,by unfold generatedReplicaRecoveryCost; omega,
    Exec.seq he₁ he₂,h387,h121,h125,h388,harchive,hcore,hphysical,hdataG⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
