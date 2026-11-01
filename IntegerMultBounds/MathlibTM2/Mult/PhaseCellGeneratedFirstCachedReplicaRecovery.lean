module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedGeneratedReplicaBoundaryFactory
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFirstCachedReplicaRecovery

/-! Physical factor generation followed by the complete cached two-pass caller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 392 Q A U}

noncomputable def generatedFirstCachedReplicaRecovery (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 392 Q A U :=
  .seq (placedGeneratedReplicaBoundaryFactory hR hQ) (firstCachedReplicaRecovery hR hQ)

theorem generatedFirstCachedReplicaRecovery_exec (H : ReplicaHaloProblem s) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hspan : H.span+H.band ≤ s) (horigin : H.origin < s)
    (R K : ℕ)
    (hpushR : mnProgPush (rpProg (P := Empty) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R)
    (hpushK : mnProgPush (cmulBlock cr (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr)) ≤ K)
    (hpad : 2*((s/(H.t-s)+1)-2*H.band) ≤ 2^H.l+1)
    (buffers : ReplicaLoopBuffers A) (v : HS 392 Q A U) (S : Stacks 392 A)
    (headers : ReplicaLoopHeaders H replicaRecoveryBatchInterior.gather buffers S)
    (hraw : buffers.rhsTail = []) (hresult : buffers.solverOutputTail = [])
    (hcache : S.R (replicaRecoveryBatchInterior.solver 117) = buffers.cacheTail)
    (hsolverFresh : ∀ k ∈ [(118 : Fin 121),119,120], S.R (replicaRecoveryBatchInterior.solver k) = [])
    (hinput : S.inp = buffers.input) (houtputStream : S.out = buffers.output)
    (hsaved : embStk replicaRecoveryBatchInterior.gather S = buffers.savedGather)
    (hkeys : S.R (replicaRecoveryBatchInterior.gather 87) = buffers.keyTail) (hdst : S.R 247 = buffers.accumulatorTail)
    (h86 : S.R (replicaRecoveryBatchInterior.gather 86) = []) (h119 : S.R (replicaRecoveryBatchInterior.gather 119) = []) (depth : ℕ)
    (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (target : ℕ)
    (hblank : ∀ i, S.R (replicaRecoveryBoundaryFactoryReg i) = [])
    (hleft : ∀ i, S.L (replicaRecoveryBoundaryFactoryReg i) = [])
    (hprivateLeft : ∀ i : Fin 255, 248 ≤ i.val →
      S.L (replicaRecoverySetupWorkerReg i) = [])
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
    (hblankSetup : ∀ i : Fin 255, 248 ≤ i.val → S.R (replicaRecoverySetupWorkerReg i) = [])
    (hcount : (S.R 390).length = H.Fs.length) (h391 : S.R 391 = []) (h248 : S.R 248 = []) :
    ∃ B : ReplicaRecoveryBatch H target X, ∃ Ds : List (ZMod s → GaussianInt), ∃ v' G n outputs,
      Ds.length = H.Fs.length ∧ v'.user = v.user ∧ n ≤ generatedReplicaBoundaryFactoryCost H target+firstCachedReplicaRecoveryTime H (B.problem htarget) ∧
      List.Forall₂ (ReplicaRecoveryAssemblyOutput B Ds) (List.finRange H.Fs.length) outputs ∧
      G.R 257 = [] ∧ G.R 247 = buffers.accumulatorTail ∧
      G.R 391 = outputs.reverse.flatten ∧ Exec body (generatedFirstCachedReplicaRecovery hR hQ) (mk v S) n (mk v' G) := by
  obtain ⟨v₁,F,n₁,columns,hu₁,hn₁,he₁,hdata,hmasters,hstage,hlevel,hgeometry,hgather,hin,hout,hoff,hwork,hmasks⟩ :=
    placedGeneratedReplicaBoundaryFactory_exec (body := body) H target hR hQ hA hp hwidth hpad htarget
      buffers v S headers h119 hblank hleft
  have hworkerOff (k : Fin 257) (hk : 242 ≤ k.val) (i : Fin 242) :
      replicaRecoveryBoundaryFactoryReg i ≠ replicaRecoveryPreparationCallerWorkerReg k := by
    intro he
    have hinj : Function.Injective replicaRecoveryPreparationCallerWorkerReg :=
      replicaRecoveryPreparationCallerReg_injective.comp (Fin.castLE_injective _)
    have hv := congrArg Fin.val (hinj he)
    change i.val = k.val at hv
    have hi := i.isLt
    omega
  have hsolverOff (j : Fin 121) (hj : 117 ≤ j.val) (i : Fin 242) :
      replicaRecoveryBoundaryFactoryReg i ≠ replicaRecoveryBatchInterior.solver j :=
    replicaRecoveryPreparationCallerReg_reserved _ j hj
  have hgap (k : Fin 392) (hk : 243 ≤ k.val ∧ k.val < 249) (i : Fin 242) :
      replicaRecoveryBoundaryFactoryReg i ≠ k := by
    intro he
    have hh := replicaRecoveryPreparationCallerReg_gap
      (replicaRecoveryPreparationWorkerReg (Fin.castLE (by decide : 242 ≤ 257) i))
    change (replicaRecoveryBoundaryFactoryReg i).val < 243 ∨ 249 ≤ (replicaRecoveryBoundaryFactoryReg i).val at hh
    rw [he] at hh
    omega
  have hhigh (k : Fin 392) (hk : 389 ≤ k.val) (i : Fin 242) :
      replicaRecoveryBoundaryFactoryReg i ≠ k := by
    rw [replicaRecoveryBoundaryFactoryReg_reindex]
    intro he
    have hv := congrArg Fin.val he
    change (replicaRecoveryCallerFactoryReg i).val = k.val at hv
    have hi := (replicaRecoveryCallerFactoryReg i).isLt
    omega
  have hprivateLeftF (i : Fin 255) (hi : 248 ≤ i.val) : F.L (replicaRecoverySetupWorkerReg i) = [] := by
    rw [replicaRecoverySetupWorkerReg_eq]
    exact (hoff _ (hworkerOff _ (by change 242 ≤ i.val; omega))).1.trans
      (by simpa only [replicaRecoverySetupWorkerReg_eq] using hprivateLeft i hi)
  have hshared : ∀ i : Fin 242,
      F.L (replicaRecoveryPreparationCallerWorkerReg (Fin.castLE (by decide : 242 ≤ 257) i)) =
      F.L (replicaRecoveryPreparationCallerWorkerReg (Fin.castLE (by decide : 255 ≤ 257) (replicaBoundaryPhaseReg i))) := by
    have hview : embStk (Fin.castLE (by decide : 242 ≤ 255)) (embStk replicaRecoverySetupWorkerReg F) =
        embStk replicaRecoveryBoundaryFactoryReg F := by
      refine Stacks.ext rfl rfl ?_ ?_ <;> funext i
      · exact congrArg F.L (replicaRecoverySetupWorkerReg_eq (Fin.castLE (by decide : 242 ≤ 255) i))
      · exact congrArg F.R (replicaRecoverySetupWorkerReg_eq (Fin.castLE (by decide : 242 ≤ 255) i))
    have hbank := hdata.bank
    rw [←hview] at hbank
    have hmask : F.L (replicaRecoverySetupWorkerReg 167) = [] := by
      rw [replicaRecoverySetupWorkerReg_eq]
      exact hwork.maskLeft
    have hh := replicaBoundaryPhase_left_of_bank (embStk replicaRecoverySetupWorkerReg F)
      hbank hmask hprivateLeftF
    intro i
    exact (congrArg F.L (replicaRecoverySetupWorkerReg_eq (Fin.castLE (by decide : 242 ≤ 255) i))).symm.trans
      ((hh i).trans (congrArg F.L (replicaRecoverySetupWorkerReg_eq (replicaBoundaryPhaseReg i))))
  have hblankSetupF (i : Fin 255) (hi : 248 ≤ i.val) : F.R (replicaRecoverySetupWorkerReg i) = [] := by
    rw [replicaRecoverySetupWorkerReg_eq]
    exact (hoff _ (hworkerOff _ (by change 242 ≤ i.val; omega))).2.trans
      (by simpa only [replicaRecoverySetupWorkerReg_eq] using hblankSetup i hi)
  obtain ⟨B,Ds,v',G,n₂,outputs,hlen,hu₂,hn₂,hcert,h257,h247,h391G,he₂⟩ :=
    firstCachedReplicaRecovery_exec (body := body) H hR hQ hA hspan horigin R K hpushR hpushK hpad buffers v₁ F
      (headers.of_gather_view hgather)
      (by rw [hraw,hresult]; exact hdata.initial_native_bank H target columns hwork)
      ((hoff _ (hsolverOff 117 (by decide))).2.trans hcache)
      (by intro k hk
          have hb : 117 ≤ k.val := by
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
            rcases hk with rfl | rfl | rfl <;> decide
          exact (hoff _ (hsolverOff k hb)).2.trans (hsolverFresh k hk))
      (hin.trans hinput) (hout.trans houtputStream) (hgather.trans hsaved)
      ((congrArg (fun C : Stacks 126 A => C.R 87) hgather).trans hkeys)
      ((hoff 247 (hgap 247 (by decide))).2.trans hdst)
      ((congrArg (fun C : Stacks 126 A => C.R 86) hgather).trans h86)
      ((congrArg (fun C : Stacks 126 A => C.R 119) hgather).trans h119) depth hp hwidth
      (by intro k hk
          apply hgeometry k
          simp only [replicaFactoryGeometryPorts,couplingIntervalPorts,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hk ⊢
          norm_num at hk ⊢
          omega)
      hwork.coupling_fresh target columns hdata hwork hmasters hstage hlevel
      (by intro k hk
          exact ⟨(hoff _ (hworkerOff _ hk)).1.trans (hprivate k hk).1,
            (hoff _ (hworkerOff _ hk)).2.trans (hprivate k hk).2⟩)
      push c hpush M hpushM X hX htarget hshared hblankSetupF hmasks.1 hmasks.2
      (by rw [(hoff 390 (hhigh 390 (by decide))).2]; exact hcount)
      ((hoff 391 (hhigh 391 (by decide))).2.trans h391)
      ((hoff 248 (hgap 248 (by decide))).2.trans h248)
  refine ⟨B,Ds,v',G,n₁+n₂,outputs,hlen,hu₂.trans hu₁,by omega,hcert,?_,h247,h391G,Exec.seq he₁ he₂⟩
  exact h257.trans (hwork.scratch 125 (by decide))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
