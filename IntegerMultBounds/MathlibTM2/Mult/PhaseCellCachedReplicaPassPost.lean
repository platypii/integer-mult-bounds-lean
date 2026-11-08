module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaInteriorResumeReady

/-! Retain the executed cached pass's archive, accuracy, cache and recovery
language when a disjoint pass runs afterward. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

structure CachedReplicaPassPost {s T A : ℕ} [NeZero s] (H : ReplicaHaloProblem s)
    (job : CachedReplicaPassPlacement T) (buffers : ReplicaLoopBuffers A)
    (S F : Stacks T A) (Ds : List (ZMod s → GaussianInt)) : Prop where
  clock : F.R (job.plan.gather 122) = []
  output : F.R job.output = buffers.accumulatorTail
  rhs : F.R job.rhs = S.R job.rhs
  ready : RetainedCouplingReady (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
    H.origin (H.origin+H.span) buffers.rhsTail (embStk weightCacheCoreReg (embStk job.plan.solver F))
  metadata : CouplingIntervalMetadata H.metadataWidth s H.t H.band H.origin (H.origin+H.span) H.origin H.span
    (embStk job.coupling.bank F)
  input : F.inp = S.inp
  outputStream : F.out = S.out
  gatherLeft : (embStk job.plan.gather F).L = (embStk job.plan.gather S).L
  gatherRight : ∀ i : Fin 126, i ≠ 125 → F.R (job.plan.gather i) = S.R (job.plan.gather i)
  cache : F.R (job.plan.solver 117) = buffers.cacheTail
  solverFresh : ∀ i ∈ [(118 : Fin 121),119,120], F.R (job.plan.solver i) = []
  nativeLeft : (embStk weightCacheCoreReg (embStk job.plan.solver F)).L =
    (embStk weightCacheCoreReg (embStk job.plan.solver S)).L
  length : Ds.length = H.Fs.length
  archive : F.R (job.plan.gather 125) = Ds.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))
  residual : ∀ j : Fin Ds.length, ReplicaCouplingResidualSpec H (H.Fs.length-1-j.val) (Ds[j.val]'j.isLt)
  coefficients : F.R (job.coupling.bank 138) = cstream A H.wordWidth
    (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span)++
      S.R (job.coupling.bank 138)
  coefficientWords : (F.R (job.coupling.bank 139)).length =
    (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span).length
  coefficientRows : (F.R (job.coupling.bank 140)).length = 2*H.band+1
  fresh : ∀ i ∈ [(127 : Fin 168),143,166,158,135,167], F.R (job.coupling.bank i) = []
  format : ∀ D ∈ Ds, (∀ i, ‖value H.precision (D i)‖ ≤ (2 : ℝ)^replicaResidualExponent H) ∧
    (∀ i, Fits H.wordWidth (D i))
  accurate : ReplicaCouplingResidualsAccurate H Ds
  nativeR : (embStk weightCacheCoreReg (embStk job.plan.solver F)).R =
    counterR H.precision H.wordWidth
      (replicaCouplingUnaryBank A (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
        H.origin (H.origin+H.span) buffers.rhsTail buffers.solverOutputTail S.inp S.out).R
  cleanup : releaseReplicaCouplingNativeCost (extendStacks (by decide : 117 ≤ 248)
    (embStk weightCacheCoreReg (embStk job.plan.solver F))) ≤
      replicaCouplingNativeCleanupBound (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span)
  bankFrame : ∀ i : Fin 168, 117 ≤ i.val → i ∉ replicaCouplingSetupPorts →
    F.R (job.coupling.bank i) = S.R (job.coupling.bank i)
  retainedHeaders : CouplingMasterHeaders (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
    H.origin (H.origin+H.span) (embStk job.coupling.bank S) →
    (S.R (job.coupling.bank 118)).length = H.stage+1 → (S.R (job.coupling.bank 120)).length = H.l →
    PackedHaloRetainedHeaders (2^15*H.p) (H.stage+1) H.precision H.l s H.t H.u H.band
      H.origin (H.origin+H.span) H.metadataWidth H.wordWidth (embStk job.coupling.bank F)
  recoveryRhs : ReplicaRecoveryRhsHeaders H job.plan.gather buffers F
  recoveryWork : ∀ i ∈ [(136 : Fin 168),159,161], F.R (job.coupling.bank i) = []
  resume : ReplicaInteriorResumeReady H job buffers F

theorem CachedReplicaPassPost.of_frame {s T A : ℕ} [NeZero s] {H : ReplicaHaloProblem s}
    {job : CachedReplicaPassPlacement T} {buffers : ReplicaLoopBuffers A} {S F G : Stacks T A}
    {Ds : List (ZMod s → GaussianInt)} (h : CachedReplicaPassPost H job buffers S F Ds)
    (hin : G.inp = F.inp) (hout : G.out = F.out)
    (hf : ∀ k, job.Owns k → G.L k = F.L k ∧ G.R k = F.R k) :
    CachedReplicaPassPost H job buffers S G Ds := by
  have hg : embStk job.plan.gather G = embStk job.plan.gather F := by
    refine Stacks.ext hin hout ?_ ?_
    · funext i; exact (hf _ (.gather i)).1
    · funext i; exact (hf _ (.gather i)).2
  have hs : embStk job.plan.solver G = embStk job.plan.solver F := by
    refine Stacks.ext hin hout ?_ ?_
    · funext i; exact (hf _ (.solver i)).1
    · funext i; exact (hf _ (.solver i)).2
  have hb : embStk job.coupling.bank G = embStk job.coupling.bank F := by
    refine Stacks.ext hin hout ?_ ?_
    · funext i; exact (hf _ (.bank i)).1
    · funext i; exact (hf _ (.bank i)).2
  refine ⟨(hf _ (.gather 122)).2.trans h.clock,(hf _ .output).2.trans h.output,
    (hf _ .rhs).2.trans h.rhs,?_,?_,hin.trans h.input,hout.trans h.outputStream,?_,?_,
    (hf _ (.solver 117)).2.trans h.cache,?_,?_,h.length,(hf _ (.gather 125)).2.trans h.archive,
    h.residual,?_,?_,?_,?_,h.format,h.accurate,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [hs] using h.ready
  · simpa only [hb] using h.metadata
  · simpa only [hg] using h.gatherLeft
  · intro i hi; exact (hf _ (.gather i)).2.trans (h.gatherRight i hi)
  · intro i hi; exact (hf _ (.solver i)).2.trans (h.solverFresh i hi)
  · simpa only [hs] using h.nativeLeft
  · exact (hf _ (.bank 138)).2.trans h.coefficients
  · simpa only [(hf _ (.bank 139)).2] using h.coefficientWords
  · simpa only [(hf _ (.bank 140)).2] using h.coefficientRows
  · intro i hi; exact (hf _ (.bank i)).2.trans (h.fresh i hi)
  · simpa only [hs] using h.nativeR
  · simpa only [hs] using h.cleanup
  · intro i hi hport; exact (hf _ (.bank i)).2.trans (h.bankFrame i hi hport)
  · simpa only [hb] using h.retainedHeaders
  · exact ReplicaRecoveryRhsHeaders.of_frame H job.plan.gather buffers F G h.recoveryRhs
      (fun i => (hf _ (.gather i)).2)
  · intro i hi
    exact (hf _ (.bank i)).2.trans (h.recoveryWork i hi)
  · exact h.resume.of_frame hin hout hf

/-- The retained numerical bank already provides the blank workspace needed by
metadata-driven mask generation; no extra cleanup premise is required. -/
theorem CachedReplicaPassPost.maskBlank {s T A : ℕ} [NeZero s] {H : ReplicaHaloProblem s}
    {job : CachedReplicaPassPlacement T} {buffers : ReplicaLoopBuffers A} {S F : Stacks T A}
    {Ds : List (ZMod s → GaussianInt)} (h : CachedReplicaPassPost H job buffers S F Ds) :
    ∀ i : Fin 168, i.val < 32 → F.R (job.coupling.bank i) = [] := by
  intro i hi
  have hclean := (h.ready.clean (⟨i.val,by omega⟩ : Fin 64)).2
  simpa [embStk,weightCacheCoreReg,mul,ReplicaCouplingPlacement.bank,show i.val < 117 by omega] using hclean

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
