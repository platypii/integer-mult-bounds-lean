module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedReplicaPassInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryAssemblyControls

/-! The first pass retains the peripheral state for another interior solve.
The saved boundary archive is excluded from disposable gather workspace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

structure ReplicaInteriorResumeReady {s T A : ℕ} (H : ReplicaHaloProblem s)
    (job : CachedReplicaPassPlacement T) (buffers : ReplicaLoopBuffers A) (S : Stacks T A) : Prop where
  headers : ReplicaLoopHeaders H job.plan.gather buffers
    {S with R := Function.update S.R (job.plan.gather 125) []}
  cache : S.R (job.plan.solver 117) = buffers.cacheTail
  solverFresh : ∀ i ∈ [(118 : Fin 121),119,120], S.R (job.plan.solver i) = []
  input : S.inp = buffers.input
  output : S.out = buffers.output
  keys : S.R (job.plan.gather 87) = buffers.keyTail
  destination : S.R job.output = buffers.accumulatorTail
  packets : S.R (job.plan.gather 86) = []
  count : S.R (job.plan.gather 119) = []
  nativeLeft : ∀ i : Fin 117, S.L (job.plan.solver (weightCacheCoreReg i)) = []

theorem ReplicaLoopHeaders.of_archive_frame {s T A : ℕ} {H : ReplicaHaloProblem s}
    {gather : Fin 126 → Fin T} (hinj : Function.Injective gather) {buffers : ReplicaLoopBuffers A}
    {S F : Stacks T A} (h : ReplicaLoopHeaders H gather buffers S)
    (hf : ∀ i : Fin 126, i ≠ 125 → F.R (gather i) = S.R (gather i)) :
    ReplicaLoopHeaders H gather buffers {F with R := Function.update F.R (gather 125) []} := by
  apply h.of_frame
  intro i _ _
  by_cases hi : i = 125
  · subst i
    simpa only [Function.update_self] using (h.fresh 125 (by simp)).symm
  · simpa only [Function.update_of_ne (hinj.ne hi)] using hf i hi

theorem ReplicaInteriorResumeReady.transport {s T T' A : ℕ} {H : ReplicaHaloProblem s}
    {job : CachedReplicaPassPlacement T} {job' : CachedReplicaPassPlacement T'}
    {buffers : ReplicaLoopBuffers A} {S : Stacks T A} {F : Stacks T' A}
    (h : ReplicaInteriorResumeReady H job buffers S) (hin : F.inp = S.inp) (hout : F.out = S.out)
    (hgather : ∀ i : Fin 126, i ≠ 125 → F.R (job'.plan.gather i) = S.R (job.plan.gather i))
    (hsolver : ∀ i : Fin 121, 117 ≤ i.val → F.R (job'.plan.solver i) = S.R (job.plan.solver i))
    (hleft : ∀ i : Fin 117, F.L (job'.plan.solver (weightCacheCoreReg i)) =
      S.L (job.plan.solver (weightCacheCoreReg i)))
    (hdst : F.R job'.output = S.R job.output) : ReplicaInteriorResumeReady H job' buffers F := by
  have hg (i : Fin 126) :
      Function.update F.R (job'.plan.gather 125) [] (job'.plan.gather i) =
      Function.update S.R (job.plan.gather 125) [] (job.plan.gather i) := by
    by_cases hi : i = 125
    · subst i; simp only [Function.update_self]
    · simpa only [Function.update_of_ne (job'.plan.gather_injective.ne hi),
        Function.update_of_ne (job.plan.gather_injective.ne hi)] using hgather i hi
  refine ⟨?_,(hsolver 117 (by decide)).trans h.cache,?_,hin.trans h.input,hout.trans h.output,
    (hgather 87 (by decide)).trans h.keys,hdst.trans h.destination,
    (hgather 86 (by decide)).trans h.packets,(hgather 119 (by decide)).trans h.count,?_⟩
  · constructor
    · intro r hr h102 h116
      exact (congrArg List.length (hg r.1)).trans (h.headers.masters r hr h102 h116)
    · exact (congrArg List.length (hg 111)).trans h.headers.origin
    · exact (congrArg List.length (hg 113)).trans h.headers.endpoint
    · exact (congrArg List.length (hg 115)).trans h.headers.width
    · exact (congrArg List.length (hg 123)).trans h.headers.volume
    · exact (hg 124).trans h.headers.source
    · intro i hi; exact (hg i).trans (h.headers.blank i hi)
    · intro i hi; exact (hg i).trans (h.headers.fresh i hi)
  · intro i hi
    have hi' : 117 ≤ i.val := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    exact (hsolver i hi').trans (h.solverFresh i hi)
  · intro i; exact (hleft i).trans (h.nativeLeft i)

theorem ReplicaInteriorResumeReady.of_frame {s T A : ℕ} {H : ReplicaHaloProblem s}
    {job : CachedReplicaPassPlacement T} {buffers : ReplicaLoopBuffers A} {S F : Stacks T A}
    (h : ReplicaInteriorResumeReady H job buffers S) (hin : F.inp = S.inp) (hout : F.out = S.out)
    (hf : ∀ k, job.Owns k → F.L k = S.L k ∧ F.R k = S.R k) :
    ReplicaInteriorResumeReady H job buffers F :=
  h.transport hin hout (fun i _ => (hf _ (.gather i)).2)
    (fun i _ => (hf _ (.solver i)).2) (fun i => (hf _ (.solver (weightCacheCoreReg i))).1)
    (hf _ .output).2

theorem ReplicaInteriorResumeReady.assembly_controls {s T A : ℕ} {H : ReplicaHaloProblem s}
    {job : CachedReplicaPassPlacement T} {buffers : ReplicaLoopBuffers A} {S : Stacks T A}
    (h : ReplicaInteriorResumeReady H job buffers S) (master : Fin T)
    (hmask : S.R master = couplingSourceIntervalMaskSymbols true A s H.t H.band H.origin
      (H.origin+H.span) H.origin H.span) : ReplicaAssemblyControls H job.plan.gather master S := by
  refine ⟨hmask,?_,?_⟩
  · have hw := h.headers.masters (94,94) (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide)
    simpa [Function.update_of_ne (job.plan.gather_injective.ne (by decide : (94 : Fin 126) ≠ 125)),
      replicaFactoryHeaderValue] using hw
  · have hn := h.headers.masters (121,113) (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide)
    simpa [Function.update_of_ne (job.plan.gather_injective.ne (by decide : (121 : Fin 126) ≠ 125)),
      replicaFactoryHeaderValue] using hn

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
