module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseReplicaInteriorBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaInteriorArchivePlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryInteriorFrame

/-! Release once, reuse the retained first-pass headers, and execute the entire
second interior batch. Saved boundary fields remain on their original tape. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def resumedReplicaInterior (job : CachedReplicaPassPlacement T) (fresh : Fin T)
    (hg : ∀ i, fresh ≠ job.plan.gather i) (hs : ∀ i, fresh ≠ job.plan.solver i)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (releaseReplicaInteriorBank job.plan)
    (replicaRecoveryInterior (job.plan.reserveArchive fresh hg hs) (job.plan.solver 110) job.output hR hQ)

theorem resumedReplicaInterior_exec (H J : ReplicaHaloProblem s) (layout : H.SameLayout J)
    (job : CachedReplicaPassPlacement T) (fresh : Fin T)
    (hg : ∀ i, fresh ≠ job.plan.gather i) (hs : ∀ i, fresh ≠ job.plan.solver i)
    (houtput : fresh ≠ job.output) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (hpad : 2*((s/(H.t-s)+1)-2*H.band) ≤ 2^H.l+1)
    (buffers : ReplicaLoopBuffers A) (borrowed : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (ready : ReplicaInteriorResumeReady H job buffers S) (hblank : S.R fresh = [])
    (hsource : S.R (job.plan.solver 110) = J.Fs.reverse.flatMap
      (fun R => cstream A H.wordWidth (packedInterval H.origin H.span R))++borrowed) :
    ∃ v' G n, v'.user = v.user ∧
      n ≤ releaseReplicaInteriorBankCost job.plan S+replicaRecoveryInteriorTime H J ∧
      RealReplicaHaloOutput J job.output buffers.accumulatorTail G ∧
      G.R (job.plan.gather 125) = S.R (job.plan.gather 125) ∧
      (G.inp = S.inp ∧ G.out = S.out) ∧
      Exec body (resumedReplicaInterior job fresh hg hs hR hQ) (mk v S) n (mk v' G) ∧
      (∀ k, ¬job.Owns k → k ≠ fresh → G.L k = S.L k ∧ G.R k = S.R k) := by
  let plan := job.plan.reserveArchive fresh hg hs
  let F := releasedReplicaInteriorBank job.plan S
  let nextBuffers := {buffers with rhsTail := S.R (job.plan.solver 110), solverOutputTail := S.R (job.plan.solver 93)}
  have hnotFresh : fresh ∉ replicaInteriorReleasePorts job.plan := by
    intro hk
    obtain ⟨i,_,he⟩ := List.mem_map.mp hk
    exact hs _ he.symm
  have hblankF : F.R fresh = [] := (ite_eq_right hnotFresh).trans hblank
  have h110 : F.R (job.plan.solver 110) = S.R (job.plan.solver 110) := by
    apply ite_eq_right
    change ¬job.plan.solver (weightCacheCoreReg (110 : Fin 117)) ∈ replicaInteriorReleasePorts job.plan
    simp only [replicaInteriorReleasePorts_native,ne_eq,not_true_eq_false,and_false,not_false_eq_true]
  have hheaders : ReplicaLoopHeaders H plan.gather nextBuffers F := by
    have h := ready.released.archive_headers fresh hg hs hblankF
    exact ⟨h.masters,h.origin,h.endpoint,h.width,h.volume,h.source,h.blank,h.fresh⟩
  have hgd : ∀ i, plan.gather i ≠ job.output := by
    intro i
    change Function.update job.plan.gather 125 fresh i ≠ _
    by_cases hi : i = 125
    · subst i; simpa only [Function.update_self] using houtput
    · simpa only [Function.update_of_ne hi] using job.gather_output i
  let R := mnProgPush (rpProg (P := Empty) (Q := Q) (A := A) (U := U)
    Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR)
  let K := mnProgPush (cmulBlock cr (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
    mul mul_injective (by decide) hQ cr))
  obtain ⟨v₀,hu₀,he₀⟩ := releaseReplicaInteriorBank_exec (body := body) job.plan v S
  obtain ⟨v',G,m,hu,hm,hfields,hgather,he,hstreams⟩ := replicaInteriorFromArchive_exec_within
    (body := body) H J layout plan (job.plan.solver 110) job.output (fun i => plan.disjoint i 110)
    hgd job.solver_output hR hQ hA hp hwidth hpad R K (le_refl _) (le_refl _) nextBuffers borrowed v₀ F
    hheaders (h110.trans hsource) (releasedReplicaInteriorBank_native job.plan S ready.nativeLeft)
    ready.released.cache ready.released.solverFresh ready.released.input ready.released.output
    ready.released.keys ready.released.destination ready.released.packets ready.released.count 0
  have harchive := replicaRecoveryInterior_preserves plan (job.plan.solver 110) job.output (job.plan.gather 125)
    hR hQ (job.plan.reserveArchive_avoids fresh hg hs)
    (fun i => (job.plan.disjoint 125 i).symm) (job.plan.disjoint 125 110).symm
    (job.gather_output 125).symm he.toExec
  refine ⟨v',G,releaseReplicaInteriorBankCost job.plan S+m,hu.trans hu₀,
    Nat.add_le_add_left hm _,hfields,?_,⟨hstreams.1.trans ready.input.symm,hstreams.2.trans ready.output.symm⟩,
    Exec.seq he₀ he.toExec,?_⟩
  · exact harchive.2.trans (ite_eq_right (replicaInteriorReleasePorts_gather job.plan 125))
  · intro k hk hkfresh
    have hgk : ∀ i, plan.gather i ≠ k := by
      intro i
      change Function.update job.plan.gather 125 fresh i ≠ k
      by_cases hi : i = 125
      · subst i; simpa only [Function.update_self] using hkfresh.symm
      · simp only [Function.update_of_ne hi]
        intro heq; exact hk (heq ▸ CachedReplicaPassPlacement.Owns.gather i)
    have hsk : ∀ i, job.plan.solver i ≠ k := by
      intro i heq; exact hk (heq ▸ CachedReplicaPassPlacement.Owns.solver i)
    have hdk : job.output ≠ k := by intro heq; exact hk (heq ▸ CachedReplicaPassPlacement.Owns.output)
    have hframe := replicaRecoveryInterior_preserves plan (job.plan.solver 110) job.output k hR hQ
      hgk hsk (hsk 110) hdk he.toExec
    have hnot : k ∉ replicaInteriorReleasePorts job.plan := by
      intro hmem
      obtain ⟨i,_,heq⟩ := List.mem_map.mp hmem
      exact hk (heq ▸ CachedReplicaPassPlacement.Owns.solver (weightCacheCoreReg i))
    exact ⟨hframe.1,hframe.2.trans (ite_eq_right hnot)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
