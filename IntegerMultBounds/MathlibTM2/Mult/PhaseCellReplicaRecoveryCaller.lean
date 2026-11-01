module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLoadedReplicaRecoveryLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareReplicaRecoveryCallerRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLoadReplicaRecoveryQueues
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryTransition
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCompleteReplicaRow

/-! Prepare the owned RHS from the retained gather source and recover the actual
coupling archive through the common caller placement in one paid trace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 389 Q A U}

noncomputable def replicaRecoveryCaller (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 389 Q A U :=
  .seq prepareReplicaRecoveryCallerRhs
    (embProg replicaRecoveryCallerReg Empty.elim (loadedReplicaRecoveryLoop (P := Empty) hR hQ))

def replicaRecoveryCallerCost (H : ReplicaHaloProblem s) (target W : ℕ) :=
  copyRowsOrderedCost H.Fs.length (H.span*H.wordWidth)+loadedReplicaRecoveryLoopCost H target W

theorem replicaRecoveryCaller_exec (H : ReplicaHaloProblem s)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (hsep : H.span+H.band ≤ s)
    (hpad : 2*((s/(H.t-s)+1)-2*H.band) ≤ 2^H.l+1)
    (target W : ℕ) (columns : List (ZMod s → GaussianInt)) :
    let I := haloInterior s H.t H.band H.origin (H.origin+H.span)
    let B := haloBoundary s H.t H.band H.origin (H.origin+H.span)
    let bits := boundaryTableBits H.p (boundaryRecoveryTarget H.p target) H.rhsExp B.card
    H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp B.card →
    PreparedBoundaryColumns A H.p bits H.precision H.wordWidth W B columns →
    (∀ i ∈ B, ∀ j ∈ B, |bandBoundaryTable B W (computedBoundaryTable A H.precision H.wordWidth B columns) i j-
      (SchurDominance.run (realMatrix s H.t H.p H.u) (haloVertices s H.origin (H.origin+H.span)) I.toList).1 i j| ≤ 1/(2 : ℝ)^bits) →
    ∀ (X : ℕ → ZMod s → ℝ),
    (∀ r < H.Fs.length, Solves (realMatrix s H.t H.p H.u) (haloVertices s H.origin (H.origin+H.span)) (X r)
      (fun i => (value H.precision (H.Fs.reverse.getD (H.Fs.length-1-r) (fun _ => 0) i)).re)) →
    ∀ (Ds : List (ZMod s → GaussianInt)), ReplicaRecoveryResidualRows H Ds →
    ∀ (buffers : ReplicaLoopBuffers A) (v : HS 389 Q A U) (G : Stacks 389 A),
    ReplicaLoopHeaders H replicaRecoveryCallerInterior.gather buffers G →
    G.R 125 = Ds.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D)) →
    G.R 388 = [] → G.R 387 = [] →
    let C := embStk replicaRecoveryCallerReg G
    let S := embStk recoveryQueueWorkerReg C
    (∀ i : Fin 242, S.L (Fin.castLE (by decide) i) = S.L (replicaBoundaryPhaseReg i)) →
    PackedBoundaryFactorPages
      (cstream A H.wordWidth ((naturalLineLc H.precision (factorNewtonSteps H.p H.precision) W B.card
        (factorRankIntegerMatrix B W columns)).map colC).flatten)
      (cstream A H.wordWidth ((naturalLineUc H.precision (factorNewtonSteps H.p H.precision) W B.card
        (factorRankIntegerMatrix B W columns)).map colC).flatten)
      (cstream A H.wordWidth ((naturalLineRcs H.precision (factorNewtonSteps H.p H.precision) W B.card
        (factorRankIntegerMatrix B W columns)).map fun z => (⟨z,0⟩ : GaussianInt)))
      (embStk (Fin.castLE (by decide : 242 ≤ 255)) S) →
    ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg S) →
    ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 255)) S) →
    S.R 116 = [] → S.R 167 = [] →
    ∃ v' G' n, v'.user = v.user ∧ n ≤ replicaRecoveryCallerCost H target W ∧
      Exec body (replicaRecoveryCaller hR hQ) (Host.mk v G) n (Host.mk v' G') ∧
      G'.R 387 = [] ∧ G'.R 121 = G.R 121 ∧ G'.R 125 = [] ∧ G'.R 388 = [] ∧
      let F := embStk recoveryQueueWorkerReg (embStk replicaRecoveryCallerReg G')
      F.R 238 = C.R 238 ∧ F.R 93 = C.R 93 ∧
      RecoveredReplicaArchive H target X (C.R 125) F ∧
      ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 255)) F) ∧
      ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg F) ∧
      F.R 116 = [] ∧ F.R 167 = [] ∧ F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      F.R 110 = S.R 110 ∧ F.R 132 = S.R 132 ∧
      (∀ k : Fin 255, 248 ≤ k.val → F.R k = S.R k) ∧
      (∀ bo hf df, PackedBoundaryFactorPages bo hf df (embStk (Fin.castLE (by decide : 242 ≤ 255)) S) →
        PackedBoundaryFactorPages bo hf df (embStk (Fin.castLE (by decide : 242 ≤ 255)) F)) := by
  dsimp only
  intro htarget hcolumns htable X hX Ds hDs buffers v G headers hres hqueue hblank
    hleft hpages hphysical hcore h116 h167
  let words := H.Fs.flatMap (fun R => cstream A H.wordWidth (packedInterval H.origin H.span R))
  let J : Stacks 389 A := {G with R := Function.update G.R 388 words}
  obtain ⟨v₁,m,hu₁,hm,he₁⟩ := prepareReplicaRecoveryCallerRhs_exec (body := body) H buffers v G headers hblank hqueue
  have hworker : embStk recoveryQueueWorkerReg (embStk replicaRecoveryCallerReg J) =
      embStk recoveryQueueWorkerReg (embStk replicaRecoveryCallerReg G) :=
    prepareReplicaRecoveryCallerRhs_worker_frame G words
  have hread (k : Fin 259) (hk : k ≠ 258) :
      (embStk replicaRecoveryCallerReg J).R k = (embStk replicaRecoveryCallerReg G).R k := by
    change Function.update G.R 388 words (replicaRecoveryCallerReg k) = _
    apply Function.update_of_ne
    intro heq
    apply hk
    apply replicaRecoveryCallerReg_injective
    simpa only [replicaRecoveryCallerReg_rhs] using heq
  have hmaster : ((embStk replicaRecoveryCallerReg J).R 256).length = H.Fs.length := by
    rw [hread 256 (by decide)]
    change (G.R (replicaRecoveryCallerReg 256)).length = _
    rw [replicaRecoveryCallerReg_master]
    have hh := headers.masters (121,113) (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide)
    simpa [replicaRecoveryCallerInterior_gather,replicaFactoryHeaderValue] using hh
  obtain ⟨vi,F,n,hu,hn,he,h255,h256,h257,h258,hresF,hrhsF,houtput,hcoreF,hphysicalF,h116F,h167F,hL,hinp,hout,
    h110,h132,hpersistent,hfactor⟩ := loadedReplicaRecoveryLoop_exec (body := fun z : Empty => nomatch z)
      H hR hQ hA hp hwidth hsep hpad target W columns htarget hcolumns htable X hX Ds hDs
      (embDn replicaRecoveryCallerReg v₁) (embStk replicaRecoveryCallerReg J)
      (by rw [hread 257 (by decide)]; change G.R (replicaRecoveryCallerReg 257) = _; simpa using hres)
      (by change J.R (replicaRecoveryCallerReg 258) = _; simp [J,words])
      (by rw [hread 255 (by decide)]; change G.R (replicaRecoveryCallerReg 255) = _; simpa using hblank)
      hmaster (by rw [hworker]; exact hleft) (by rw [hworker]; exact hpages)
      (by rw [hworker]; exact hphysical) (by rw [hworker]; exact hcore)
      (by rw [hworker]; exact h116) (by rw [hworker]; exact h167)
  obtain ⟨v',hv,hu',he'⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    replicaRecoveryCallerReg_injective (fun z => nomatch z) he v₁ rfl J rfl
  let G' := embOvr replicaRecoveryCallerReg F.get J
  have hview : embStk replicaRecoveryCallerReg G' = F := embStk_ovr replicaRecoveryCallerReg_injective F J
  have hget (k : Fin 259) : G'.R (replicaRecoveryCallerReg k) = F.R k :=
    congrArg (fun S : Stacks 259 A => S.R k) hview
  have h387 : G'.R 387 = [] := (hget 255).trans h255
  have h121 : G'.R 121 = G.R 121 := (hget 256).trans (h256.trans (hread 256 (by decide)))
  have h125 : G'.R 125 = [] := (hget 257).trans h257
  have h388 : G'.R 388 = [] := (hget 258).trans h258
  refine ⟨v',G',m+n,hu'.trans (hu.trans hu₁),by unfold replicaRecoveryCallerCost; omega,
    Exec.seq he₁ he',h387,h121,h125,h388,?_⟩
  rw [hview]
  rw [hworker] at hL hinp hout h110 h132 hpersistent hfactor
  refine ⟨hresF.trans (hread 238 (by decide)),hrhsF.trans (hread 93 (by decide)),?_,hcoreF,hphysicalF,
    h116F,h167F,hL,hinp,hout,h110,h132,hpersistent,hfactor⟩
  simpa only [hread 125 (by decide)] using houtput

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
