module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedReplicaRecoveryCaller
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseReplicaCouplingCaller
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoverySharedBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingNativeStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryCallerSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareReplicaRecoveryCallerRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLoadReplicaRecoveryQueues
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryTransition
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCompleteReplicaRow

/-! Release coupling native arithmetic, initialize shared physical readiness,
and recover every residual with a uniform paid cleanup bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 389 Q A U}

noncomputable def releasedReplicaRecoveryCaller (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 389 Q A U :=
  .seq releaseReplicaCouplingCaller (initializedReplicaRecoveryCaller hR hQ)

def releasedReplicaRecoveryCallerCost (H : ReplicaHaloProblem s) (target W : ℕ) :=
  replicaCouplingNativeCleanupBound (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span)+
    initializedReplicaRecoveryCallerCost H target W

theorem releasedReplicaRecoveryCaller_exec (H : ReplicaHaloProblem s)
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
    ReplicaRecoveryRhsHeaders H replicaRecoveryCallerInterior.gather buffers G →
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
    (∀ i : Fin 255, 248 ≤ i.val → G.R (replicaRecoveryCallerWorkerReg i) = []) →
    ReplicaRecoverySharedBank H W (embStk (Fin.castLE (by decide : 248 ≤ 255)) S) →
    releaseReplicaCouplingNativeCost (embStk replicaRecoveryCallerNativeReg G) ≤
      replicaCouplingNativeCleanupBound (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span) →
    S.R 167 = [] →
    ∃ v' G' n, v'.user = v.user ∧ n ≤ releasedReplicaRecoveryCallerCost H target W ∧
      Exec body (releasedReplicaRecoveryCaller hR hQ) (Host.mk v G) n (Host.mk v' G') ∧
      G'.R 387 = [] ∧ G'.R 121 = G.R 121 ∧ G'.R 125 = [] ∧ G'.R 388 = [] ∧
      let F := embStk recoveryQueueWorkerReg (embStk replicaRecoveryCallerReg G')
      F.R 238 = C.R 238 ∧ F.R 93 = C.R 93 ∧
      RecoveredReplicaArchive H target X (C.R 125) F ∧
      ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 255)) F) ∧
      ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg F) ∧
      F.R 116 = [] ∧ F.R 167 = [] ∧ F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      F.R 110 = S.R 110 ∧ F.R 132 = S.R 132 ∧
      (∀ bo hf df, PackedBoundaryFactorPages bo hf df (embStk (Fin.castLE (by decide : 242 ≤ 255)) S) →
        PackedBoundaryFactorPages bo hf df (embStk (Fin.castLE (by decide : 242 ≤ 255)) F)) := by
  dsimp only
  intro htarget hcolumns htable X hX Ds hDs buffers v G headers hres hqueue hblank
    hleft hpages hpersistent hshared hcost h167
  obtain ⟨v₁,J,hu₁,he₁,hview,hgather,hL,hinpJ,houtJ,hhigh,h93J,h110J,hoff⟩ :=
    releaseReplicaCouplingCaller_exec (body := body) v G
  have hcoreJ : ReplicaRecoveryCoreReady H W (embStk replicaRecoveryCallerNativeReg J) := by
    rw [hview]
    exact hshared.released H W _
  have hgatherR (i : Fin 126) : J.R (replicaRecoveryCallerInterior.gather i) =
      G.R (replicaRecoveryCallerInterior.gather i) := congrArg (fun S : Stacks 126 A => S.R i) hgather
  have hheadersJ := ReplicaRecoveryRhsHeaders.of_frame H replicaRecoveryCallerInterior.gather buffers G J headers hgatherR
  have hprivate (k : Fin 259) (hk : 248 ≤ k.val) : J.R (replicaRecoveryCallerReg k) = G.R (replicaRecoveryCallerReg k) := by
    apply hoff
    intro i hi
    have hh := congrArg (fun k : Fin 259 => k.val) (replicaRecoveryCallerReg_injective hi)
    change i.val = k.val at hh
    have hb := i.isLt
    omega
  have hworkerL : (embStk replicaRecoveryCallerWorkerReg J).L = (embStk replicaRecoveryCallerWorkerReg G).L :=
    congrArg (fun L => L ∘ replicaRecoveryCallerWorkerReg) hL
  have hpagesJ (bo hf df : List (Fin (A+4)))
      (h : PackedBoundaryFactorPages bo hf df (embStk (Fin.castLE (by decide : 242 ≤ 255)) (embStk replicaRecoveryCallerWorkerReg G))) :
      PackedBoundaryFactorPages bo hf df
        (embStk (Fin.castLE (by decide : 242 ≤ 255)) (embStk replicaRecoveryCallerWorkerReg J)) := by
    apply h.of_solution_frame
    intro k hk h238
    exact hhigh (Fin.castLE (by decide) k) (by change 117 ≤ k.val; omega)
  have h116J : (embStk replicaRecoveryCallerWorkerReg J).R 116 = [] := by
    have hh := congrArg (fun S : Stacks 248 A => S.R 116) hview
    exact hh.trans (releasedReplicaCouplingNative_blank _ 116 (by decide) (by decide))
  obtain ⟨v',F,n,hu,hn,he,h387,h121,h125,h388,h238,h93,houtput,hcoreF,hphysicalF,h116F,h167F,
    hLF,hinp,hout,h110,h132,hfactor⟩ := initializedReplicaRecoveryCaller_exec (body := body)
      H hR hQ hA hp hwidth hsep hpad target W columns htarget hcolumns htable X hX Ds hDs buffers v₁ J
      hheadersJ ((hgatherR 125).trans hres)
      ((hprivate 258 (by decide)).trans hqueue) ((hprivate 255 (by decide)).trans hblank)
      (by
        change ∀ i : Fin 242, (embStk replicaRecoveryCallerWorkerReg J).L (Fin.castLE (by decide) i) =
          (embStk replicaRecoveryCallerWorkerReg J).L (replicaBoundaryPhaseReg i)
        rw [hworkerL]; exact hleft)
      (hpagesJ _ _ _ hpages) (by intro i hi; exact (hhigh i (by omega)).trans (hpersistent i hi)) hcoreJ h116J
      ((hhigh 167 (by decide)).trans h167)
  refine ⟨v',F,releaseReplicaCouplingNativeCost (embStk replicaRecoveryCallerNativeReg G)+n,
    hu.trans hu₁,by unfold releasedReplicaRecoveryCallerCost; omega,Exec.seq he₁ he,
    h387,h121.trans (hgatherR 121),h125,h388,
    h238.trans (hhigh 238 (by decide)),h93.trans h93J,?_,hcoreF,hphysicalF,h116F,h167F,
    hLF.trans hworkerL,hinp.trans hinpJ,hout.trans houtJ,h110.trans h110J,
    h132.trans (hhigh 132 (by decide)),?_⟩
  · have hh : (embStk replicaRecoveryCallerReg J).R 125 = (embStk replicaRecoveryCallerReg G).R 125 := hhigh 125 (by decide)
    rw [hh] at houtput
    exact houtput
  · intro bo hf df hpagesG
    apply hfactor bo hf df
    apply hpagesG.of_solution_frame
    intro k hk h238
    exact hhigh (Fin.castLE (by decide) k) (by change 117 ≤ k.val; omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
