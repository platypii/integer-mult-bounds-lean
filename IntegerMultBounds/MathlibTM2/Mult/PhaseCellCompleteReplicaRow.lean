module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedReplicaBoundaryRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinishedReplicaRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireReplicaRecoveryRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryOwnedFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryBoundaryFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedIntervalSuffix

/-! Solve an actual archived residual, recover the full halo, and archive the result.
Shared factors and readiness survive for the next replica. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 255 Q A U}

noncomputable def completeReplicaRow (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 255 Q A U :=
  .seq (retainedReplicaBoundaryRow hQ) (finishedReplicaRecovery hR hQ)

def completeReplicaRowCost (H : ReplicaHaloProblem s) (target W : ℕ) :=
  replicaBoundaryRhsCost H + preparedResidualSolveCost H.precision H.wordWidth
    (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card W + finishedReplicaRecoveryCost H target

theorem completeReplicaRow_exec (H : ReplicaHaloProblem s)
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
    ∀ r < H.Fs.length, ∀ D, ReplicaCouplingResidualSpec H r D →
    ∀ x, Solves (realMatrix s H.t H.p H.u) (haloVertices s H.origin (H.origin+H.span)) x
      (fun i => (value H.precision (H.Fs.reverse.getD r (fun _ => 0) i)).re) →
    ∀ (rhsQueueTail solutionTail : List (Fin (A+4))) (v : HS 255 Q A U) (S : Stacks 255 A),
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
    S.R 93 = cstream A H.wordWidth (packedInterval H.origin H.span (H.Fs.reverse.getD r (fun _ => 0)))++rhsQueueTail →
    S.R 238 = cstream A H.wordWidth (packedInterval H.origin H.span D)++solutionTail →
    ∃ v' F n, ∃ E : ZMod s → GaussianInt, v'.user = v.user ∧ n ≤ completeReplicaRowCost H target W ∧
      Exec body (completeReplicaRow hR hQ) (mk v S) n (mk v' F) ∧
      F.R 93 = rhsQueueTail ∧ F.R 238 = solutionTail ∧ F.R 110 = S.R 110 ∧ F.R 132 = S.R 132 ∧
      F.R 125 = cstream A H.wordWidth (packedInterval H.origin H.span E)++S.R 125 ∧
      (∀ i, Fits H.wordWidth (E i)) ∧
      PhaseCellInterface.ErrorOn (haloVertices s H.origin (H.origin+H.span))
        (fun i => (packedIntervalRead H.precision H.wordWidth H.origin (F.R 125) i).re) x (1/(2 : ℝ)^target) ∧
      ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 255)) F) ∧
      ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg F) ∧
      F.R 116 = [] ∧ F.R 167 = [] ∧ F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k : Fin 255, 248 ≤ k.val → F.L k = S.L k ∧ F.R k = S.R k) ∧
      (∀ bo hf df, PackedBoundaryFactorPages bo hf df (embStk (Fin.castLE (by decide : 242 ≤ 255)) S) →
        PackedBoundaryFactorPages bo hf df (embStk (Fin.castLE (by decide : 242 ≤ 255)) F)) := by
  dsimp only
  intro htarget hcolumns htable r hr D hD x hx rhsQueueTail solutionTail v S
    hleft hpages hphysical hcore h116 h167 hsource hresidual
  let words := cstream A H.wordWidth (replicaBoundarySolution H W columns D)++solutionTail
  let J := retainedReplicaBoundaryState S words
  obtain ⟨v₁,m,hu₁,hm,he₁,hcoreJ,hpagesJ,hphysicalJ⟩ := retainedReplicaBoundaryRow_exec
    (body := body) H hQ hA hp hwidth (boundaryRecoveryTarget H.p target) W columns
      htarget hcolumns r hr D hD v S solutionTail hleft hphysical hresidual hcore hpages
  have hframe (k : Fin 255) (hk : k ∉ [143,238]) : J.R k = S.R k :=
    retainedReplicaBoundaryState_frame S words k hk
  obtain ⟨v₂,F,n,E,hu₂,hn,he₂,h93,h238,h110,h132,h125,hfits,herror,hcoreF,hphysicalF,
    h116F,h167F,hL,hinp,hout,hpersistent,hfactor⟩ := finishedReplicaRecovery_exec
      (body := body) H hR hQ hA hp hwidth hsep hpad target W columns htarget hcolumns htable
      r hr D hD x hx rhsQueueTail solutionTail v₁ J hphysicalJ hcoreJ
      ((hframe 116 (by decide)).trans h116) ((hframe 167 (by decide)).trans h167)
      ((hframe 93 (by decide)).trans hsource)
      (by simp [J,retainedReplicaBoundaryState,words])
  refine ⟨v₂,F,m+n,E,hu₂.trans hu₁,by unfold completeReplicaRowCost; omega,
    Exec.seq he₁ he₂,h93,h238,h110.trans (hframe 110 (by decide)),
    h132.trans (hframe 132 (by decide)),?_,hfits,herror,hcoreF,hphysicalF,
    h116F,h167F,hL,hinp,hout,?_,?_⟩
  · exact h125.trans (congrArg (fun tail => cstream A H.wordWidth (packedInterval H.origin H.span E)++tail)
      (hframe 125 (by decide)))
  · intro k hk
    exact ⟨(hpersistent k hk).1,(hpersistent k hk).2.trans (hframe k (by
      simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff]
      norm_num
      omega))⟩
  · intro bo hf df hpagesS
    apply hfactor bo hf df
    apply hpagesS.of_solution_frame
    intro k hk h238
    apply hframe
    simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,Fin.castLE] at h238 ⊢
    norm_num at h238 ⊢
    omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
