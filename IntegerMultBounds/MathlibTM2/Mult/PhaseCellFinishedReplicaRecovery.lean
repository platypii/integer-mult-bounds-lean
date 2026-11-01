module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedReplicaRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireReplicaRecoveryRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryOwnedFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryBoundaryFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedIntervalSuffix

/-! Recover, archive and retire one replica row in a single physical trace.
The archived prefix keeps the error bound and both shared readiness contracts. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 255 Q A U}

noncomputable def finishedReplicaRecovery (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 255 Q A U :=
  .seq (preparedReplicaRecovery hR hQ) retireReplicaRecoveryRow

def finishedReplicaRecoveryCost (H : ReplicaHaloProblem s) (target : ℕ) :=
  replicaRecoveryRowCost H target+18*(H.span*H.wordWidth)+18

theorem finishedReplicaRecovery_exec (H : ReplicaHaloProblem s)
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
    ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg S) →
    ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 255)) S) →
    S.R 116 = [] → S.R 167 = [] →
    S.R 93 = cstream A H.wordWidth (packedInterval H.origin H.span (H.Fs.reverse.getD r (fun _ => 0)))++rhsQueueTail →
    S.R 238 = cstream A H.wordWidth (replicaBoundarySolution H W columns D)++solutionTail →
    ∃ v' F n, ∃ E : ZMod s → GaussianInt, v'.user = v.user ∧ n ≤ finishedReplicaRecoveryCost H target ∧
      Exec body (finishedReplicaRecovery hR hQ) (mk v S) n (mk v' F) ∧
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
    hphysical hcore h116 h167 hsource hsolution
  obtain ⟨v₁,J,m,E,hu,hm,he,h93,h238,h132,hfits,herror,hresidual,hcoreJ,h116J,h167J,hL,hinp,hout,
    hpersistent,hpages,h125⟩ := preparedReplicaRecovery_exec (body := body) H hR hQ hA hp hwidth hsep hpad
      target W columns htarget hcolumns htable r hr D hD x hx rhsQueueTail solutionTail v S
      hphysical hcore h116 h167 hsource hsolution
  obtain ⟨residual,hlenResidual,hrhs⟩ := hresidual
  let rhs := cstream A H.wordWidth (packedInterval H.origin H.span (H.Fs.reverse.getD r (fun _ => 0)))
  let words := cstream A H.wordWidth (packedInterval H.origin H.span E)
  have hlenRhs : rhs.length = H.span*H.wordWidth := by simp only [rhs,length_cstream,packedInterval_length _ H.span_fit]
  have hlenWords : words.length = H.span*H.wordWidth := by simp only [words,length_cstream,packedInterval_length _ H.span_fit]
  have hvolume : (J.R 251).length = H.span*H.wordWidth := by
    rw [(hpersistent 251 (by decide)).2]
    have hh := hphysical.volume
    change (S.R (replicaBoundaryPhaseReg 123)).length = _ at hh
    simpa only [replicaBoundaryPhaseReg_volume] using hh
  obtain ⟨v₂,hu₂,he₂⟩ := retireReplicaRecoveryRow_exec (body := body) (H.span*H.wordWidth)
    residual rhs words (S.R 110) (S.R 132) hlenResidual hlenRhs hlenWords v₁ J hvolume hrhs h132
    (hcoreJ.native 104 (by decide) (by decide) (by decide)) (hcoreJ.native 105 (by decide) (by decide) (by decide))
  let F := retiredReplicaRecoveryState J (S.R 110) (S.R 132) words
  have hcoreF : ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 255)) F) := by
    apply ReplicaRecoveryCoreReady.of_owned_frame H W hcoreJ
      (F := embStk (Fin.castLE (by decide : 248 ≤ 255)) F) rfl
    intro k hk
    apply retiredReplicaRecoveryState_frame
    simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,Fin.castLE] at hk ⊢
    norm_num at hk ⊢
    tauto
  have hextra (k : Fin 255) (hk : 248 ≤ k.val) : F.L k = S.L k ∧ F.R k = S.R k := by
    refine ⟨(hpersistent k hk).1,?_⟩
    apply (retiredReplicaRecoveryState_frame J _ _ words k ?_).trans (hpersistent k hk).2
    simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff]
    norm_num
    omega
  have harchive : F.R 125 = words++S.R 125 := by simp [F,retiredReplicaRecoveryState,h125]
  refine ⟨v₂,F,m+(18*(H.span*H.wordWidth)+18),E,hu₂.trans hu,by unfold finishedReplicaRecoveryCost; omega,
    Exec.seq he he₂,?_,?_,?_,?_,harchive,hfits,?_,hcoreF,
    ReplicaBoundaryRhsReady.of_recovery_core H W hphysical hcoreF (fun k hk => (hextra k hk).2),
    ?_,?_,hL,hinp,hout,hextra,?_⟩
  · exact (retiredReplicaRecoveryState_frame J _ _ words 93 (by decide)).trans h93
  · exact (retiredReplicaRecoveryState_frame J _ _ words 238 (by decide)).trans h238
  · simp [F,retiredReplicaRecoveryState]
  · simp [F,retiredReplicaRecoveryState]
  · intro i hi
    obtain ⟨ha,hb⟩ := (mem_haloVertices _ _ _).mp hi
    have hread : packedIntervalRead H.precision H.wordWidth H.origin (words++S.R 125) i =
        packedIntervalRead H.precision H.wordWidth H.origin
          (cstream A H.wordWidth (packedInterval H.origin H.span E)++S.R 132) i :=
      packedIntervalRead_suffix _ _ _ _ E _ _ H.span_fit i ha hb
    change ‖(packedIntervalRead H.precision H.wordWidth H.origin (F.R 125) i).re-x i‖ ≤ 1/(2 : ℝ)^target
    rw [harchive,hread]
    have hi' := herror i hi
    rw [h132] at hi'
    exact hi'
  · exact (retiredReplicaRecoveryState_frame J _ _ words 116 (by decide)).trans h116J
  · exact (retiredReplicaRecoveryState_frame J _ _ words 167 (by decide)).trans h167J
  · intro bo hf df hpage
    apply (hpages bo hf df hpage).of_solution_frame
    intro k hk _
    apply retiredReplicaRecoveryState_frame
    simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,Fin.castLE]
    norm_num
    omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
