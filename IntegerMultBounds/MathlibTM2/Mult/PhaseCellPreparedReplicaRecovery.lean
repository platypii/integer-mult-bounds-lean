module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedReplicaRecoveryReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryCoreFrame

/-! Physical preparation and the actual recovery kernel compose in the retained
machine. Persistent boundary data stays outside the recovery image. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 255 Q A U}

noncomputable def preparedReplicaRecovery (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 255 Q A U :=
  .seq prepareReplicaRecoveryInputs
    (embProg (Fin.castLE (by decide : 248 ≤ 255)) Empty.elim (packedBoundaryRecovery (P := Empty) hR hQ))

def replicaRecoveryRowCost (H : ReplicaHaloProblem s) (target : ℕ) := replicaRecoveryInputsCost H+
  packedBoundaryRecoveryCost H.p H.u H.l target H.rhsExp s H.t H.origin (H.origin+H.span) H.metadataWidth H.precision H.wordWidth

theorem preparedReplicaRecovery_exec (H : ReplicaHaloProblem s)
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
    ∃ v' F n, ∃ E : ZMod s → GaussianInt, v'.user = v.user ∧ n ≤ replicaRecoveryRowCost H target ∧
      Exec body (preparedReplicaRecovery hR hQ) (mk v S) n (mk v' F) ∧
      F.R 93 = rhsQueueTail ∧ F.R 238 = solutionTail ∧
      F.R 132 = cstream A H.wordWidth (packedInterval H.origin H.span E)++S.R 132 ∧
      (∀ i, Fits H.wordWidth (E i)) ∧
      PhaseCellInterface.ErrorOn (haloVertices s H.origin (H.origin+H.span))
        (fun i => (packedIntervalRead H.precision H.wordWidth H.origin (F.R 132) i).re) x (1/(2 : ℝ)^target) ∧
      (∃ residual : List (Fin (A+4)), residual.length = H.span*H.wordWidth ∧
        F.R 110 = residual++(cstream A H.wordWidth (packedInterval H.origin H.span (H.Fs.reverse.getD r (fun _ => 0)))++S.R 110)) ∧
      ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 255)) F) ∧
      F.R 116 = [] ∧ F.R 167 = [] ∧ F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k : Fin 255, 248 ≤ k.val → F.L k = S.L k ∧ F.R k = S.R k) ∧
      (∀ bo hf df, PackedBoundaryFactorPages bo hf df (embStk (Fin.castLE (by decide : 242 ≤ 255)) S) →
        PackedBoundaryFactorPages bo hf df (embStk (Fin.castLE (by decide : 242 ≤ 255)) F)) := by
  dsimp only
  intro htarget hcolumns htable r hr D hD x hx rhsQueueTail solutionTail v S
    hphysical hcore h116 h167 hsource hsolution
  let xs := cstream A H.wordWidth (packedInterval H.origin H.span (H.Fs.reverse.getD r (fun _ => 0)))
  let J := preparedReplicaRecoveryInputState S xs rhsQueueTail
  let e : Fin 248 → Fin 255 := Fin.castLE (by decide)
  have hinj : Function.Injective e := by intro i j he; exact Fin.ext (congrArg (fun k : Fin 255 => k.val) he)
  have hlen : xs.length = H.span*H.wordWidth := by
    have hfit := H.span_fit
    simp [xs,packedInterval]
    omega
  obtain ⟨v₀,hu₀,he₀,hentry⟩ := prepareReplicaRecoveryReady_exec (body := body) H W
    (H.Fs.reverse.getD r (fun _ => 0)) rhsQueueTail v S hphysical hcore hsource h116 h167
  obtain ⟨vi,T,n,E,hu,hn,he,h93,h139,h238,hinp,hout,h132,hfits,herror,hresidual,hnative,hL,hretained,
    hwork,hready,hfresh,hfactor,hpages,h127,h143,h158,h167F,hclean,h126⟩ :=
    ReplicaCouplingResidualSpec.recovery_exec (body := fun z : Empty => nomatch z) H hR hQ hA hp hwidth hsep hpad
      target W columns htarget hcolumns htable r hr D hD x hx solutionTail
      (List.replicate (H.span*H.wordWidth) Node.tick) (S.R 132)
      (List.replicate (H.span*H.wordWidth) Node.tick) (S.R 110) (by simp) (by simp)
      (embDn e v₀) (embStk e J) hentry
      (by change J.R 238 = _; rw [preparedReplicaRecoveryInputState_frame S xs rhsQueueTail 238 (by decide)]; exact hsolution)
      (by change J.R 132 = _; simp [J,preparedReplicaRecoveryInputState,seededReplicaRecoveryState,stagedReplicaRecoveryRhsState,hlen])
      (by change J.R 110 = _; simp [J,preparedReplicaRecoveryInputState,seededReplicaRecoveryState,stagedReplicaRecoveryRhsState,hlen]; rfl)
  have hcoreT : ReplicaRecoveryCoreReady H W T := by
    apply ReplicaRecoveryCoreReady.of_recovery_frame H W hentry.toReplicaRecoveryCoreReady
      ⟨hready,hwork⟩ h143 h139 hnative hretained hfresh
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact h127 | exact h158 | exact hclean _ (by decide)
  obtain ⟨v',hv,hu',he'⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim) hinj
    (fun z => nomatch z) he v₀ rfl J rfl
  let G := embOvr e T.get J
  have hget (i : Fin 248) : G.R (e i) = T.R i := by
    have hh := embOvr_get hinj T.get J (.rt i)
    change G.R (e i) = (T.R i).map id at hh
    simpa only [List.map_id] using hh
  have hread93 : G.R 93 = T.R 93 := hget 93
  have hread132 : G.R 132 = T.R 132 := hget 132
  refine ⟨v',G,replicaRecoveryInputsCost H+n,E,hu'.trans (hu.trans hu₀),by unfold replicaRecoveryRowCost; omega,
    Exec.seq he₀ he',?_,?_,?_,hfits,?_,?_,?_,?_,?_,?_,hinp,hout,?_,?_⟩
  · rw [hread93,h93]; simp [embStk,e,J,preparedReplicaRecoveryInputState,seededReplicaRecoveryState,stagedReplicaRecoveryRhsState]
  · exact (hget 238).trans h238
  · exact (hget 132).trans h132
  · rw [hread132]; exact herror
  · obtain ⟨residual,hlen,hrhs⟩ := hresidual
    exact ⟨residual,hlen,(hget 110).trans hrhs⟩
  · rw [embStk_ovr hinj]; exact hcoreT
  · exact (hget 116).trans (hnative 116 (by decide) (by decide))
  · exact (hget 167).trans h167F
  · exact embOvr_left_of_eq J T hL
  · intro k hk
    have hoff : ∀ i, e i ≠ k := by
      intro i heq
      have hv := congrArg Fin.val heq
      have hi := i.isLt
      change i.val = k.val at hv
      omega
    have hh := embOvr_off T.get J hoff
    refine ⟨hh.1,hh.2.trans ?_⟩
    apply preparedReplicaRecoveryInputState_frame
    simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff]
    norm_num
    omega
  · intro bo hf df hpage
    change PackedBoundaryFactorPages bo hf df (embStk packedBoundaryRecoveryBase (embStk e G))
    rw [embStk_ovr hinj]
    exact hpages bo hf df (factorPages_prepare_recovery_inputs S xs rhsQueueTail hpage)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
