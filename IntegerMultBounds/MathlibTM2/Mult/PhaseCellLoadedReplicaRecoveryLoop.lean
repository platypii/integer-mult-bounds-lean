module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedReplicaRecoveryLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLoadReplicaRecoveryQueues
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryTransition
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCompleteReplicaRow

/-! Load actual owned queues, initialize the controller, and execute every
complete recovery row in one trace. Both borrowed queue suffixes restore. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 259 Q A U}

def loadedReplicaRecoveryLoopReg : Fin 257 → Fin 259 := Fin.castLE (by decide)

noncomputable def loadedReplicaRecoveryLoop (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 259 Q A U :=
  .seq loadReplicaRecoveryQueues
    (embProg loadedReplicaRecoveryLoopReg Empty.elim (initializedReplicaRecoveryLoop (P := Empty) hR hQ))

def loadedReplicaRecoveryLoopCost (H : ReplicaHaloProblem s) (target W : ℕ) :=
  (8*(H.Fs.length*(H.span*H.wordWidth))+8)+
    ((4*H.Fs.length+4)+H.Fs.length*(completeReplicaRowCost H target W+3)+2)

def ReplicaRecoveryResidualRows (H : ReplicaHaloProblem s) (Ds : List (ZMod s → GaussianInt)) : Prop :=
  Ds.length = H.Fs.length ∧
    ∀ j : Fin Ds.length, ReplicaCouplingResidualSpec H (H.Fs.length-1-j.val) Ds[j.val]

theorem loadedReplicaRecoveryLoop_exec (H : ReplicaHaloProblem s)
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
    ∀ (v : HS 259 Q A U) (G : Stacks 259 A),
    G.R 257 = Ds.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D)) →
    G.R 258 = H.Fs.flatMap (fun R => cstream A H.wordWidth (packedInterval H.origin H.span R)) →
    let S := embStk recoveryQueueWorkerReg G
    G.R 255 = [] → (G.R 256).length = H.Fs.length →
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
    ∃ v' G' n, v'.user = v.user ∧ n ≤ loadedReplicaRecoveryLoopCost H target W ∧
      Exec body (loadedReplicaRecoveryLoop hR hQ) (Host.mk v G) n (Host.mk v' G') ∧
      G'.R 255 = [] ∧ G'.R 256 = G.R 256 ∧ G'.R 257 = [] ∧ G'.R 258 = [] ∧
      let F := embStk recoveryQueueWorkerReg G'
      F.R 238 = G.R 238 ∧ F.R 93 = G.R 93 ∧
      RecoveredReplicaArchive H target X (G.R 125) F ∧
      ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 255)) F) ∧
      ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg F) ∧
      F.R 116 = [] ∧ F.R 167 = [] ∧ F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      F.R 110 = S.R 110 ∧ F.R 132 = S.R 132 ∧
      (∀ k : Fin 255, 248 ≤ k.val → F.R k = S.R k) ∧
      (∀ bo hf df, PackedBoundaryFactorPages bo hf df (embStk (Fin.castLE (by decide : 242 ≤ 255)) S) →
        PackedBoundaryFactorPages bo hf df (embStk (Fin.castLE (by decide : 242 ≤ 255)) F)) := by
  dsimp only
  intro htarget hcolumns htable X hX Ds hDs v G hres hrhs
    hblank hmaster hleft hpages hphysical hcore h116 h167
  obtain ⟨hlen,hgood⟩ := hDs
  obtain ⟨v₁,hu₁,he₁,h257,h258,hcursor,hcoreJ,hphysicalJ,hpagesJ⟩ :=
    loadReplicaRecoveryQueues_exec (body := body) H W
      (RecoveredReplicaRowSpec (A := A) H target X) Ds hlen hgood v G hres hrhs hcore hphysical
  let J := loadedReplicaRecoveryQueues G
  have hframe (k : Fin 259) (hk : k ∉ [257,238,258,93]) : J.R k = G.R k :=
    loadedReplicaRecoveryQueues_frame G k hk
  have hworker : embStk initializedReplicaRecoveryWorkerReg (embStk loadedReplicaRecoveryLoopReg J) =
      embStk recoveryQueueWorkerReg J := rfl
  obtain ⟨vi,F,n,hu,hn,he,h255,h256,hresF,hrhsF,houtput,hcoreF,hphysicalF,h116F,h167F,hL,hinp,hout,
    h110,h132,hpersistent,hfactor⟩ := initializedReplicaRecoveryLoop_exec (body := fun z : Empty => nomatch z)
      H hR hQ hA hp hwidth hsep hpad target W columns htarget hcolumns htable X hX
      (G.R 238) (G.R 93) (G.R 125) (embDn loadedReplicaRecoveryLoopReg v₁)
      (embStk loadedReplicaRecoveryLoopReg J)
      ((hframe 255 (by decide)).trans hblank)
      (by change (J.R 256).length = _; rw [hframe 256 (by decide)]; exact hmaster)
      hcursor hleft (hpagesJ _ _ _ hpages) hphysicalJ hcoreJ
      ((hframe 116 (by decide)).trans h116) ((hframe 167 (by decide)).trans h167)
  have hinj : Function.Injective loadedReplicaRecoveryLoopReg := by
    intro i j hij
    exact Fin.ext (congrArg (fun k : Fin 259 => k.val) hij)
  obtain ⟨v',hv,hu',he'⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    hinj (fun z => nomatch z) he v₁ rfl J rfl
  let G' := embOvr loadedReplicaRecoveryLoopReg F.get J
  have hview : embStk recoveryQueueWorkerReg G' = embStk initializedReplicaRecoveryWorkerReg F := by
    change embStk initializedReplicaRecoveryWorkerReg (embStk loadedReplicaRecoveryLoopReg G') = _
    rw [embStk_ovr hinj]
  have hget (k : Fin 257) : G'.R (loadedReplicaRecoveryLoopReg k) = F.R k := by
    have hh := congrArg (fun S : Stacks 257 A => S.R k) (embStk_ovr hinj F J)
    exact hh
  have hoff (k : Fin 259) (hk : 257 ≤ k.val) : G'.R k = J.R k := by
    apply (embOvr_off F.get J ?_).2
    intro i hi
    have hv := congrArg (fun k : Fin 259 => k.val) hi
    change i.val = k.val at hv
    have hb := i.isLt
    omega
  have h255' : G'.R 255 = [] := (hget 255).trans h255
  have h256' : G'.R 256 = G.R 256 := (hget 256).trans (h256.trans (hframe 256 (by decide)))
  refine ⟨v',G',(8*(H.Fs.length*(H.span*H.wordWidth))+8)+n,hu'.trans (hu.trans hu₁),
    by unfold loadedReplicaRecoveryLoopCost; omega,Exec.seq he₁ he',h255',h256',
    (hoff 257 (by decide)).trans h257,(hoff 258 (by decide)).trans h258,?_⟩
  rw [hview]
  refine ⟨hresF,hrhsF,houtput,hcoreF,hphysicalF,h116F,h167F,hL,hinp,hout,?_,?_,?_,?_⟩
  · exact h110.trans (hframe 110 (by decide))
  · exact h132.trans (hframe 132 (by decide))
  · intro k hk
    exact (hpersistent k hk).trans (hframe ⟨k.val,by omega⟩ (by
      simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff]
      norm_num
      have hb := k.isLt
      omega))
  · intro bo hf df hpagesG
    exact hfactor bo hf df (hpagesJ bo hf df hpagesG)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
