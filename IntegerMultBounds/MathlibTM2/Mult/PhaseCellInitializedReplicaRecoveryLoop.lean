module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryTransition
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCompleteReplicaRow

/-! Copy the retained replica count once, execute the complete recovery loop,
and release its private controller while preserving the master. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 257 Q A U}

def initializedReplicaRecoveryLoopReg : Fin 256 → Fin 257 := Fin.castLE (by decide)
def initializedReplicaRecoveryWorkerReg : Fin 255 → Fin 257 := Fin.castLE (by decide)

noncomputable def initializedReplicaRecoveryLoop (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 257 Q A U :=
  .seq (Node.ucopy 256 255 104)
    (embProg initializedReplicaRecoveryLoopReg Empty.elim (replicaRecoveryLoop (P := Empty) hR hQ))

theorem initializedReplicaRecoveryLoop_exec (H : ReplicaHaloProblem s)
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
    ∀ (residualTail rhsTail outputTail : List (Fin (A+4))),
    ∀ (v : HS 257 Q A U) (G : Stacks 257 A),
    let S := embStk initializedReplicaRecoveryWorkerReg G
    G.R 255 = [] → (G.R 256).length = H.Fs.length →
    ReplicaRecoveryCursor H (RecoveredReplicaRowSpec (A := A) H target X) residualTail rhsTail outputTail 0 S →
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
    ∃ v' G' n, v'.user = v.user ∧ n ≤ (4*H.Fs.length+4)+H.Fs.length*(completeReplicaRowCost H target W+3)+2 ∧
      Exec body (initializedReplicaRecoveryLoop hR hQ) (Host.mk v G) n (Host.mk v' G') ∧
      G'.R 255 = [] ∧ G'.R 256 = G.R 256 ∧
      let F := embStk initializedReplicaRecoveryWorkerReg G'
      F.R 238 = residualTail ∧ F.R 93 = rhsTail ∧
      RecoveredReplicaArchive H target X outputTail F ∧
      ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 255)) F) ∧
      ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg F) ∧
      F.R 116 = [] ∧ F.R 167 = [] ∧ F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      F.R 110 = S.R 110 ∧ F.R 132 = S.R 132 ∧
      (∀ k : Fin 255, 248 ≤ k.val → F.R k = S.R k) ∧
      (∀ bo hf df, PackedBoundaryFactorPages bo hf df (embStk (Fin.castLE (by decide : 242 ≤ 255)) S) →
        PackedBoundaryFactorPages bo hf df (embStk (Fin.castLE (by decide : 242 ≤ 255)) F)) := by
  dsimp only
  intro htarget hcolumns htable X hX residualTail rhsTail outputTail v G
    hblank hmaster hcursor hleft hpages hphysical hcore h116 h167
  have h104 : G.R 104 = [] := hcore.native 104 (by decide) (by decide) (by decide)
  obtain ⟨v₁,hu₁,he₁⟩ := Node.ucopy_exec (body := body) (a := 256) (b := 255) (t := 104)
    (by decide) (by decide) (by decide) v G h104
  let J : Stacks 257 A := {G with R := Function.update G.R 255 (List.replicate H.Fs.length Node.tick)}
  have he₁' : Exec body (Node.ucopy 256 255 104) (Host.mk v G) (4*H.Fs.length+4) (Host.mk v₁ J) := by
    simpa [J,hmaster,hblank] using he₁
  have hworker : embStk replicaRecoveryWorkerReg (embStk initializedReplicaRecoveryLoopReg J) =
      embStk initializedReplicaRecoveryWorkerReg G := by
    change embStk initializedReplicaRecoveryWorkerReg J = _
    apply embStk_updateR_off
    intro i hi
    have hv := congrArg (fun k : Fin 257 => k.val) hi
    change i.val = 255 at hv
    have hb := i.isLt
    omega
  obtain ⟨vi,F,n,hu,hn,he,h255,hres,hrhs,houtput,hcoreF,hphysicalF,h116F,h167F,hL,hinp,hout,
    h110,h132,hpersistent,hfactor⟩ := replicaRecoveryLoop_exec (body := fun z : Empty => nomatch z)
      H hR hQ hA hp hwidth hsep hpad target W columns htarget hcolumns htable X hX
      residualTail rhsTail outputTail (embDn initializedReplicaRecoveryLoopReg v₁)
      (embStk initializedReplicaRecoveryLoopReg J) (by simp [J,embStk,initializedReplicaRecoveryLoopReg])
      (by rw [hworker]; exact hcursor) (by rw [hworker]; exact hleft)
      (by rw [hworker]; exact hpages) (by rw [hworker]; exact hphysical)
      (by rw [hworker]; exact hcore) (by rw [hworker]; exact h116) (by rw [hworker]; exact h167)
  have hinj : Function.Injective initializedReplicaRecoveryLoopReg := by
    intro i j hij
    exact Fin.ext (congrArg (fun k : Fin 257 => k.val) hij)
  obtain ⟨v',hv,hu',he'⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    hinj (fun z => nomatch z) he v₁ rfl J rfl
  let G' := embOvr initializedReplicaRecoveryLoopReg F.get J
  have hview : embStk initializedReplicaRecoveryWorkerReg G' = embStk replicaRecoveryWorkerReg F := by
    change embStk replicaRecoveryWorkerReg (embStk initializedReplicaRecoveryLoopReg G') = _
    rw [embStk_ovr hinj]
  have h255' : G'.R 255 = [] := by
    have hh := congrArg (fun S : Stacks 256 A => S.R 255) (embStk_ovr hinj F J)
    exact hh.trans h255
  have h256' : G'.R 256 = G.R 256 := by
    have hoff : ∀ i, initializedReplicaRecoveryLoopReg i ≠ 256 := by
      intro i hi
      have hv := congrArg (fun k : Fin 257 => k.val) hi
      change i.val = 256 at hv
      have hb := i.isLt
      omega
    exact (embOvr_off F.get J hoff).2.trans (by simp [J])
  refine ⟨v',G',(4*H.Fs.length+4)+n,hu'.trans (hu.trans hu₁),by omega,
    Exec.seq he₁' he',h255',h256',?_⟩
  rw [hview]
  rw [hworker] at hL hinp hout h110 h132 hpersistent hfactor
  exact ⟨hres,hrhs,houtput,hcoreF,hphysicalF,h116F,h167F,hL,hinp,hout,h110,h132,hpersistent,hfactor⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
