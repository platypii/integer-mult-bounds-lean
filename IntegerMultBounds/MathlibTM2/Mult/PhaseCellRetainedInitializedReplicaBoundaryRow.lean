module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryPhaseBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedReplicaBoundaryRow

/-! Lift the proved boundary phase beside the recovery masters, preserving their
actual tapes and the six fresh recovery temporaries without runtime copying. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 255 Q A U}

noncomputable def retainedInitializedReplicaBoundaryRow (hQ : SS.states ≤ Q) : Pr P 255 Q A U :=
  embProg replicaBoundaryPhaseReg Empty.elim (initializedReplicaBoundaryRow (P := Empty) hQ)

theorem retainedInitializedReplicaBoundaryRow_exec (H : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (target W : ℕ) (columns : List (ZMod s → GaussianInt)) :
    let B := haloBoundary s H.t H.band H.origin (H.origin+H.span)
    let q := H.precision
    let w := H.wordWidth
    let K := factorNewtonSteps H.p q
    let AZ := factorRankIntegerMatrix B W columns
    let bo := cstream A w ((naturalLineLc q K W B.card AZ).map colC).flatten
    let hf := cstream A w ((naturalLineUc q K W B.card AZ).map colC).flatten
    let df := cstream A w ((naturalLineRcs q K W B.card AZ).map fun x => (⟨x,0⟩ : GaussianInt))
    H.target = boundaryHaloTarget H.p H.u target H.rhsExp B.card →
    PreparedBoundaryColumns A H.p (boundaryTableBits H.p target H.rhsExp B.card) q w W B columns →
    ∀ r < H.Fs.length, ∀ D, ReplicaCouplingResidualSpec H r D →
    ∀ (v : HS 255 Q A U) (S : Stacks 255 A) (remaining : List (Fin (A+4))),
    (∀ i : Fin 242, S.L (Fin.castLE (by decide) i) = S.L (replicaBoundaryPhaseReg i)) →
    let J := embStk replicaBoundaryPhaseReg S
    CouplingIntervalMetadata H.metadataWidth s H.t H.band H.origin (H.origin+H.span) H.origin H.span
      (embStk (Fin.castLE (by decide : 168 ≤ 242)) J) →
    (J.R 123).length = H.span*w → (J.R 130).length = w →
    (∀ k : Fin 242, k.val < 77 → J.R k = []) →
    (∀ k ∈ [(104 : Fin 242),105,116,117,118,120,124,143,167], J.R k = []) →
    J.R 238 = cstream A w (packedInterval H.origin H.span D)++remaining →
    PackedPreparedBank q w W B.card J → PackedBoundaryFactorPages bo hf df J →
    let F := preparedBoundaryRhsState (initializedReplicaBoundaryRhsState H J) (cstream A w (replicaBoundarySolution H W columns D)++remaining) []
    let G := embOvr replicaBoundaryPhaseReg F.get S
    ∃ v' m, v'.user = v.user ∧ m ≤ initializeReplicaBoundaryRhsCost H+replicaBoundaryRhsCost H+preparedResidualSolveCost q w B.card W ∧
      Exec body (retainedInitializedReplicaBoundaryRow hQ)
        (mk v S) m (mk v' G) ∧ PackedPreparedBank q w W B.card (embStk replicaBoundaryPhaseReg G) ∧ PackedBoundaryFactorPages bo hf df (embStk replicaBoundaryPhaseReg G) ∧ ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg G) ∧
      (∀ k ∈ [(116 : Fin 255),117,118,120,123,124,167], G.L k = S.L k ∧ G.R k = S.R k) ∧
      (∀ k : Fin 255, 242 ≤ k.val → k.val < 248 → G.L k = S.L k ∧ G.R k = S.R k) ∧ G.L = S.L ∧
      PackedPreparedBank q w W B.card (embStk (Fin.castLE (by decide : 242 ≤ 255)) G) ∧
      PackedBoundaryFactorPages bo hf df (embStk (Fin.castLE (by decide : 242 ≤ 255)) G) := by
  dsimp only
  intro htarget hcolumns r hr D hD v S remaining hleft hmeta hvolume hword hscratch hfresh harchive hbank hpages
  let J := embStk replicaBoundaryPhaseReg S
  obtain ⟨vi,m,hu,hm,he,hbankF,hpagesF,hphysicalF⟩ := initializedReplicaBoundaryRow_exec
    (body := fun z : Empty => nomatch z) H hQ hA hp hwidth target W columns htarget hcolumns r hr D hD
    (embDn replicaBoundaryPhaseReg v) J remaining hmeta hvolume hword hscratch hfresh harchive hbank hpages
  let F := preparedBoundaryRhsState (initializedReplicaBoundaryRhsState H J)
    (cstream A H.wordWidth (replicaBoundarySolution H W columns D)++remaining) []
  obtain ⟨v',hv,hu',he'⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    replicaBoundaryPhaseReg_injective (fun z => nomatch z) he v rfl S rfl
  let G := embOvr replicaBoundaryPhaseReg F.get S
  have hbankG : PackedPreparedBank H.precision H.wordWidth W
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card (embStk replicaBoundaryPhaseReg G) := by
    rw [embStk_ovr replicaBoundaryPhaseReg_injective]
    exact hbankF
  have hleftG : G.L = S.L := embOvr_left_of_eq S F rfl
  refine ⟨v',m,hu'.trans hu,hm,he',hbankG,?_,?_,?_,?_,hleftG,?_,?_⟩
  · rw [embStk_ovr replicaBoundaryPhaseReg_injective]; exact hpagesF
  · rw [embStk_ovr replicaBoundaryPhaseReg_injective]; exact hphysicalF
  · intro k hk
    exact replicaBoundaryPhase_master_frame S F k hk
  · intro k h242 h248
    exact embOvr_off F.get S (fun i => replicaBoundaryPhaseReg_recovery_scratch_off i k h242 h248)
  · exact preparedBoundaryPhaseBank G hbankG (by intro i; rw [hleftG]; exact hleft i)
  · apply boundaryPhaseFactorPages G
    rw [embStk_ovr replicaBoundaryPhaseReg_injective]
    exact hpagesF

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
