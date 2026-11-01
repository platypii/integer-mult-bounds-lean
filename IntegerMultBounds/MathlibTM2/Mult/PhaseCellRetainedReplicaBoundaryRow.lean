module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryPhaseBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryOwnedFrame

/-! Execute one shared-factor boundary row beside retained recovery masters.
Only the solution/archive stack and the empty RHS port change. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 255 Q A U}

noncomputable def retainedReplicaBoundaryRow (hQ : SS.states ≤ Q) : Pr P 255 Q A U :=
  embProg replicaBoundaryPhaseReg Empty.elim (replicaBoundaryRow (P := Empty) hQ)

def retainedReplicaBoundaryState (S : Stacks 255 A) (words : List (Fin (A+4))) : Stacks 255 A :=
  {S with R := Function.update (Function.update S.R 238 words) 143 []}

theorem retainedReplicaBoundaryState_frame (S : Stacks 255 A) (words : List (Fin (A+4)))
    (k : Fin 255) (hk : k ∉ [143,238]) : (retainedReplicaBoundaryState S words).R k = S.R k := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hk
  simp [retainedReplicaBoundaryState,hk.1,hk.2]

theorem retainedReplicaBoundaryRow_exec (H : ReplicaHaloProblem s)
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
    ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg S) →
    S.R 238 = cstream A w (packedInterval H.origin H.span D)++remaining →
    ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 255)) S) →
    PackedBoundaryFactorPages bo hf df (embStk (Fin.castLE (by decide : 242 ≤ 255)) S) →
    let F := retainedReplicaBoundaryState S (cstream A w (replicaBoundarySolution H W columns D)++remaining)
    ∃ v' m, v'.user = v.user ∧ m ≤ replicaBoundaryRhsCost H+preparedResidualSolveCost q w B.card W ∧
      Exec body (retainedReplicaBoundaryRow hQ)
        (mk v S) m (mk v' F) ∧ ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 255)) F) ∧
      PackedBoundaryFactorPages bo hf df (embStk (Fin.castLE (by decide : 242 ≤ 255)) F) ∧
      ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg F) := by
  dsimp only
  intro htarget hcolumns r hr D hD v S remaining hleft hphysical harchive hcore hpages
  let words := cstream A H.wordWidth (replicaBoundarySolution H W columns D)++remaining
  let F := retainedReplicaBoundaryState S words
  obtain ⟨vi,m,hu,hm,he,hbankT,hpagesT,hphysicalT⟩ := replicaBoundaryRow_exec (body := fun z : Empty => nomatch z) H
    hQ hA hp hwidth target W columns htarget hcolumns r hr D hD (embDn replicaBoundaryPhaseReg v)
    (embStk replicaBoundaryPhaseReg S) remaining hphysical
    (by change S.R (replicaBoundaryPhaseReg 238) = _; rw [replicaBoundaryPhaseReg_fixed _ (by decide)]; exact harchive)
    (preparedBoundaryPhaseBank_of_native S hcore.bank hleft) (boundaryPhaseFactorPages_of_native S hpages)
  obtain ⟨v',hv,hu',he'⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    replicaBoundaryPhaseReg_injective (fun z => nomatch z) he v rfl S rfl
  have hresult : embOvr replicaBoundaryPhaseReg
      (preparedBoundaryRhsState (embStk replicaBoundaryPhaseReg S) words []).get S = F := by
    unfold preparedBoundaryRhsState
    rw [embOvr_updateR_updateR replicaBoundaryPhaseReg_injective]
    rw [replicaBoundaryPhaseReg_fixed 238 (by decide),replicaBoundaryPhaseReg_fixed 143 (by decide)]
    rfl
  have hcoreF : ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 255)) F) := by
    apply ReplicaRecoveryCoreReady.of_owned_frame H W hcore
      (F := embStk (Fin.castLE (by decide : 248 ≤ 255)) F) rfl
    intro k hk
    have h143 : S.R 143 = [] := hcore.rhs
    by_cases heq : k = 143
    · subst k
      change (retainedReplicaBoundaryState S words).R 143 = S.R 143
      simp [retainedReplicaBoundaryState,h143]
    apply retainedReplicaBoundaryState_frame
    simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,Fin.castLE] at hk heq ⊢
    norm_num at hk heq ⊢
    tauto
  refine ⟨v',m,hu'.trans hu,hm,he'.cast rfl (congrArg (mk v') hresult),hcoreF,?_,?_⟩
  · apply hpages.of_solution_frame
    intro k hk h238
    apply retainedReplicaBoundaryState_frame
    simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,Fin.castLE] at h238 ⊢
    norm_num at h238 ⊢
    omega
  · change ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg F)
    rw [← hresult,embStk_ovr replicaBoundaryPhaseReg_injective]
    exact hphysicalT

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
