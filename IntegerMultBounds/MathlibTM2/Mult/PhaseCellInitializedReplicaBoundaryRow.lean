module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeReplicaBoundaryRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryRow

/-! Shared physical setup preserves the prepared numerical bank. Compose that
setup once with the first actual residual row and retain readiness for recovery. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 242 Q A U}

private theorem boundarySetup_frame (H : ReplicaHaloProblem s) (S : Stacks 242 A)
    (k : Fin 242) (hk : k.val < 64 ∨ 168 ≤ k.val) :
    (initializedReplicaBoundaryRhsState H S).R k = S.R k := by
  apply initializedReplicaBoundaryRhsState_frame
  simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff]
  norm_num
  omega

theorem preparedBank_initialize_boundary_rhs (H : ReplicaHaloProblem s)
    {q w W N : ℕ} {S : Stacks 242 A} (h : PackedPreparedBank q w W N S) :
    PackedPreparedBank q w W N (initializedReplicaBoundaryRhsState H S) := by
  apply h.of_runtime_frame (F := initializedReplicaBoundaryRhsState H S) rfl
  · intro k hk; exact boundarySetup_frame H S k (Or.inl hk)
  · exact initializedReplicaBoundaryRhsState_frame H S 119 (by decide)
  · intro k hk _; exact boundarySetup_frame H S k (Or.inr hk)

theorem factorPages_initialize_boundary_rhs (H : ReplicaHaloProblem s)
    {S : Stacks 242 A} {bo hf df : List (Fin (A+4))} (h : PackedBoundaryFactorPages bo hf df S) :
    PackedBoundaryFactorPages bo hf df (initializedReplicaBoundaryRhsState H S) := by
  apply h.of_solution_frame
  intro k hk _
  exact boundarySetup_frame H S k (Or.inr hk)

noncomputable def initializedReplicaBoundaryRow (hQ : SS.states ≤ Q) : Pr P 242 Q A U :=
  .seq initializeReplicaBoundaryRhs (replicaBoundaryRow hQ)

theorem initializedReplicaBoundaryRow_exec (H : ReplicaHaloProblem s)
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
    ∀ (v : HS 242 Q A U) (S : Stacks 242 A) (remaining : List (Fin (A+4))),
    CouplingIntervalMetadata H.metadataWidth s H.t H.band H.origin (H.origin+H.span) H.origin H.span
      (embStk (Fin.castLE (by decide : 168 ≤ 242)) S) →
    (S.R 123).length = H.span*w → (S.R 130).length = w →
    (∀ k : Fin 242, k.val < 77 → S.R k = []) →
    (∀ k ∈ [(104 : Fin 242),105,116,117,118,120,124,143,167], S.R k = []) →
    S.R 238 = cstream A w (packedInterval H.origin H.span D)++remaining →
    PackedPreparedBank q w W B.card S → PackedBoundaryFactorPages bo hf df S →
    let F := preparedBoundaryRhsState (initializedReplicaBoundaryRhsState H S) (cstream A w (replicaBoundarySolution H W columns D)++remaining) []
    ∃ v' m, v'.user = v.user ∧ m ≤ initializeReplicaBoundaryRhsCost H+replicaBoundaryRhsCost H+preparedResidualSolveCost q w B.card W ∧
      Exec body (initializedReplicaBoundaryRow hQ)
        (mk v S) m (mk v' F) ∧ PackedPreparedBank q w W B.card F ∧ PackedBoundaryFactorPages bo hf df F ∧ ReplicaBoundaryRhsReady H F := by
  dsimp only
  intro htarget hcolumns r hr D hD v S remaining hmeta hvolume hword hscratch hfresh harchive hbank hpages
  obtain ⟨v₀,n₀,hu₀,hn₀,he₀,hphysical⟩ := initializeReplicaBoundaryRhs_exec (body := body) H
    (by omega : 4 ≤ A) v S hmeta hvolume hword hscratch hfresh
  let J := initializedReplicaBoundaryRhsState H S
  have harchiveJ : J.R 238 = cstream A H.wordWidth (packedInterval H.origin H.span D)++remaining := by
    rw [initializedReplicaBoundaryRhsState_frame H S 238 (by decide)]
    exact harchive
  obtain ⟨v',m,hu,hm,hex,hbankF,hpagesF,hphysicalF⟩ := replicaBoundaryRow_exec (body := body) H
    hQ hA hp hwidth target W columns htarget hcolumns r hr D hD v₀ J remaining hphysical harchiveJ
    (preparedBank_initialize_boundary_rhs H hbank) (factorPages_initialize_boundary_rhs H hpages)
  exact ⟨v',n₀+m,hu.trans hu₀,by omega,Exec.seq he₀ hex,hbankF,hpagesF,hphysicalF⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
