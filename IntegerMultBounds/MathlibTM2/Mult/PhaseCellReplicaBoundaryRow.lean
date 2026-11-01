module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedReplicaBoundaryRow

/-! Execute a complete physical residual-archive row with the shared boundary
solver. Both physical headers and numerical factors survive for the next row. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 242 Q A U}

noncomputable def replicaBoundaryRow (hQ : SS.states ≤ Q) : Pr P 242 Q A U :=
  preparedReplicaBoundaryRow replicaBoundaryFoldBank 123 124 0 1 2 3 4 104 105 hQ

theorem ReplicaBoundaryRhsReady.after_row (H : ReplicaHaloProblem s) {S : Stacks 242 A}
    (h : ReplicaBoundaryRhsReady H S) (words : List (Fin (A+4))) :
    ReplicaBoundaryRhsReady H (preparedBoundaryRhsState S words []) := by
  constructor
  · simpa [preparedBoundaryRhsState] using h.volume
  · simpa [preparedBoundaryRhsState] using h.rhsVolume
  · simpa [preparedBoundaryRhsState] using h.mask
  · simpa [preparedBoundaryRhsState] using h.width
  · simpa [preparedBoundaryRhsState] using h.count
  · simpa [preparedBoundaryRhsState] using h.floor
  · simpa [preparedBoundaryRhsState] using h.parity
  · simpa [preparedBoundaryRhsState] using h.bytes
  · simpa [preparedBoundaryRhsState] using h.saved
  · simpa [preparedBoundaryRhsState] using h.tmp
  · simp [preparedBoundaryRhsState]
  · intro k hk
    have h143 : k ≠ 143 := by intro he; subst k; omega
    have h238 : k ≠ 238 := by intro he; subst k; omega
    simpa [preparedBoundaryRhsState,h143,h238] using h.scratch k hk

theorem replicaBoundaryRow_exec (H : ReplicaHaloProblem s)
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
    ReplicaBoundaryRhsReady H S →
    S.R 238 = cstream A w (packedInterval H.origin H.span D)++remaining →
    PackedPreparedBank q w W B.card S → PackedBoundaryFactorPages bo hf df S →
    let F := preparedBoundaryRhsState S (cstream A w (replicaBoundarySolution H W columns D)++remaining) []
    ∃ v' m, v'.user = v.user ∧ m ≤ replicaBoundaryRhsCost H+preparedResidualSolveCost q w B.card W ∧
      Exec body (replicaBoundaryRow hQ)
        (mk v S) m (mk v' F) ∧ PackedPreparedBank q w W B.card F ∧ PackedBoundaryFactorPages bo hf df F ∧ ReplicaBoundaryRhsReady H F := by
  dsimp only
  intro htarget hcolumns r hr D hD v S remaining hphysical harchive hbank hpages
  obtain ⟨v₀,n,hu₀,hn,he⟩ := replicaBoundaryRhs_exec (body := body) H (by omega : 4 ≤ A) D remaining v S
    hphysical harchive
  have he' : Exec body
      (prepareReplicaBoundaryRhs replicaBoundaryFoldBank 123 238 124 143 0 1 2 3 4 104 105)
      (mk v S) n (mk v₀ (preparedBoundaryRhsState S remaining
        (cstream A H.wordWidth ((bFoldOrder s (haloBoundary s H.t H.band H.origin (H.origin+H.span))).map
          (fun i => realPartWord (D i)))))) := he
  obtain ⟨v',m,hu,hm,hex,hbankF,hpagesF⟩ := preparedReplicaBoundaryRow_finish (body := body) H
    hQ hA hp hwidth target W columns replicaBoundaryFoldBank 123 124 0 1 2 3 4 104 105
    htarget hcolumns r hr D hD v v₀ S n remaining hu₀ he' hbank hpages
  exact ⟨v',m,hu,by omega,hex,hbankF,hpagesF,hphysical.after_row H _⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
