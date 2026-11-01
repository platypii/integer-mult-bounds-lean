module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundarySolveStock

/-! Execute a complete physical residual-archive row with the shared boundary
solver. Both physical headers and numerical factors survive for the next row. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 242 Q A U}

theorem preparedReplicaBoundaryRow_finish_within (H : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (target W : ℕ) (columns : List (ZMod s → GaussianInt))
    (bank : Fin 168 → Fin 242) (volume rhsVolume symbols ts tm acc cs saved tmp : Fin 242)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (stock : ℕ) :
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
    ∀ (v v₀ : HS 242 Q A U) (S : Stacks 242 A) (n : ℕ) (remaining : List (Fin (A+4))),
    v₀.user = v.user →
    (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+stock)
      depth (prepareReplicaBoundaryRhs bank volume 238 rhsVolume 143 symbols ts tm acc cs saved tmp)
      (mk v S) n (mk v₀ (preparedBoundaryRhsState S remaining
        (cstream A w ((bFoldOrder s B).map (fun i => realPartWord (D i))))))) →
    PackedPreparedBank q w W B.card S → PackedBoundaryFactorPages bo hf df S →
    let F := preparedBoundaryRhsState S (cstream A w (replicaBoundarySolution H W columns D)++remaining) []
    ∃ v' m, v'.user = v.user ∧ m ≤ n+preparedResidualSolveCost q w B.card W ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (stock+push.workspace q w B.card W)) depth
        (preparedReplicaBoundaryRow bank volume rhsVolume symbols ts tm acc cs saved tmp hQ)
        (mk v S) m (mk v' F)) ∧ PackedPreparedBank q w W B.card F ∧ PackedBoundaryFactorPages bo hf df F := by
  dsimp only
  intro htarget hcolumns r hr D hD v v₀ S n remaining hu₀ he₀ hbank hpages
  let rhs := cstream A H.wordWidth ((bFoldOrder s (haloBoundary s H.t H.band H.origin (H.origin+H.span))).map
    (fun i => realPartWord (D i)))
  let J := preparedBoundaryRhsState S remaining rhs
  have hbankJ := hbank.replace_rhs remaining rhs
  have hpagesJ := hpages.replace_rhs remaining rhs
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := ReplicaCouplingResidualSpec.boundary_solve_exec_within (body := body) H
    hQ hA hp hwidth target W columns push htarget hcolumns r hr D hD v₀ J hbankJ
    (by simp [J,preparedBoundaryRhsState,boundaryFactorState,embStk,preparedBoundaryCoreReg,
      packedBoundaryFactorReg,boundaryFactorReg,rhs]) hpagesJ
  let output := cstream A H.wordWidth (replicaBoundarySolution H W columns D)
  have hfinal : {J with R := (Function.update (Function.update J.R 143 []) 238 (output++J.R 238))} =
      preparedBoundaryRhsState S (output++remaining) [] := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h143 : k = 143 <;> by_cases h238 : k = 238 <;>
      simp [J,preparedBoundaryRhsState,h143,h238]
  have hbankF := hbankJ.publish output
  have hpagesF := hpagesJ.publish output
  rw [hfinal] at hbankF hpagesF
  exact ⟨v₁,n+n₁,hu₁.trans hu₀,Nat.add_le_add_left hn₁ n,
    (fun depth => (mn_seq_within_add (he₀ depth) (he₁ depth)).cast rfl (congrArg (mk v₁) hfinal)),hbankF,hpagesF⟩

theorem replicaBoundaryRow_exec_within (H : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (target W : ℕ) (columns : List (ZMod s → GaussianInt))
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c : ℕ)
    (hpush : mnNativePushBound c (replicaBoundaryRhs (P := P) (Q := Q) (A := A) (U := U))) :
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
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (c*replicaBoundaryRhsCost H+push.workspace q w B.card W)) depth
        (replicaBoundaryRow hQ) (mk v S) m (mk v' F)) ∧ PackedPreparedBank q w W B.card F ∧ PackedBoundaryFactorPages bo hf df F ∧ ReplicaBoundaryRhsReady H F := by
  dsimp only
  intro htarget hcolumns r hr D hD v S remaining hphysical harchive hbank hpages
  obtain ⟨v₀,n,hu₀,hn,he⟩ := replicaBoundaryRhs_exec (body := body) H (by omega : 4 ≤ A) D remaining v S
    hphysical harchive
  have he' : Exec body
      (prepareReplicaBoundaryRhs replicaBoundaryFoldBank 123 238 124 143 0 1 2 3 4 104 105)
      (mk v S) n (mk v₀ (preparedBoundaryRhsState S remaining
        (cstream A H.wordWidth ((bFoldOrder s (haloBoundary s H.t H.band H.origin (H.origin+H.span))).map
          (fun i => realPartWord (D i)))))) := he
  obtain ⟨v',m,hu,hm,hex,hbankF,hpagesF⟩ := preparedReplicaBoundaryRow_finish_within (body := body) H
    hQ hA hp hwidth target W columns replicaBoundaryFoldBank 123 124 0 1 2 3 4 104 105 push (c*replicaBoundaryRhsCost H)
    htarget hcolumns r hr D hD v v₀ S n remaining hu₀ (fun depth => mn_native_exec_within he' c hpush depth _
      (Nat.add_le_add_left (Nat.mul_le_mul_left c hn) _)) hbank hpages
  exact ⟨v',m,hu,by omega,hex,hbankF,hpagesF,hphysical.after_row H _⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
