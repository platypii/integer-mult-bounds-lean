module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareReplicaBoundaryRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryRhsFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundarySolve

/-! Finish an actual archive-to-RHS preparation trace with the shared solver.
The published solution sits above the remaining archive until recovery takes it. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 242 Q A U}

noncomputable def preparedReplicaBoundaryRow (bank : Fin 168 → Fin 242)
    (volume rhsVolume symbols ts tm acc cs saved tmp : Fin 242) (hQ : SS.states ≤ Q) : Pr P 242 Q A U :=
  .seq (prepareReplicaBoundaryRhs bank volume 238 rhsVolume 143 symbols ts tm acc cs saved tmp)
    (packedPreparedResidualSolve hQ)

theorem preparedReplicaBoundaryRow_finish (H : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (target W : ℕ) (columns : List (ZMod s → GaussianInt))
    (bank : Fin 168 → Fin 242) (volume rhsVolume symbols ts tm acc cs saved tmp : Fin 242) :
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
    Exec body (prepareReplicaBoundaryRhs bank volume 238 rhsVolume 143 symbols ts tm acc cs saved tmp)
      (mk v S) n (mk v₀ (preparedBoundaryRhsState S remaining
        (cstream A w ((bFoldOrder s B).map (fun i => realPartWord (D i)))))) →
    PackedPreparedBank q w W B.card S → PackedBoundaryFactorPages bo hf df S →
    let F := preparedBoundaryRhsState S (cstream A w (replicaBoundarySolution H W columns D)++remaining) []
    ∃ v' m, v'.user = v.user ∧ m ≤ n+preparedResidualSolveCost q w B.card W ∧
      Exec body (preparedReplicaBoundaryRow bank volume rhsVolume symbols ts tm acc cs saved tmp hQ)
        (mk v S) m (mk v' F) ∧ PackedPreparedBank q w W B.card F ∧ PackedBoundaryFactorPages bo hf df F := by
  dsimp only
  intro htarget hcolumns r hr D hD v v₀ S n remaining hu₀ he₀ hbank hpages
  let rhs := cstream A H.wordWidth ((bFoldOrder s (haloBoundary s H.t H.band H.origin (H.origin+H.span))).map
    (fun i => realPartWord (D i)))
  let J := preparedBoundaryRhsState S remaining rhs
  have hbankJ := hbank.replace_rhs remaining rhs
  have hpagesJ := hpages.replace_rhs remaining rhs
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := ReplicaCouplingResidualSpec.boundary_solve_exec (body := body) H
    hQ hA hp hwidth target W columns htarget hcolumns r hr D hD v₀ J hbankJ
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
    (Exec.seq he₀ he₁).cast rfl (congrArg (mk v₁) hfinal),hbankF,hpagesF⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
