module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedFactoryFactorExec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundarySolution

/-! The executed shared factory supplies exactly the numerical language used
by replica boundary solve and recovery, at their common proved precision. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 242 Q A U}

structure ReplicaBoundaryFactorData (H : ReplicaHaloProblem s) (target : ℕ)
    (columns : List (ZMod s → GaussianInt)) (F : Stacks 242 A) : Prop where
  prepared : PreparedBoundaryColumns A H.p
    (boundaryTableBits H.p (boundaryRecoveryTarget H.p target) H.rhsExp
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card)
    H.precision H.wordWidth (12*H.band+1) (haloBoundary s H.t H.band H.origin (H.origin+H.span)) columns
  error : let B := haloBoundary s H.t H.band H.origin (H.origin+H.span)
    ∀ i ∈ B, ∀ j ∈ B,
      |bandBoundaryTable B (12*H.band+1) (computedBoundaryTable A H.precision H.wordWidth B columns) i j-
        (SchurDominance.run (realMatrix s H.t H.p H.u) (haloVertices s H.origin (H.origin+H.span))
          (haloInterior s H.t H.band H.origin (H.origin+H.span)).toList).1 i j| ≤
        1/(2 : ℝ)^(boundaryTableBits H.p (boundaryRecoveryTarget H.p target) H.rhsExp B.card)
  pages : let B := haloBoundary s H.t H.band H.origin (H.origin+H.span)
    let W := 12*H.band+1
    let K := factorNewtonSteps H.p H.precision
    let AZ := factorRankIntegerMatrix B W columns
    PackedBoundaryFactorPages
      (cstream A H.wordWidth ((naturalLineLc H.precision K W B.card AZ).map colC).flatten)
      (cstream A H.wordWidth ((naturalLineUc H.precision K W B.card AZ).map colC).flatten)
      (cstream A H.wordWidth ((naturalLineRcs H.precision K W B.card AZ).map fun z => (⟨z,0⟩ : GaussianInt))) F
  bank : PackedPreparedBank H.precision H.wordWidth (12*H.band+1)
    (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card F

def replicaBoundaryFactoryInput (H : ReplicaHaloProblem s) (S : Stacks 242 A) : Stacks 242 A :=
  packedFactoryInputBank S (2^15*H.p) (H.stage+1) H.precision H.l s H.t H.u H.band
    H.origin (H.origin+H.span) (publicationGeometryWidth H.t H.band)

theorem replicaBoundaryFactoryInput_eq (H : ReplicaHaloProblem s) (target : ℕ)
    (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card) (S : Stacks 242 A) :
    let bits := boundaryTableBits H.p (boundaryRecoveryTarget H.p target) H.rhsExp
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card
    let T := initialSchurTarget H.p H.u bits 2
    packedFactoryInputBank S (2^15*H.p) (executionStagePrecision H.p H.l T 2+1)
      (executionPrecision H.p H.l T 2) H.l s H.t H.u H.band H.origin (H.origin+H.span)
      (publicationGeometryWidth H.t H.band) = replicaBoundaryFactoryInput H S := by
  obtain ⟨hq,hstage,hw⟩ := H.boundary_sizing (boundaryRecoveryTarget H.p target) htarget
  unfold replicaBoundaryFactoryInput
  rw [hq,hstage]

noncomputable def replicaBoundaryFactoryCost (H : ReplicaHaloProblem s) (target : ℕ) :=
  let B := haloBoundary s H.t H.band H.origin (H.origin+H.span)
  let V := publicationGeometryWidth H.t H.band
  constructedBoundaryFactorCost H.p H.u H.l s H.t H.origin (H.origin+H.span)
    (boundaryRecoveryTarget H.p target) H.rhsExp+
    (2*(B.card*V+V+B.card)+7)+((s+H.t+H.band+H.origin+(H.origin+H.span))*(4*V+10)+56*V+77)

theorem replicaBoundaryFactory_exec (H : ReplicaHaloProblem s) (target : ℕ)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (hpad : 2*((s/(H.t-s)+1)-2*H.band) ≤ 2^H.l+1)
    (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card)
    (v : HS 242 Q A U) (S : Stacks 242 A) :
    ∃ v' F n, ∃ columns : List (ZMod s → GaussianInt), v'.user = v.user ∧
      n ≤ replicaBoundaryFactoryCost H target ∧
      Exec body (packedBoundaryFactoryGeometry hR hQ) (mk v (replicaBoundaryFactoryInput H S)) n (mk v' F) ∧
      ReplicaBoundaryFactorData H target columns F := by
  obtain ⟨hq,hstage,hw⟩ := H.boundary_sizing (boundaryRecoveryTarget H.p target) htarget
  simp only [ReplicaHaloProblem.band] at hq hstage hw
  have ha : 0 < |H.α| := abs_pos.mpr (by
    intro hz
    have hh := H.alpha_sq
    have hu : (0 : ℝ) < H.u := by exact_mod_cast (show 0 < H.u by have hh := H.u_pos; omega)
    simp [hz] at hh
    linarith)
  have hα : |H.α|^2 = (H.u : ℝ) := by simpa only [sq_abs] using H.alpha_sq
  have hbudget : |H.α|^2*H.d ≤ H.p := by simpa only [sq_abs] using H.budget
  obtain ⟨v',F,n,columns,hu,hn,he,hinp,hout,h110,h132,hcolumns,herror,hpages,hbetween,htable,hstock⟩ :=
    packedFactoryInputBank_factor_exec (body := body) (p := H.p) (l := H.l) (s := s) (t := H.t) (u := H.u)
      (target := boundaryRecoveryTarget H.p target) (rhsExp := H.rhsExp)
      (a := H.origin) (b := H.origin+H.span) (α := |H.α|) (d := H.d)
      hR hQ hA hp hwidth ha H.s_lt_t H.u_pos hα H.theta_lower H.gap hbudget H.band_fit
      (by have hh := H.span_fit; omega) H.span_fit hpad v S
  refine ⟨v',F,n,columns,hu,hn,?_,?_⟩
  · have hin := replicaBoundaryFactoryInput_eq H target htarget S
    simp only [ReplicaHaloProblem.band] at hin
    exact (congrArg (fun I : Stacks 242 A => Exec body (packedBoundaryFactoryGeometry hR hQ)
      (mk v I) n (mk v' F)) hin).mp he
  · constructor
    · simpa only [ReplicaHaloProblem.band,← hq,← hw] using hcolumns
    · simpa only [ReplicaHaloProblem.band,← hq,← hw] using herror
    · simpa only [ReplicaHaloProblem.band,← hq,← hw] using hpages
    · simpa only [ReplicaHaloProblem.band,← hq,← hw,packedBoundaryRecoveryBase,embStk_extendStacks] using hbetween.bank

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
