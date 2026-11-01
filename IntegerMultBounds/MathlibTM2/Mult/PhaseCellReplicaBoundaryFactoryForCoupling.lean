module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryFactoryWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireReplicaFactoryGeometry

/-! Generate shared factors and ordinary masters, then pay once to release the
old factory geometry before the actual coupling setup regenerates it. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 242 Q A U}

noncomputable def replicaBoundaryFactoryForCoupling (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 242 Q A U :=
  .seq (replicaBoundaryFactoryWithWidth hR hQ) retireReplicaFactoryGeometry

theorem replicaBoundaryFactoryForCoupling_exec (H : ReplicaHaloProblem s) (target : ℕ)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (hpad : 2*((s/(H.t-s)+1)-2*H.band) ≤ 2^H.l+1)
    (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card)
    (v : HS 242 Q A U) (S : Stacks 242 A) :
    ∃ v' F n, ∃ columns : List (ZMod s → GaussianInt), v'.user = v.user ∧
      n ≤ replicaBoundaryFactoryCost H target+(8*H.precision+9)+
        (26*publicationGeometryWidth H.t H.band+27) ∧
      Exec body (replicaBoundaryFactoryForCoupling hR hQ) (mk v (replicaBoundaryFactoryInput H S)) n (mk v' F) ∧
      ReplicaBoundaryFactorData H target columns F ∧
      CouplingMasterHeaders (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span)
        (embStk (Fin.castLE (by decide : 168 ≤ 242)) F) ∧
      (F.R 118).length = H.stage+1 ∧ (F.R 120).length = H.l ∧
      (∀ k ∈ replicaFactoryGeometryPorts, F.R (Fin.castLE (by decide : 168 ≤ 242) k) = []) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ ReplicaFactoryWorkspace F := by
  obtain ⟨v₁,J,n₁,columns,hu₁,hn₁,he₁,hdata,hheaders,hcursor,hinp,hout,hwork⟩ :=
    replicaBoundaryFactoryWithWidth_exec (body := body) H target hR hQ hA hp hwidth hpad htarget v S
  have hview : embStk packedRecoveryRuntimeReg (extendStacks (by decide : 242 ≤ 248) J) =
      embStk (Fin.castLE (by decide : 168 ≤ 242)) J := by
    refine Stacks.ext rfl rfl ?_ ?_ <;> funext i
    all_goals simp [embStk,extendStacks,packedRecoveryRuntimeReg,
      show i.val < 242 by have hi := i.isLt; omega]
    all_goals rfl
  rw [hview] at hheaders
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂,hdataF,hmasters,hstage,hlevel,hworkF⟩ :=
    retireReplicaFactoryGeometry_exec (body := body) H target (publicationGeometryWidth H.t H.band)
      columns v₁ J hdata hheaders hcursor hwork
  exact ⟨v₂,retiredReplicaFactoryGeometry J,n₁+n₂,columns,hu₂.trans hu₁,by omega,
    Exec.seq he₁ he₂,hdataF,hmasters,hstage,hlevel,retiredReplicaFactoryGeometry_blank J,hinp,hout,hworkF⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
