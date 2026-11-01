module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedReplicaRecoveryPreparation

/-! Generate one boundary factor bank inside the common replica caller.
The placement preserves every surrounding tape, including retained replica input. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 392 Q A U}

def replicaRecoveryBoundaryFactoryReg (i : Fin 242) : Fin 392 :=
  replicaRecoveryPreparationCallerWorkerReg (Fin.castLE (by decide) i)

theorem replicaRecoveryBoundaryFactoryReg_injective : Function.Injective replicaRecoveryBoundaryFactoryReg :=
  replicaRecoveryPreparationCallerReg_injective.comp
    ((Fin.castLE_injective _).comp (Fin.castLE_injective _))

noncomputable def placedReplicaBoundaryFactory (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 392 Q A U :=
  embProg replicaRecoveryBoundaryFactoryReg Empty.elim (packedBoundaryFactoryGeometry (P := Empty) hR hQ)

theorem placedReplicaBoundaryFactory_exec (H : ReplicaHaloProblem s) (target : ℕ)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (hpad : 2*((s/(H.t-s)+1)-2*H.band) ≤ 2^H.l+1)
    (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card)
    (v : HS 392 Q A U) (S : Stacks 392 A) (base : Stacks 242 A)
    (hinput : embStk replicaRecoveryBoundaryFactoryReg S = replicaBoundaryFactoryInput H base) :
    ∃ v' F n, ∃ columns : List (ZMod s → GaussianInt), v'.user = v.user ∧
      n ≤ replicaBoundaryFactoryCost H target ∧
      Exec body (placedReplicaBoundaryFactory hR hQ) (mk v S) n (mk v' F) ∧
      ReplicaBoundaryFactorData H target columns (embStk replicaRecoveryBoundaryFactoryReg F) ∧
      PackedHaloBetweenInputs (2^15*H.p) (H.stage+1) H.precision H.l s H.t H.u H.band
        H.origin (H.origin+H.span) (publicationGeometryWidth H.t H.band) H.wordWidth (12*H.band+1)
        (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card
        (extendStacks (by decide) (embStk replicaRecoveryBoundaryFactoryReg F)) ∧
      ReplicaFactoryWorkspace (embStk replicaRecoveryBoundaryFactoryReg F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k, (∀ i, replicaRecoveryBoundaryFactoryReg i ≠ k) → F.L k = S.L k ∧ F.R k = S.R k) := by
  let e := replicaRecoveryBoundaryFactoryReg
  obtain ⟨vi,G,n,columns,hu,hn,he,hfactor,hbetween,hin,hout,hworkspace,_⟩ :=
    replicaBoundaryFactory_exec (body := fun f : Empty => nomatch f) H target hR hQ hA hp hwidth
      hpad htarget (embDn e v) base
  have he' : Exec (fun f : Empty => nomatch f) (packedBoundaryFactoryGeometry hR hQ)
      (mk (embDn e v) (embStk e S)) n (mk vi G) := by rw [hinput]; exact he
  obtain ⟨v',hv,hu',hePlaced⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    replicaRecoveryBoundaryFactoryReg_injective (fun f : Empty => nomatch f) he' v rfl S rfl
  let F := embOvr e G.get S
  have hview : embStk e F = G := embStk_ovr replicaRecoveryBoundaryFactoryReg_injective G S
  have hinS : S.inp = base.inp := congrArg Stacks.inp hinput
  have houtS : S.out = base.out := congrArg Stacks.out hinput
  refine ⟨v',F,n,columns,hu'.trans hu,hn,hePlaced,?_,?_,?_,?_,?_,?_⟩
  · rw [hview]; exact hfactor
  · rw [hview]; exact hbetween
  · rw [hview]; exact hworkspace
  · exact hin.trans hinS.symm
  · exact hout.trans houtS.symm
  · intro k hk
    exact embOvr_off G.get S hk

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
