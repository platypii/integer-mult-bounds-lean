module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareReplicaBoundaryFactory
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryFactoryForCoupling

/-! Generate the shared factor bank in the actual replica caller. Input
installation is executed, old geometry is retired, and the gather file restores. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 389 Q A U}

noncomputable def generatedReplicaBoundaryFactory (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 389 Q A U :=
  .seq prepareReplicaBoundaryFactory
    (.seq (embProg replicaRecoveryCallerFactoryReg Empty.elim (replicaBoundaryFactoryForCoupling hR hQ)) (uclear 119))

noncomputable def generatedReplicaBoundaryFactoryCost (H : ReplicaHaloProblem s) (target : ℕ) :=
  prepareReplicaBoundaryFactoryCost H+
    (replicaBoundaryFactoryCost H target+(8*H.precision+9)+(26*publicationGeometryWidth H.t H.band+27))+
    (2*publicationGeometryWidth H.t H.band+2)

theorem generatedReplicaBoundaryFactory_exec (H : ReplicaHaloProblem s) (target : ℕ)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (hpad : 2*((s/(H.t-s)+1)-2*H.band) ≤ 2^H.l+1)
    (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card)
    (buffers : ReplicaLoopBuffers A) (v : HS 389 Q A U) (S : Stacks 389 A)
    (headers : ReplicaLoopHeaders H replicaRecoveryCallerInterior.gather buffers S)
    (h119 : S.R 119 = [])
    (hblank : ∀ i, S.R (replicaRecoveryCallerFactoryReg i) = [])
    (hleft : ∀ i, S.L (replicaRecoveryCallerFactoryReg i) = []) :
    ∃ v' F n, ∃ columns : List (ZMod s → GaussianInt), v'.user = v.user ∧
      n ≤ generatedReplicaBoundaryFactoryCost H target ∧
      Exec body (generatedReplicaBoundaryFactory hR hQ) (mk v S) n (mk v' F) ∧
      ReplicaBoundaryFactorData H target columns (embStk replicaRecoveryCallerFactoryReg F) ∧
      CouplingMasterHeaders (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span)
        (embStk replicaRecoveryCallerCoupling.bank F) ∧
      (F.R (replicaRecoveryCallerCoupling.bank 118)).length = H.stage+1 ∧
      (F.R (replicaRecoveryCallerCoupling.bank 120)).length = H.l ∧
      (∀ k ∈ replicaFactoryGeometryPorts, F.R (replicaRecoveryCallerCoupling.bank k) = []) ∧
      embStk replicaRecoveryCallerInterior.gather F = embStk replicaRecoveryCallerInterior.gather S ∧
      F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k, (∀ i, replicaRecoveryCallerFactoryReg i ≠ k) → F.L k = S.L k ∧ F.R k = S.R k) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,hview,he₁⟩ := prepareReplicaBoundaryFactory_exec (body := body)
    H buffers v S headers h119 hblank hleft 0
  let M := preparedReplicaBoundaryFactoryInput H S
  obtain ⟨vn,B,n₂,columns,hun,hn₂,hen,hdata,hmasters,hstage,hlevel,hgeometry,hinp,hout⟩ :=
    replicaBoundaryFactoryForCoupling_exec (body := fun f : Empty => nomatch f) H target
      hR hQ hA hp hwidth hpad htarget (embDn replicaRecoveryCallerFactoryReg v₁)
      (embStk replicaRecoveryCallerFactoryReg S)
  obtain ⟨v₂,hvn,hu₂,he₂⟩ := exec_emb_ovr (e := replicaRecoveryCallerFactoryReg) (ι := Empty.elim)
    (body' := body) replicaRecoveryCallerFactoryReg_injective (fun f => nomatch f) hen v₁ rfl M hview
  let J := embOvr replicaRecoveryCallerFactoryReg B.get M
  have hbankJ : embStk replicaRecoveryCallerFactoryReg J = B :=
    embStk_ovr replicaRecoveryCallerFactoryReg_injective B M
  have hoffJ (k : Fin 389) (hk : ∀ i, replicaRecoveryCallerFactoryReg i ≠ k) : J.L k = M.L k ∧ J.R k = M.R k :=
    embOvr_off B.get M hk
  have h119J : J.R 119 = List.replicate (publicationGeometryWidth H.t H.band) tick := by
    have hg := congrArg (fun C : Stacks 126 A => C.R 119) (preparedReplicaBoundaryFactoryInput_gather H S)
    exact (hoffJ 119 (fun i => replicaRecoveryCallerFactoryReg_gather i 119)).2.trans hg
  obtain ⟨v',hu₃,he₃⟩ := uclear_exec body 119 v₂ J
  rw [h119J,List.length_replicate] at he₃
  let F : Stacks 389 A := {J with R := Function.update J.R 119 []}
  have hbankF : embStk replicaRecoveryCallerFactoryReg F = B := by
    exact (embStk_updateR_off J 119 [] (fun i => replicaRecoveryCallerFactoryReg_gather i 119)).trans hbankJ
  have hinput : F.inp = S.inp := hinp
  have houtput : F.out = S.out := hout
  have hoff (k : Fin 389) (hk : ∀ i, replicaRecoveryCallerFactoryReg i ≠ k) : F.L k = S.L k ∧ F.R k = S.R k := by
    refine ⟨(hoffJ k hk).1,?_⟩
    by_cases h119k : k = 119
    · subst k
      exact h119.symm
    · change Function.update J.R 119 [] k = S.R k
      rw [Function.update_of_ne h119k,(hoffJ k hk).2]
      exact (replicaBoundaryFactoryInstalled_frame H _ k hk).2.trans (Function.update_of_ne h119k _ _)
  have hbank : embStk (Fin.castLE (by decide : 168 ≤ 242)) (embStk replicaRecoveryCallerFactoryReg F) =
      embStk replicaRecoveryCallerCoupling.bank F := replicaRecoveryCallerCoupling_runtime_view F
  refine ⟨v',F,n₁+(n₂+(2*publicationGeometryWidth H.t H.band+2)),columns,
    hu₃.trans (hu₂.trans (hun.trans hu₁)),by unfold generatedReplicaBoundaryFactoryCost; omega,
    Exec.seq he₁.toExec (Exec.seq he₂ he₃),?_,?_,?_,?_,?_,?_,hinput,houtput,hoff⟩
  · rw [hbankF]
    exact hdata
  · rw [←hbank,hbankF]
    exact hmasters
  · have hh := congrArg (fun C : Stacks 168 A => (C.R 118).length) hbank
    rw [hbankF] at hh
    exact hh.symm.trans hstage
  · have hh := congrArg (fun C : Stacks 168 A => (C.R 120).length) hbank
    rw [hbankF] at hh
    exact hh.symm.trans hlevel
  · intro k hk
    have hh := congrArg (fun C : Stacks 168 A => C.R k) hbank
    rw [hbankF] at hh
    exact hh.symm.trans (hgeometry k hk)
  · refine Stacks.ext hinput houtput ?_ ?_ <;> funext k
    · exact (hoff _ (fun i => replicaRecoveryCallerFactoryReg_gather i k)).1
    · exact (hoff _ (fun i => replicaRecoveryCallerFactoryReg_gather i k)).2

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
