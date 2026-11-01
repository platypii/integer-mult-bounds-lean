module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallPackedFactoryStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryFactory
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingRecoveryFrame

/-! Instantiate the existing physical factory installer at the shared replica
bank, reading ordinary masters directly from the retained gather headers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 389 Q A U}

def replicaRecoveryCallerFactoryReg (i : Fin 242) : Fin 389 :=
  replicaRecoveryCallerNativeReg (packedBoundaryRecoveryBase i)

theorem replicaRecoveryCallerFactoryReg_injective : Function.Injective replicaRecoveryCallerFactoryReg :=
  replicaRecoveryCallerNativeReg_injective.comp (Fin.castLE_injective (by decide : 242 ≤ 248))

theorem replicaRecoveryCallerFactoryReg_gather (i : Fin 242) (j : Fin 126) :
    replicaRecoveryCallerFactoryReg i ≠ replicaRecoveryCallerInterior.gather j :=
  replicaRecoveryCallerReg_worker_gather_disjoint (Fin.castLE (by decide) i) j

def replicaBoundaryFactoryMasterSource : Fin 10 → Fin 389 :=
  fun i => replicaRecoveryCallerInterior.gather (![114,101,112,108,97,98,99,100,111,113] i)

theorem ReplicaLoopHeaders.boundary_factory_masters (H : ReplicaHaloProblem s)
    (buffers : ReplicaLoopBuffers A) (S : Stacks 389 A)
    (h : ReplicaLoopHeaders H replicaRecoveryCallerInterior.gather buffers S) (i : Fin 10) :
    (S.R (replicaBoundaryFactoryMasterSource i)).length =
      masterHeaderValues (2^15*H.p) (H.stage+1) H.precision H.l s H.t H.u H.band H.origin (H.origin+H.span) i := by
  fin_cases i
  · simpa [replicaBoundaryFactoryMasterSource,masterHeaderValues,replicaFactoryHeaderValue] using
      h.masters (114,114) (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide)
  · simpa [replicaBoundaryFactoryMasterSource,masterHeaderValues,replicaFactoryHeaderValue] using
      h.masters (101,101) (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide)
  · simpa [replicaBoundaryFactoryMasterSource,masterHeaderValues,replicaFactoryHeaderValue] using
      h.masters (112,112) (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide)
  · simpa [replicaBoundaryFactoryMasterSource,masterHeaderValues,replicaFactoryHeaderValue] using
      h.masters (108,109) (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide)
  · simpa [replicaBoundaryFactoryMasterSource,masterHeaderValues,replicaFactoryHeaderValue] using
      h.masters (97,97) (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide)
  · simpa [replicaBoundaryFactoryMasterSource,masterHeaderValues,replicaFactoryHeaderValue] using
      h.masters (98,98) (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide)
  · simpa [replicaBoundaryFactoryMasterSource,masterHeaderValues,replicaFactoryHeaderValue] using
      h.masters (99,99) (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide)
  · simpa [replicaBoundaryFactoryMasterSource,masterHeaderValues,replicaFactoryHeaderValue] using
      h.masters (100,100) (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide)
  · exact h.origin
  · exact h.endpoint

def installReplicaBoundaryFactory : Pr P 389 Q A U :=
  installPackedFactory replicaRecoveryCallerFactoryReg replicaBoundaryFactoryMasterSource
    119 102 104 105 105

def replicaBoundaryFactoryInstalled (H : ReplicaHaloProblem s) (S : Stacks 389 A) : Stacks 389 A :=
  let rs := masterHeaderCopies (replicaRecoveryCallerFactoryReg ∘ packedFactoryNativeReg) replicaBoundaryFactoryMasterSource
  let M := {S with R := unaryCopiesR (fun i => (S.R i).length) S.R rs}
  {M with R := (Function.update (Function.update (Function.update M.R (replicaRecoveryCallerFactoryReg 163)
    (List.replicate (publicationGeometryWidth H.t H.band) tick)) (replicaRecoveryCallerFactoryReg 155)
    (binSyms (publicationGeometryWidth H.t H.band) H.origin)) (replicaRecoveryCallerFactoryReg 165)
    (binSyms (publicationGeometryWidth H.t H.band) H.span))}

def replicaBoundaryFactoryMasterCost (H : ReplicaHaloProblem s) :=
  ((List.ofFn (fun i : Fin 10 => 4*masterHeaderValues (2^15*H.p) (H.stage+1) H.precision H.l
    s H.t H.u H.band H.origin (H.origin+H.span) i+4)).sum+1)

def installReplicaBoundaryFactoryCost (H : ReplicaHaloProblem s) :=
  replicaBoundaryFactoryMasterCost H+factoryGeometryCost H.origin (H.origin+H.span) (publicationGeometryWidth H.t H.band)

theorem replicaBoundaryFactoryInstalled_frame (H : ReplicaHaloProblem s) (S : Stacks 389 A)
    (k : Fin 389) (hoff : ∀ i, replicaRecoveryCallerFactoryReg i ≠ k) :
    (replicaBoundaryFactoryInstalled H S).L k = S.L k ∧
      (replicaBoundaryFactoryInstalled H S).R k = S.R k := by
  refine ⟨rfl,?_⟩
  unfold replicaBoundaryFactoryInstalled
  change Function.update (Function.update (Function.update _ _ _) _ _) _ _ _ = _
  rw [Function.update_of_ne (hoff 165).symm,Function.update_of_ne (hoff 155).symm,
    Function.update_of_ne (hoff 163).symm]
  apply unaryCopiesR_off
  intro r hr he
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
  exact hoff _ he

theorem replicaBoundaryFactoryInstalled_gather (H : ReplicaHaloProblem s) (S : Stacks 389 A) :
    embStk replicaRecoveryCallerInterior.gather (replicaBoundaryFactoryInstalled H S) =
      embStk replicaRecoveryCallerInterior.gather S := by
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  exact (replicaBoundaryFactoryInstalled_frame H S _ (fun i => replicaRecoveryCallerFactoryReg_gather i k)).2

theorem installReplicaBoundaryFactory_exec (H : ReplicaHaloProblem s) (buffers : ReplicaLoopBuffers A)
    (v : HS 389 Q A U) (S : Stacks 389 A)
    (headers : ReplicaLoopHeaders H replicaRecoveryCallerInterior.gather buffers S)
    (hwidth : (S.R 119).length = publicationGeometryWidth H.t H.band)
    (hblank : ∀ i, S.R (replicaRecoveryCallerFactoryReg i) = [])
    (hleft : ∀ i, S.L (replicaRecoveryCallerFactoryReg i) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ installReplicaBoundaryFactoryCost H ∧
      embStk replicaRecoveryCallerFactoryReg (replicaBoundaryFactoryInstalled H S) =
        replicaBoundaryFactoryInput H (embStk replicaRecoveryCallerFactoryReg S) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (2*replicaBoundaryFactoryMasterCost H+(8*H.origin+8*(H.origin+H.span)+
          24*publicationGeometryWidth H.t H.band+40))) depth
        installReplicaBoundaryFactory (mk v S) n (mk v' (replicaBoundaryFactoryInstalled H S)) := by
  have hoff (i : Fin 126) (j : Fin 242) : replicaRecoveryCallerInterior.gather i ≠ replicaRecoveryCallerFactoryReg j :=
    (replicaRecoveryCallerFactoryReg_gather j i).symm
  have hsourceTmp (i : Fin 10) : replicaBoundaryFactoryMasterSource i ≠ (104 : Fin 389) := by
    fin_cases i <;> decide
  let bank : Fin 126 ⊕ Fin 242 → Fin 389 := Sum.elim replicaRecoveryCallerInterior.gather replicaRecoveryCallerFactoryReg
  have hbank : Function.Injective bank := by
    intro i j he
    cases i with
    | inl i => cases j with
      | inl j => exact congrArg Sum.inl (replicaRecoveryCallerInterior.gather_injective he)
      | inr j => exact False.elim (hoff i j he)
    | inr i => cases j with
      | inl j => exact False.elim (hoff j i he.symm)
      | inr j => exact congrArg Sum.inr (replicaRecoveryCallerFactoryReg_injective he)
  have hgeometry : [replicaBoundaryFactoryMasterSource 8,replicaBoundaryFactoryMasterSource 9,(119 : Fin 389),
      replicaRecoveryCallerFactoryReg 155,replicaRecoveryCallerFactoryReg 165,replicaRecoveryCallerFactoryReg 163,102,104,105].Nodup := by
    exact List.Nodup.map hbank (by decide :
      ([.inl 111,.inl 113,.inl 119,.inr 155,.inr 165,.inr 163,.inl 102,.inl 104,.inl 105] : List (Fin 126 ⊕ Fin 242)).Nodup)
  obtain ⟨v',n,hu,hn,hview,he⟩ := installPackedFactory_exec_within (body := body)
    replicaRecoveryCallerFactoryReg replicaRecoveryCallerFactoryReg_injective replicaBoundaryFactoryMasterSource
    119 102 104 105 105 (fun i j => hoff _ j) hsourceTmp
    (fun i => replicaRecoveryCallerFactoryReg_gather i 104) hgeometry
    (2^15*H.p) (H.stage+1) H.precision H.l s H.t H.u H.band H.origin (H.origin+H.span)
    (publicationGeometryWidth H.t H.band) v S (headers.boundary_factory_masters H buffers S)
    hwidth (hoff 119) hblank hleft
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl
      · exact headers.fresh 102 (by simp)
      · exact headers.fresh 104 (by simp)
      · exact headers.fresh 105 (by simp))
    (by
      intro k hk j
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl
      · exact hoff 102 j
      · exact hoff 104 j
      · exact hoff 105 j) depth
  have hcost : copyUnaryHeadersCost (fun i => (S.R i).length)
      (masterHeaderCopies (replicaRecoveryCallerFactoryReg ∘ packedFactoryNativeReg) replicaBoundaryFactoryMasterSource) =
      replicaBoundaryFactoryMasterCost H := by
    unfold copyUnaryHeadersCost masterHeaderCopies replicaBoundaryFactoryMasterCost
    simp only [List.map_ofFn,Function.comp_def,headers.boundary_factory_masters H buffers S]
  rw [hcost] at hn he
  have hend : (H.origin+H.span)-H.origin = H.span := by omega
  simp only [hend] at hview he
  exact ⟨v',n,hu,hn,hview,he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
