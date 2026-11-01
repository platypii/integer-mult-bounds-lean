module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyReplicaHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingHeaderData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaHaloProblem

/-! Reload the coupling ABI from untouched gather metadata, using the same
structural header copier as the interior factory. The original RHS survives. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def reloadReplicaCouplingHeaders (plan : ReplicaInteriorPlacement T) : Pr P T Q A U :=
  copyReplicaHeaders plan replicaCouplingHeaderCopies

theorem ReplicaLoopHeaders.coupling_masters (H : ReplicaHaloProblem s)
    (plan : ReplicaInteriorPlacement T) (buffers : ReplicaLoopBuffers A) (S : Stacks T A)
    (h : ReplicaLoopHeaders H plan.gather buffers S) :
    ∀ r ∈ replicaCouplingHeaderCopies, (S.R (plan.gather r.1)).length =
      replicaCouplingMasterValue (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span) r.1 := by
  intro r hr
  simp only [replicaCouplingHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [replicaCouplingMasterValue,replicaFactoryHeaderValue] using h.masters (114,114) (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide)
  · simpa [replicaCouplingMasterValue,replicaFactoryHeaderValue] using h.masters (112,112) (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide)
  · simpa [replicaCouplingMasterValue,replicaFactoryHeaderValue] using h.masters (99,99) (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide)
  · simpa [replicaCouplingMasterValue,replicaFactoryHeaderValue] using h.masters (97,97) (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide)
  · simpa [replicaCouplingMasterValue,replicaFactoryHeaderValue] using h.masters (98,98) (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide)
  · simpa [replicaCouplingMasterValue,replicaFactoryHeaderValue] using h.masters (100,100) (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide)
  · simpa [replicaCouplingMasterValue] using h.origin
  · simpa [replicaCouplingMasterValue] using h.endpoint
  · simpa [replicaCouplingMasterValue,replicaFactoryHeaderValue] using h.masters (94,94) (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide)

theorem reloadReplicaCouplingHeaders_exec_within (plan : ReplicaInteriorPlacement T)
    (P q w s t u band a b : ℕ) (borrowed output : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hbank : embStk weightCacheCoreReg (embStk plan.solver S) = releasedCellBank [] borrowed output S.inp S.out)
    (hmasters : ∀ r ∈ replicaCouplingHeaderCopies, (S.R (plan.gather r.1)).length =
      replicaCouplingMasterValue P q w s t u band a b r.1)
    (htmp : S.R (plan.gather 7) = []) (depth : ℕ) :
    let value := fun k => (S.R k).length
    let F := {S with R := unaryCopiesR value S.R (placedReplicaHeaderCopies plan replicaCouplingHeaderCopies)}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*replicaCouplingHeaderCost P q w s t u band a b) depth
        (reloadReplicaCouplingHeaders plan) (mk v S) (replicaCouplingHeaderCost P q w s t u band a b) (mk v' F) ∧
      CouplingReady P q w s t u band a b borrowed (embStk weightCacheCoreReg (embStk plan.solver F)) ∧
      embStk plan.gather F = embStk plan.gather S ∧ F.L = S.L ∧
      ∀ k, (∀ r ∈ replicaCouplingHeaderCopies, plan.solver (weightCacheCoreReg r.2) ≠ k) → F.R k = S.R k := by
  dsimp only
  have havoid : ∀ r ∈ replicaCouplingHeaderCopies, r.1 ≠ 7 := by
    intro r hr
    simp only [replicaCouplingHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨v',hu,he,hview,hgather,hleft,hframe⟩ := copyReplicaHeaders_exec_within (body := body) plan replicaCouplingHeaderCopies
    (replicaCouplingMasterValue P q w s t u band a b) havoid v S hmasters htmp depth
  have hc := (copyReplicaHeaders_cost plan replicaCouplingHeaderCopies
    (replicaCouplingMasterValue P q w s t u band a b) S hmasters).trans
      (replicaCouplingHeaderCopies_cost P q w s t u band a b)
  rw [hc] at he
  refine ⟨v',hu,he,?_,hgather,funext hleft,hframe⟩
  rw [hview,hbank]
  exact replicaCouplingUnaryBank_ready A P q w s t u band a b borrowed output S.inp S.out

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
