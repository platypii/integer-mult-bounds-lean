module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaFactoryHeaderData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyReplicaHeaders

/-! Install ordinary numerical factory headers from the retained gather bank.
The generic structural copier restores all masters and private scratch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}

def placedReplicaFactoryHeaderCopies (plan : ReplicaInteriorPlacement T) :=
  replicaFactoryHeaderCopies.map (fun r => (plan.gather r.1,plan.solver (weightCacheCoreReg r.2)))

def reloadReplicaFactoryHeaders (plan : ReplicaInteriorPlacement T) : Pr P₀ T Q A U :=
  copyUnaryHeaders (plan.gather 7) (placedReplicaFactoryHeaderCopies plan)

theorem reloadReplicaFactoryHeaders_exec_within (plan : ReplicaInteriorPlacement T)
    (P stage q l s t u band N B L w : ℕ)
    (borrowed output : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hbank : embStk weightCacheCoreReg (embStk plan.solver S) = releasedCellBank [] borrowed output S.inp S.out)
    (hmasters : ∀ r ∈ replicaFactoryHeaderCopies, (S.R (plan.gather r.1)).length =
      replicaFactoryHeaderValue P stage q l s t u band N B L w r.1)
    (htmp : S.R (plan.gather 7) = []) (depth : ℕ) :
    let value := fun k => (S.R k).length
    let rs := placedReplicaFactoryHeaderCopies plan
    let F := {S with R := unaryCopiesR value S.R rs}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*copyUnaryHeadersCost value rs) depth
        (reloadReplicaFactoryHeaders plan) (mk v S) (copyUnaryHeadersCost value rs) (mk v' F) ∧
      embStk weightCacheCoreReg (embStk plan.solver F) =
        replicaFactoryUnaryBank A P stage q l s t u band N B L w borrowed output S.inp S.out ∧
      (∀ k, F.L k = S.L k) ∧
      ∀ k, (∀ r ∈ replicaFactoryHeaderCopies, plan.solver (weightCacheCoreReg r.2) ≠ k) → F.R k = S.R k := by
  dsimp only
  have havoid : ∀ r ∈ replicaFactoryHeaderCopies, r.1 ≠ 7 := by
    intro r hr
    simp only [replicaFactoryHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨v',hu,he,hview,hgather,hleft,hframe⟩ := copyReplicaHeaders_exec_within (body := body) plan replicaFactoryHeaderCopies
    (replicaFactoryHeaderValue P stage q l s t u band N B L w) havoid v S hmasters htmp depth
  refine ⟨v',hu,he,?_,hleft,hframe⟩
  rw [hbank] at hview
  exact hview

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
