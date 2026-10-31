module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaFactoryHeaderData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaInteriorPlacement

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
  let e := fun k => plan.solver (weightCacheCoreReg k)
  have he : Function.Injective e := plan.solver_injective.comp weightCacheCoreReg_injective
  let rs := placedReplicaFactoryHeaderCopies plan
  let value := fun k => (S.R k).length
  let σ := replicaFactoryHeaderValue P stage q l s t u band N B L w
  let F : Stacks T A := {S with R := unaryCopiesR value S.R rs}
  have hsourceNe : ∀ r ∈ replicaFactoryHeaderCopies, r.1 ≠ 7 := by
    intro r hr
    simp only [replicaFactoryHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hregs : ∀ r ∈ rs, [r.1,r.2,plan.gather 7].Nodup := by
    intro r hr
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
    have hgs := plan.disjoint p.1 (weightCacheCoreReg p.2)
    have hgt := plan.gather_injective.ne (hsourceNe p hp)
    have hst := (plan.disjoint 7 (weightCacheCoreReg p.2)).symm
    simp [List.nodup_cons,hgs,hgt,hst]
  have hsep : ∀ r ∈ rs, ∀ p ∈ rs, r.2 ≠ p.1 := by
    intro r hr p hp
    obtain ⟨r',hr',rfl⟩ := List.mem_map.mp hr
    obtain ⟨p',hp',rfl⟩ := List.mem_map.mp hp
    exact (plan.disjoint p'.1 (weightCacheCoreReg r'.2)).symm
  obtain ⟨v',hu,hex⟩ := copyUnaryHeaders_exec (body := body) (plan.gather 7) rs hregs hsep value v S
    (by intro r hr; rfl) htmp
  have hproj := unaryCopiesR_project plan.gather e he value σ replicaFactoryHeaderCopies hmasters S.R
  have hR : S.R ∘ e = (releasedCellBank [] borrowed output S.inp S.out).R := congrArg Stacks.R hbank
  have hfinal : embStk weightCacheCoreReg (embStk plan.solver F) =
      replicaFactoryUnaryBank A P stage q l s t u band N B L w borrowed output S.inp S.out := by
    refine Stacks.ext rfl rfl ?_ ?_
    · have hh := congrArg Stacks.L hbank
      simpa only [F,embStk,replicaFactoryUnaryBank] using hh
    · change unaryCopiesR value S.R rs ∘ e = unaryCopiesR σ (releasedCellBank [] borrowed output S.inp S.out).R replicaFactoryHeaderCopies
      have hp : unaryCopiesR value S.R rs ∘ e = unaryCopiesR σ (S.R ∘ e) replicaFactoryHeaderCopies := hproj
      rw [hp,hR]
  refine ⟨v',hu,mn_native_exec_within hex 2 (copyUnaryHeaders_native _ _) depth _ (le_refl _),hfinal,
    (by intro k; rfl),?_⟩
  intro k hk
  apply unaryCopiesR_off
  intro r hr
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
  exact hk p hp

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
