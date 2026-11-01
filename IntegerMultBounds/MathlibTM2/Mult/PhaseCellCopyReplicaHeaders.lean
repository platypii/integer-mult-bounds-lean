module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaInteriorPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedWeightCache
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedHeaderCopies

/-! One structural header-copy contract serves successive numerical phases.
The schedule is arbitrary; concrete header roles and bank data are supplied last. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def placedReplicaHeaderCopies (plan : ReplicaInteriorPlacement T) (rs : List (Fin 126 × Fin 117)) :=
  rs.map (fun r => (plan.gather r.1,plan.solver (weightCacheCoreReg r.2)))

def copyReplicaHeaders (plan : ReplicaInteriorPlacement T) (rs : List (Fin 126 × Fin 117)) : Pr P T Q A U :=
  copyUnaryHeaders (plan.gather 7) (placedReplicaHeaderCopies plan rs)

theorem copyReplicaHeaders_cost (plan : ReplicaInteriorPlacement T)
    (rs : List (Fin 126 × Fin 117)) (σ : Fin 126 → ℕ) (S : Stacks T A)
    (hmasters : ∀ r ∈ rs, (S.R (plan.gather r.1)).length = σ r.1) :
    copyUnaryHeadersCost (fun k => (S.R k).length) (placedReplicaHeaderCopies plan rs) =
      (rs.map (fun r => 4*σ r.1+4)).sum+1 := by
  simp only [copyUnaryHeadersCost,placedReplicaHeaderCopies,List.map_map]
  congr 2
  apply List.map_congr_left
  intro r hr
  dsimp only [Function.comp_apply]
  rw [hmasters r hr]

theorem copyReplicaHeaders_exec_within (plan : ReplicaInteriorPlacement T)
    (rs : List (Fin 126 × Fin 117)) (σ : Fin 126 → ℕ) (havoid : ∀ r ∈ rs, r.1 ≠ 7)
    (v : HS T Q A U) (S : Stacks T A)
    (hmasters : ∀ r ∈ rs, (S.R (plan.gather r.1)).length = σ r.1)
    (htmp : S.R (plan.gather 7) = []) (depth : ℕ) :
    let value := fun k => (S.R k).length
    let placed := placedReplicaHeaderCopies plan rs
    let F := {S with R := unaryCopiesR value S.R placed}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*copyUnaryHeadersCost value placed) depth
        (copyReplicaHeaders plan rs) (mk v S) (copyUnaryHeadersCost value placed) (mk v' F) ∧
      embStk weightCacheCoreReg (embStk plan.solver F) =
        {embStk weightCacheCoreReg (embStk plan.solver S) with
          R := unaryCopiesR σ (embStk weightCacheCoreReg (embStk plan.solver S)).R rs} ∧
      embStk plan.gather F = embStk plan.gather S ∧
      (∀ k, F.L k = S.L k) ∧
      ∀ k, (∀ r ∈ rs, plan.solver (weightCacheCoreReg r.2) ≠ k) → F.R k = S.R k := by
  dsimp only
  let e := fun k => plan.solver (weightCacheCoreReg k)
  have he : Function.Injective e := plan.solver_injective.comp weightCacheCoreReg_injective
  let placed := placedReplicaHeaderCopies plan rs
  let value := fun k => (S.R k).length
  let F : Stacks T A := {S with R := unaryCopiesR value S.R placed}
  have hregs : ∀ r ∈ placed, [r.1,r.2,plan.gather 7].Nodup := by
    intro r hr
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
    have hgs := plan.disjoint p.1 (weightCacheCoreReg p.2)
    have hgt := plan.gather_injective.ne (havoid p hp)
    have hst := (plan.disjoint 7 (weightCacheCoreReg p.2)).symm
    simp [List.nodup_cons,hgs,hgt,hst]
  have hsep : ∀ r ∈ placed, ∀ p ∈ placed, r.2 ≠ p.1 := by
    intro r hr p hp
    obtain ⟨r',hr',rfl⟩ := List.mem_map.mp hr
    obtain ⟨p',hp',rfl⟩ := List.mem_map.mp hp
    exact (plan.disjoint p'.1 (weightCacheCoreReg r'.2)).symm
  obtain ⟨v',hu,hex⟩ := copyUnaryHeaders_exec (body := body) (plan.gather 7) placed hregs hsep value v S
    (by intro r hr; rfl) htmp
  have hproj := unaryCopiesR_project plan.gather e he value σ rs hmasters S.R
  have hoff (k : Fin T) (hk : ∀ r ∈ rs, e r.2 ≠ k) : F.R k = S.R k := by
    apply unaryCopiesR_off
    intro r hr
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
    exact hk p hp
  refine ⟨v',hu,mn_native_exec_within hex 2 (copyUnaryHeaders_native _ _) depth _ (le_refl _),?_,?_,
    (by intro k; rfl),hoff⟩
  · refine Stacks.ext rfl rfl rfl ?_
    exact hproj
  · refine Stacks.ext rfl rfl rfl ?_
    funext k
    exact hoff _ (fun r _ => (plan.disjoint k (weightCacheCoreReg r.2)).symm)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
