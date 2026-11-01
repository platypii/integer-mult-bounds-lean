module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedRecoveryPlan

/-! Complex pairing reuses five cleared recovery work registers and three
retained masters. Placement is structural; no full-bank case analysis is used. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
namespace ComputedRecoveryPlan
variable {T : ℕ}

def pairMasterIndex : Fin 3 → Fin 10 := ![2,8,9]
theorem pairMasterIndex_injective : Function.Injective pairMasterIndex := by decide

def pairPlacement (plan : ComputedRecoveryPlan T) (i : Fin 8) : Fin T :=
  if h : i.val < 3 then plan.master.masters (pairMasterIndex ⟨i.val,h⟩)
  else plan.work ⟨i.val,by omega⟩

theorem pairPlacement_injective (plan : ComputedRecoveryPlan T) : Function.Injective plan.pairPlacement := by
  intro i j hij
  by_cases hi : i.val < 3 <;> by_cases hj : j.val < 3
  · simp only [pairPlacement,hi,hj,dite_true] at hij
    exact Fin.ext (congrArg (fun k : Fin 3 => k.val) (pairMasterIndex_injective (plan.master.masters_injective hij)))
  · simp only [pairPlacement,hi,hj,dite_true,dite_false] at hij
    exact False.elim (plan.master_work _ _ hij)
  · simp only [pairPlacement,hi,hj,dite_true,dite_false] at hij
    exact False.elim (plan.master_work _ _ hij.symm)
  · simp only [pairPlacement,hi,hj,dite_false] at hij
    exact Fin.ext (congrArg (fun k : Fin 392 => k.val) (plan.work_injective hij))

theorem pairPlacement_masters (plan : ComputedRecoveryPlan T) :
    plan.pairPlacement 0 = plan.master.masters 2 ∧ plan.pairPlacement 1 = plan.master.masters 8 ∧
      plan.pairPlacement 2 = plan.master.masters 9 := ⟨rfl,rfl,rfl⟩

theorem pairPlacement_work (plan : ComputedRecoveryPlan T) (k : Fin 8)
    (hk : k ∈ ([(3 : Fin 8),4,5,6,7])) : plan.pairPlacement k ∈ List.ofFn plan.work := by
  have hlarge : ¬ k.val < 3 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [pairPlacement,hlarge,dite_false]
  exact List.mem_ofFn.mpr ⟨_,rfl⟩

theorem pairPlacement_regs (plan : ComputedRecoveryPlan T)
    (hcount : plan.replicas ≠ plan.count) (hspare : plan.replicas ≠ plan.spare) :
    [plan.replicas,plan.pairPlacement 5,plan.count,plan.result,plan.spare,
      plan.pairPlacement 7,plan.pairPlacement 6].Nodup := by
  change [plan.replicas,plan.work 5,plan.count,plan.result,plan.spare,plan.work 7,plan.work 6].Nodup
  have hr := plan.regs
  regs_ne hr
  have hwork (i : Fin 392) (k : Fin T)
      (hk : k ∈ [plan.count,plan.result,plan.spare]) : plan.work i ≠ k := by
    intro hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl <;> exact plan.separate i (by simp [hi])
  have hrep (i : Fin 392) := (plan.seed_work i).2.2
  have hbank (i j : Fin 392) (hij : i ≠ j) : plan.work i ≠ plan.work j :=
    fun h => hij (plan.work_injective h)
  have h57 := hbank 5 7 (by decide)
  have h56 := hbank 5 6 (by decide)
  have h76 := hbank 7 6 (by decide)
  have h5count := hwork 5 plan.count (by simp)
  have h5result := hwork 5 plan.result (by simp)
  have h5spare := hwork 5 plan.spare (by simp)
  have h7count := hwork 7 plan.count (by simp)
  have h7result := hwork 7 plan.result (by simp)
  have h7spare := hwork 7 plan.spare (by simp)
  have h6count := hwork 6 plan.count (by simp)
  have h6result := hwork 6 plan.result (by simp)
  have h6spare := hwork 6 plan.spare (by simp)
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or]
  repeat' constructor
  all_goals solve
    | assumption
    | exact Ne.symm (by assumption)
    | exact plan.seed_result.2.2
    | exact hrep _
    | simp


end ComputedRecoveryPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
