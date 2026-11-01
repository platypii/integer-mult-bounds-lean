module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryCropPlacement

/-! Whole-packet order restoration reuses the crop bank and retained word width.
Only small role selectors are checked; ambient-bank injection stays structural. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
namespace RecoveryCropPlacement
variable {T : ℕ} {plan : ComputedRecoveryPlan T}

def orderCropIndex : Fin 13 → Fin 19 := ![4,5,6,7,8,12,11,9,10,13,14,15,16]
def orderRole : Fin 14 → Sum Unit (Fin 13) := ![
  .inr 0,.inl (),.inr 1,.inr 2,.inr 3,.inr 4,.inr 5,.inr 6,
  .inr 7,.inr 8,.inr 9,.inr 10,.inr 11,.inr 12]

theorem orderCropIndex_injective : Function.Injective orderCropIndex := by decide +kernel
theorem orderRole_injective : Function.Injective orderRole := by decide +kernel

def orderPlacement (crop : RecoveryCropPlacement plan) : Fin 14 → Fin T :=
  (Sum.elim (fun _ : Unit => plan.packet) (crop.reg ∘ orderCropIndex)) ∘ orderRole

theorem orderPlacement_injective (crop : RecoveryCropPlacement plan)
    (hrows : plan.packet ≠ crop.reg 4) (hreplicas : plan.packet ≠ plan.replicas)
    (hdestination : plan.packet ≠ crop.reg 12) : Function.Injective crop.orderPlacement := by
  have hwork (i : Fin 19) (hi : i ∈ ([(6 : Fin 19),7,8,9,10,13,14,15,16,17,18])) :
      plan.packet ≠ crop.reg i := by
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp (crop.scratch i hi)
    rw [←hj]
    exact (plan.seed_work j).2.1
  have hsep (u : Unit) (i : Fin 13) : plan.packet ≠ (crop.reg ∘ orderCropIndex) i := by
    fin_cases i
    · exact hrows
    · change plan.packet ≠ crop.reg 5
      rw [crop.replicas]; exact hreplicas
    · exact hwork 6 (by simp)
    · exact hwork 7 (by simp)
    · exact hwork 8 (by simp)
    · exact hdestination
    · change plan.packet ≠ crop.reg 11
      rw [crop.source]; exact plan.seed_result.2.1
    · exact hwork 9 (by simp)
    · exact hwork 10 (by simp)
    · exact hwork 13 (by simp)
    · exact hwork 14 (by simp)
    · exact hwork 15 (by simp)
    · exact hwork 16 (by simp)
  have hu : Function.Injective (fun _ : Unit => plan.packet) := by intro i j _; cases i; cases j; rfl
  exact (hu.sumElim (crop.injective.comp orderCropIndex_injective) hsep).comp orderRole_injective

theorem orderPlacement_ports (crop : RecoveryCropPlacement plan) :
    crop.orderPlacement 0 = crop.reg 4 ∧ crop.orderPlacement 1 = plan.packet ∧
    crop.orderPlacement 2 = plan.replicas ∧ crop.orderPlacement 6 = crop.reg 12 ∧
    crop.orderPlacement 7 = plan.result := by
  exact ⟨rfl,rfl,crop.replicas,rfl,crop.source⟩

theorem orderPlacement_scratch (crop : RecoveryCropPlacement plan) (k : Fin 14)
    (hk : k ∈ ([(3 : Fin 14),4,5,8,9,10,11,12,13])) :
    crop.orderPlacement k ∈ List.ofFn plan.work := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact crop.scratch _ (by simp [orderCropIndex])

theorem orderPlacement_outside (crop : RecoveryCropPlacement plan) (k : Fin 14)
    (hk : k ∈ ([(0 : Fin 14),1,2,7])) : crop.orderPlacement k ∉ List.ofFn plan.work := by
  have hp := crop.orderPlacement_ports
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact (crop.external 4 (by simp)).1
  · intro hm
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hm
    exact (plan.seed_work j).2.1 hj.symm
  · rw [hp.2.2.1]
    intro hm
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hm
    exact (plan.seed_work j).2.2 hj.symm
  · rw [hp.2.2.2.2]
    intro hm
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hm
    exact plan.separate j (by simp [hj])

end RecoveryCropPlacement
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
