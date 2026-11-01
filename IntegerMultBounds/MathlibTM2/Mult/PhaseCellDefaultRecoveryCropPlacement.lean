module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryCropPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryPairPlacement

/-! Crop placement reuses the existing banks. A small role selector is checked
last, after structural injection and separation of the banks are proved. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
namespace RecoveryCropPlacement
variable {T : ℕ}

abbrev CropPort := Sum (Fin 3) (Sum (Fin 3) (Sum (Fin 2) (Fin 392)))

def cropPort : Fin 19 → CropPort := ![
  .inl 0,.inl 1,.inl 2,.inr (.inl 0),.inr (.inl 1),.inr (.inr (.inl 0)),
  .inr (.inr (.inr 6)),.inr (.inr (.inr 7)),.inr (.inr (.inr 8)),
  .inr (.inr (.inr 9)),.inr (.inr (.inr 10)),.inr (.inr (.inl 1)),.inr (.inl 2),
  .inr (.inr (.inr 13)),.inr (.inr (.inr 14)),.inr (.inr (.inr 15)),
  .inr (.inr (.inr 16)),.inr (.inr (.inr 17)),.inr (.inr (.inr 18))]

theorem cropPort_injective : Function.Injective cropPort := by decide +kernel

theorem cropPort_work : ∀ k : Fin 19, k ∈ ([(6 : Fin 19),7,8,9,10,13,14,15,16,17,18]) →
    cropPort k = .inr (.inr (.inr (Fin.castLE (by decide) k))) := by decide +kernel

/-- Only the offset, row-count and destination ports are external. All other
ports come from the existing numerical masters, controls and cleared work. -/
def ofBanks (plan : ComputedRecoveryPlan T) (external : Fin 3 → Fin T)
    (hinj : Function.Injective external)
    (hmasters : ∀ i j, external i ≠ plan.master.masters j)
    (hwork : ∀ i j, external i ≠ plan.work j)
    (hcontrols : ∀ i, external i ≠ plan.replicas ∧ external i ≠ plan.result) : RecoveryCropPlacement plan := by
  let controls : Fin 2 → Fin T := ![plan.replicas,plan.result]
  have hc : Function.Injective controls := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (plan.seed_result.2.2 hij)
    · exact False.elim (plan.seed_result.2.2 hij.symm)
    · rfl
  have hcw (i : Fin 2) (j : Fin 392) : controls i ≠ plan.work j := by
    fin_cases i
    · exact (plan.seed_work j).2.2
    · intro h
      change plan.result = plan.work j at h
      exact plan.separate j (by simp [h.symm])
  let inner := Sum.elim controls plan.work
  have hi : Function.Injective inner := hc.sumElim plan.work_injective hcw
  have hei (i : Fin 3) (j : Sum (Fin 2) (Fin 392)) : external i ≠ inner j := by
    cases j with
    | inl j => fin_cases j; exact (hcontrols i).1; exact (hcontrols i).2
    | inr j => exact hwork i j
  let rest := Sum.elim external inner
  have hr : Function.Injective rest := hinj.sumElim hi hei
  let masters := fun i => plan.master.masters (ComputedRecoveryPlan.pairMasterIndex i)
  have hm : Function.Injective masters := plan.master.masters_injective.comp
    ComputedRecoveryPlan.pairMasterIndex_injective
  have hmr (i : Fin 3) (j : Sum (Fin 3) (Sum (Fin 2) (Fin 392))) : masters i ≠ rest j := by
    cases j with
    | inl j => exact (hmasters j _).symm
    | inr j =>
      cases j with
      | inl j =>
        fin_cases j
        · intro h
          change plan.master.masters (ComputedRecoveryPlan.pairMasterIndex i) = plan.replicas at h
          exact plan.master_seeds (ComputedRecoveryPlan.pairMasterIndex i) (by simp [h])
        · intro h
          change plan.master.masters (ComputedRecoveryPlan.pairMasterIndex i) = plan.result at h
          exact plan.master_controls (ComputedRecoveryPlan.pairMasterIndex i) (by simp [h])
      | inr j => exact plan.master_work _ j
  let ports := Sum.elim masters rest
  have hp : Function.Injective ports := hm.sumElim hr hmr
  refine { reg := ports ∘ cropPort
           injective := hp.comp cropPort_injective
           masters := ⟨rfl,rfl,rfl⟩
           replicas := rfl
           source := rfl
           scratch := ?_
           external := ?_ }
  · intro k hk
    change ports (cropPort k) ∈ List.ofFn plan.work
    rw [cropPort_work k hk]
    exact List.mem_ofFn.mpr ⟨_,rfl⟩
  · intro k hk
    have hext (i : Fin 3) : external i ∉ List.ofFn plan.work ∧
        (∀ j, plan.master.masters j ≠ external i) ∧ external i ≠ plan.result := by
      refine ⟨?_,fun j => (hmasters i j).symm,(hcontrols i).2⟩
      intro h
      obtain ⟨j,hj⟩ := List.mem_ofFn.mp h
      exact hwork i j hj.symm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl
    · exact hext 0
    · exact hext 1
    · exact hext 2

/-- The three external headers/streams keep their ordinary caller-facing ports. -/
theorem ofBanks_external (plan : ComputedRecoveryPlan T) (external : Fin 3 → Fin T)
    (hinj : Function.Injective external)
    (hmasters : ∀ i j, external i ≠ plan.master.masters j)
    (hwork : ∀ i j, external i ≠ plan.work j)
    (hcontrols : ∀ i, external i ≠ plan.replicas ∧ external i ≠ plan.result) (i : Fin 3) :
    (ofBanks plan external hinj hmasters hwork hcontrols).reg (![3,4,12] i) = external i := by
  fin_cases i <;> rfl

end RecoveryCropPlacement
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
