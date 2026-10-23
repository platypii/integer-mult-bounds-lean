module

public import IntegerMultBounds.MathlibTM2.Routing.SourceRegionDispatch
public import IntegerMultBounds.MathlibTM2.Routing.ReservoirPlacement
public import IntegerMultBounds.MathlibTM2.Routing.ReservoirPartition

/-! Choose a matching edge's reservoir class by two live interval classifiers.
Only the first two reservoir intervals are needed for first-available choice. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def reservoirRegionChoice (r s : Fin 3) : Fin 3 :=
  if r ≠ 0 ∧ s ≠ 0 then 0 else if r ≠ 1 ∧ s ≠ 1 then 1 else 2

def reservoirEndpointRegisters (rg : Fin 8 → Fin T) (second : Bool) : Fin 7 → Fin T :=
  fun j => rg (if j = 0 then (if second then 1 else 0) else j.succ)

theorem reservoirEndpointRegisters_injective (rg : Fin 8 → Fin T) (hrg : Function.Injective rg)
    (second : Bool) : Function.Injective (reservoirEndpointRegisters rg second) := by
  apply hrg.comp
  cases second <;> decide +kernel

def reservoirClassDispatchProgram (rg : Fin 8 → Fin T) (branch : Fin 3 → Pr P T Q A U) : Pr P T Q A U :=
  sourceRegionDispatchProgram (reservoirEndpointRegisters rg false) (fun r =>
    sourceRegionDispatchProgram (reservoirEndpointRegisters rg true) (fun s => branch (reservoirRegionChoice r s)))

theorem reservoirClassDispatch_exec (body : P → Pr P T Q A U)
    (rg : Fin 8 → Fin T) (hrg : Function.Injective rg)
    (branch : Fin 3 → Pr P T Q A U) (L q mate low high C : ℕ)
    (hq : q < 2 ^ L) (hmate : mate < 2 ^ L) (hlow : low < 2 ^ L) (hhigh : high < 2 ^ L)
    (v : HS T Q A U) (S S' : Stacks T A)
    (hqInput : S.R (rg 0) = binSyms L q) (hmateInput : S.R (rg 1) = binSyms L mate)
    (hlowInput : S.R (rg 2) = binSyms L low) (hhighInput : S.R (rg 3) = binSyms L high)
    (hblank : ∀ j : Fin 8, j = 4 ∨ j = 5 ∨ j = 6 → S.R (rg j) = [])
    (hbranch : ∀ u : HS T Q A U, ∃ (u' : HS T Q A U) (steps : ℕ), u'.user = u.user ∧ steps ≤ C ∧
      Exec body (branch (reservoirRegionChoice (sourceRegionIndex q low high) (sourceRegionIndex mate low high)))
        (mk u S) steps (mk u' S')) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ 32 * L + 36 + C ∧
      Exec body (reservoirClassDispatchProgram rg branch) (mk v S) steps (mk v' S') := by
  obtain ⟨v', steps, hu, hm, he⟩ := sourceRegionDispatch_exec body
    (reservoirEndpointRegisters rg false) (reservoirEndpointRegisters_injective rg hrg false)
    (fun r => sourceRegionDispatchProgram (reservoirEndpointRegisters rg true)
      (fun s => branch (reservoirRegionChoice r s))) L q low high (16 * L + 18 + C)
    hq hlow hhigh v S S' hqInput hlowInput hhighInput
    (by intro j hj; rcases hj with rfl | rfl | rfl <;> exact hblank _ (by simp))
    (fun u => sourceRegionDispatch_exec body (reservoirEndpointRegisters rg true)
      (reservoirEndpointRegisters_injective rg hrg true)
      (fun s => branch (reservoirRegionChoice (sourceRegionIndex q low high) s))
      L mate low high C hmate hlow hhigh u S S' hmateInput hlowInput hhighInput
      (by intro j hj; rcases hj with rfl | rfl | rfl <;> exact hblank _ (by simp)) hbranch)
  exact ⟨v', steps, hu, by omega, he⟩

theorem sourceRegionIndex_ne_zero (q low high : ℕ) :
    sourceRegionIndex q low high ≠ 0 ↔ low ≤ q := by
  unfold sourceRegionIndex
  split_ifs <;> simp_all

theorem sourceRegionIndex_ne_one (q low high : ℕ) :
    sourceRegionIndex q low high ≠ 1 ↔ q < low ∨ high ≤ q := by
  unfold sourceRegionIndex
  split_ifs <;> simp_all

theorem reservoirRegionChoice_eq (n H : ℕ) (hfit : 9 * H ≤ n) (q mate : Fin n) :
    reservoirRegionChoice (sourceRegionIndex q.val (3 * H) (6 * H))
      (sourceRegionIndex mate.val (3 * H) (6 * H)) =
      reservoirChoice (routingReservoir n H hfit) q mate := by
  have hzero (i : Fin n) : i ∉ routingReservoir n H hfit 0 ↔ 3 * H ≤ i.val := by
    rw [routingReservoir_mem_iff]
    simp
  have hone (i : Fin n) : i ∉ routingReservoir n H hfit 1 ↔ i.val < 3 * H ∨ 6 * H ≤ i.val := by
    rw [routingReservoir_mem_iff]
    simp only [Fin.val_one, one_mul]
    omega
  simp only [reservoirRegionChoice, reservoirChoice, sourceRegionIndex_ne_zero,
    sourceRegionIndex_ne_one, hzero, hone]

end IntegerMultBounds.MathlibTM2.Routing
