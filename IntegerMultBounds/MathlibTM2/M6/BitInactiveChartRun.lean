module

public import IntegerMultBounds.MathlibTM2.M6.BitHelperChartRun
public import IntegerMultBounds.MathlibTM2.M6.BitSweepNodeAddress

/-! Identify the costed flat owner route with the inactive sweep address. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Certificates.PR589 Certificates.PR589.Nine
open Shared50ModularControl (prime)
open M8.RevMachine
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

theorem inactiveChart_owner [M8.Machine.Net] (n : Fin 9) (r : Role)
    (inactive : r.bank.val / 2 ≠ BitHosting.activePair n.val) (backward : Bool := false) :
    ∃ (a k : ℕ) (machine : SharedBankSkeleton.Skeleton 1 prime), ∀ w W, 0 < w → 0 < W →
      let V := (prime^w)^128*W
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = machine ∧
        stage.cost = a*V+k*(3808274*V+LeafCore.coreCost V w+1)+2 ∧
        HasStackSeed stage.metadata ∧ ∀ x i,
          routedCell backward x (stage.transform x) i ((flatToSweep w W n r i).cast
            (by simpa only [Nat.one_mul] using ordinaryCompact_width (prime^w) W)) := by
  obtain ⟨a,k,m,build⟩ := helperChart_owner (port r.port.val) (port_checked _ r.port.isLt) none backward
  refine ⟨a,k,m,?_⟩
  intro w W hw hW V
  obtain ⟨stage,fixed,cost,seed,read⟩ := build w W hw hW
  refine ⟨stage,fixed,cost,seed,?_⟩
  intro x i
  obtain ⟨⟨s,j⟩,rfl⟩ := (flatWindowEquiv w W).surjective i
  simp only [flatToSweep,Equiv.trans_apply,Equiv.symm_apply_apply,sweepRoleEquiv,inactive,↓reduceIte]
  let cell := FlatCoordinateLayout.index (helperSlotField (port r.port.val) none w s) j
  change routedCell backward x (stage.transform x) _ ((stagedOwnerIndex (0 : Fin 1) cell).cast _)
  have same : (stagedOwnerIndex (0 : Fin 1) cell).cast
      (by simpa only [Nat.one_mul] using ordinaryCompact_width (prime^w) W) = cell :=
    Fin.ext (staged_single_val cell)
  rw [same]
  exact read x s j

end IntegerMultBounds.MathlibTM2.M6.BitNode
