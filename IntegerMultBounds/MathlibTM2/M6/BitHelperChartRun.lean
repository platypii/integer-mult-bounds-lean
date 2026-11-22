module

public import IntegerMultBounds.MathlibTM2.M6.BitFlatChartRun
public import IntegerMultBounds.MathlibTM2.M6.BitHelperPacking

/-! Move both flat parent fields to the certified port chart on one owner tape. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Certificates.PR589 Certificates.PR589.Nine
open Shared50ModularControl (prime)
open Matrix IntegerMultBounds.Swap.Modular
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

def flatParentOrder : Fin 128 ≃ Axis ⊕ Axis :=
  (@finSumFinEquiv 64 64).symm.trans (Equiv.sumCongr stageAxis.symm stageAxis.symm)

/-- Apply the same rectangularly indexed change of basis to both parent
fields, then serialize the output in the given digit order. -/
theorem pairedChart_owner [M8.Machine.Net] {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι Axis ℚ) (J : Matrix Axis ι ℚ) (hJ : H*J = 1)
    (bounded : ∀ i j, (H i j).num.natAbs ≤ 10000 ∧ (H i j).den ≤ 10000)
    (order : Fin 128 ≃ ι ⊕ ι) :
    ∃ (a k : ℕ) (machine : SharedBankSkeleton.Skeleton 1 prime), ∀ w W, 0 < w → 0 < W →
      let V := (prime^w)^128*W
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = machine ∧
        stage.cost = a*V+k*(3808274*V+M8.RevMachine.LeafCore.coreCost V w+1)+2 ∧
        HasStackSeed stage.metadata ∧ ∀ x (s : Swap.Shear.State Axis (ZMod (prime^w))) j,
          stage.transform x (FlatCoordinateLayout.index ((Sum.elim (reduce (prime^w) H *ᵥ s.1) (reduce (prime^w) H *ᵥ s.2) ∘ order)) j) =
            x (FlatCoordinateLayout.index (Sum.elim s.1 s.2 ∘ flatParentOrder) j) := by
  let D := fromBlocks H 0 0 H
  let U := D.submatrix order flatParentOrder
  let inv := (fromBlocks J 0 0 J).submatrix flatParentOrder order
  have cancel : U*inv = 1 := by
    dsimp only [U,inv]
    rw [submatrix_mul_equiv]
    simp [D,fromBlocks_multiply,hJ,submatrix_one_equiv]
  have entries (i j) : (U i j).num.natAbs ≤ 10^10000 ∧ (U i j).den ≤ 10^10000 := by
    have big : 10000 ≤ (10:ℕ)^10000 := (by decide : 10000 ≤ 10^4).trans
      (pow_le_pow_right₀ (by decide : 1 ≤ (10:ℕ)) (by decide : 4 ≤ 10000))
    change ((fromBlocks H 0 0 H) (order i) (flatParentOrder j)).num.natAbs ≤ _ ∧ _
    dsimp only [U,D,submatrix_apply]
    cases order i <;> cases flatParentOrder j
    all_goals first
      | exact ⟨(bounded _ _).1.trans big,(bounded _ _).2.trans big⟩
      | exact ⟨(by decide : (0:ℚ).num.natAbs ≤ 10000).trans big,(by decide : (0:ℚ).den ≤ 10000).trans big⟩
  obtain ⟨a,k,m,run⟩ := flatChart_owner U (isUnit_iff_exists.mpr ⟨_,cancel,mul_eq_one_comm.mp cancel⟩)
    (by decide) (by decide) entries
  refine ⟨a,k,m,?_⟩
  intro w W hw hW V
  obtain ⟨stage,fixed,cost,seed,read⟩ := run w W hw hW
  refine ⟨stage,fixed,cost,seed,?_⟩
  intro x s j
  let F := reduce (prime^w) H
  have mat : reduce (prime^w) U = (fromBlocks F 0 0 F).submatrix order flatParentOrder := by
    ext i j
    change ratMod _ (D (order i) (flatParentOrder j)) = (fromBlocks F 0 0 F) _ _
    cases order i <;> cases flatParentOrder j <;> first | rfl | exact ratMod_zero _
  have action : reduce (prime^w) U *ᵥ (Sum.elim s.1 s.2 ∘ flatParentOrder) = (Sum.elim (F *ᵥ s.1) (F *ᵥ s.2) ∘ order) := by
    rw [mat,submatrix_mulVec_equiv]
    simp [Function.comp_assoc,fromBlocks_mulVec,F]
  rw [← action]
  exact read x _ j

/-- The selected port and slot determine a fixed machine. Both halves are
charted together while the trailing spectator retains its position. -/
theorem helperChart_owner [M8.Machine.Net] (c : PortCertificate) (hc : c.Checked)
    (slot : Option (Fin 56)) :
    ∃ (a k : ℕ) (machine : SharedBankSkeleton.Skeleton 1 prime), ∀ w W, 0 < w → 0 < W →
      let V := (prime^w)^128*W
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = machine ∧
        stage.cost = a*V+k*(3808274*V+M8.RevMachine.LeafCore.coreCost V w+1)+2 ∧
        HasStackSeed stage.metadata ∧ ∀ x (s : Swap.Shear.State Axis (ZMod (prime^w))) j,
          stage.transform x (FlatCoordinateLayout.index (helperSlotField c slot w s) j) =
            x (FlatCoordinateLayout.index (Sum.elim s.1 s.2 ∘ flatParentOrder) j) := by
  exact pairedChart_owner c.fullChart.transpose c.fullChart (c.fullChart_orthonormal hc)
    (fun i j => ⟨(fullChart_entry c hc j i).1.trans (by decide),
      (fullChart_entry c hc j i).2.trans (by decide)⟩) (helperFieldOrder slot)

end IntegerMultBounds.MathlibTM2.M6.BitNode
