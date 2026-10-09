import IntegerMultBounds.Machine.ActiveRepairLayoutKeysScan

/-! Bounded physical scan-key identification suffices for the complete
list repair. No behavior beyond the finite original layout is assumed. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutKeysPipelineCommon
noncomputable section
open Compact

theorem flagged_plain {X : Type*} {M : ℕ} (e : X ≃ Fin M)
    (bad : X → Prop) [DecidablePred bad] (data : X → List Bool)
    (flag : ℕ → Bool) (hf : ∀ j<M, flag j=rankFlag e bad j) :
    RepairScan.flagged flag 0 (plain e data)=stream e bad data := by
  unfold plain
  rw [flagged_map,stream]
  apply List.map_congr_left
  intro i _
  rw [Nat.zero_add,hf i i.isLt,rankFlag_fin]

theorem items_plain {X : Type*} [Fintype X] {M : ℕ} (e : X ≃ Fin M)
    (S T : Equiv.Perm X) (bad : X → Prop) [DecidablePred bad]
    (k : ℕ) (data : X → List Bool) (flag : ℕ → Bool) (bits : ℕ → List Bool)
    (hf : ∀ j<M, flag j=rankFlag e bad j) (hb : ∀ j<M, bits j=rankKey e S T k j) :
    RepairScan.items flag bits 0 (plain e (data ∘ S.symm))=items e S T bad k data := by
  rw [plain,items_map,items,extracted,badRanks,List.map_map]
  rw [List.filter_congr (p := fun i : Fin M => flag (0+i))
    (q := fun i => decide (bad (e.symm i))) (l := List.finRange M)
    (fun i _ => by rw [Nat.zero_add,hf i i.isLt,rankFlag_fin])]
  apply List.map_congr_left
  intro i _
  simp only [keyedOf,Nat.zero_add,hb i i.isLt,rankKey_fin,Function.comp]

theorem counter_bound (s : CompactGadgetReservationShape.Shape) (rows rowBits : ℕ)
    (hp : s.payload=1) (hr : rows≤2^rowBits) : rows*s.recordWidth≤2^(s.bits+rowBits) := by
  simp only [CompactGadgetReservationShape.Shape.recordWidth,hp,Nat.mul_one]
  rw [pow_add]
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_right (2^s.bits) hr

end
end IntegerMultBounds.Machine.ActiveRepairLayoutKeysPipelineCommon
