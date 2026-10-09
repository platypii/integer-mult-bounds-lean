import IntegerMultBounds.Machine.ActiveRepairLayoutDensity
import IntegerMultBounds.Compact.TapeRepair

/-! Bridge complete layout density to the literal position-indexed scan.
Flag agreement is required only at the ranks actually visited. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutDensityScan
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

 theorem holes_plain {X : Type*} [Fintype X] {M : ℕ} (e : X ≃ Fin M)
    (bad : X → Prop) [DecidablePred bad] (data : X → List Bool)
    (flag : ℕ → Bool) (hf : ∀ j<M, flag j=rankFlag e bad j) :
    Reinsert.holes (RepairScan.flagged flag 0 (plain e data))=Nat.card {x : X // bad x} := by
  rw [flagged_plain e bad data flag hf,holes_stream,badRanks_length]

 theorem sparse_plain {X : Type*} [Fintype X] {M : ℕ} (e : X ≃ Fin M)
    (bad : X → Prop) [DecidablePred bad] (data : X → List Bool)
    (flag : ℕ → Bool) (hf : ∀ j<M, flag j=rankFlag e bad j)
    (δ : ℝ) (A D : ℕ)
    (hcount : (Nat.card {x : X // bad x} : ℝ)≤δ*Nat.card X)
    (hd : δ*(A+1)≤D) :
    Reinsert.holes (RepairScan.flagged flag 0 (plain e data))*(A+1)≤
      D*(plain e data).length := by
  rw [flagged_plain e bad data flag hf,plain_length]
  exact ActiveRepairLayoutDensity.holes_sparse e bad data δ A D hcount hd

end
end IntegerMultBounds.Machine.ActiveRepairLayoutDensityScan
