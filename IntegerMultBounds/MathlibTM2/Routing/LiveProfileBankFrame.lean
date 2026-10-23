module

public import IntegerMultBounds.MathlibTM2.Routing.LiveInactiveProfileBatch

/-! Profile-bank generation commutes with an unrelated record-stream update. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {N J A : ℕ}
variable (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
  (mode : Fin J → LiveDescriptorMode) (w : LiveDescriptorWidths)

theorem liveInactiveProfileBank_update
    (bank : Fin (liveInactiveProfileT N J) → List (Fin (A + 4))) (j : Fin J)
    (str : Fin (liveInactiveProfileT N J)) (out : List (Fin (A + 4)))
    (hstr : str ≠ liveInactiveProfileCore (liveDescriptorAux (.input j))) :
    liveInactiveProfileBank p X hG hK active s mode w (Function.update bank str out) j =
      Function.update (liveInactiveProfileBank p X hG hK active s mode w bank j) str out := by
  unfold liveInactiveProfileBank
  exact Function.update_comm hstr out _ bank

theorem liveInactiveProfileBatchBank_update
    (bank : Fin (liveInactiveProfileT N J) → List (Fin (A + 4))) (jobs : List (Fin J))
    (str : Fin (liveInactiveProfileT N J)) (out : List (Fin (A + 4)))
    (hstr : ∀ j ∈ jobs, str ≠ liveInactiveProfileCore (liveDescriptorAux (.input j))) :
    liveInactiveProfileBatchBank p X hG hK active s mode w (Function.update bank str out) jobs =
      Function.update (liveInactiveProfileBatchBank p X hG hK active s mode w bank jobs) str out := by
  induction jobs generalizing bank with
  | nil => rfl
  | cons j jobs ih =>
    rw [liveInactiveProfileBatchBank, liveInactiveProfileBatchBank,
      liveInactiveProfileBank_update p X hG hK active s mode w bank j str out (hstr j (by simp))]
    exact ih _ (fun k hk => hstr k (by simp [hk]))

end
end IntegerMultBounds.MathlibTM2.Routing
