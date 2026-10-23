module

public import IntegerMultBounds.MathlibTM2.Routing.SelectiveIdealBits
public import IntegerMultBounds.MathlibTM2.Routing.ReservoirExchangeSchedule

/-! Bit semantics of placing, running exact selective XOR and unplacing. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

theorem inverseRank_bit {n R : ℕ} (f : Equiv.Perm (Fin (R * 2 ^ n))) (e : Equiv.Perm (Fin n))
    (hf : ∀ i q, (f i).val.testBit q.val = i.val.testBit (e q).val)
    (i : Fin (R * 2 ^ n)) (q : Fin n) :
    (f.symm i).val.testBit q.val = i.val.testBit (e.symm q).val := by
  have h := hf (f.symm i) (e.symm q)
  simpa only [Equiv.apply_symm_apply] using h.symm

variable {p : Par} {X R : ℕ} (hK : 0 < p.K) (active : Fin p.n → Bool)
  (s : Fin p.n → SlotSource p X) (hs : ∀ c, (s c).Allowed active)

def placedSelectivePerm (f : Equiv.Perm (Fin (R * 2 ^ fieldsLen (selectiveLen p X)))) :
    Equiv.Perm (Fin (R * 2 ^ fieldsLen (selectiveLen p X))) :=
  (f.trans (selectiveIdealPerm hK active s R hs)).trans f.symm

/-- Placement, exact selective repair and inverse placement preserve the entire
outer row index, not merely the address bits inside the record field. -/
theorem placedSelectivePerm_row
    (f : Equiv.Perm (Fin (R * 2 ^ fieldsLen (selectiveLen p X))))
    (hf : ∀ i, (f i).val / 2 ^ fieldsLen (selectiveLen p X) = i.val / 2 ^ fieldsLen (selectiveLen p X))
    (i : Fin (R * 2 ^ fieldsLen (selectiveLen p X))) :
    (placedSelectivePerm hK active s hs f i).val / 2 ^ fieldsLen (selectiveLen p X) =
      i.val / 2 ^ fieldsLen (selectiveLen p X) := by
  have hinv (j) : (f.symm j).val / 2 ^ fieldsLen (selectiveLen p X) = j.val / 2 ^ fieldsLen (selectiveLen p X) := by
    have h := hf (f.symm j)
    simpa only [Equiv.apply_symm_apply] using h.symm
  change (f.symm (selectiveIdealPerm hK active s R hs (f i))).val / 2 ^ fieldsLen (selectiveLen p X) = _
  rw [hinv]
  change selectiveIdealIdx p X active s (f i).val / 2 ^ fieldsLen (selectiveLen p X) = _
  rw [selectiveIdealIdx_row, hf]

theorem placedSelectivePerm_target_bit
    (f : Equiv.Perm (Fin (R * 2 ^ fieldsLen (selectiveLen p X))))
    (e : Equiv.Perm (Fin (fieldsLen (selectiveLen p X))))
    (hf : ∀ i q, (f i).val.testBit q.val = i.val.testBit (e q).val)
    (i : Fin (R * 2 ^ fieldsLen (selectiveLen p X))) (q : Fin (fieldsLen (selectiveLen p X))) (c : Fin p.n)
    (hq : (e.symm q).val = p.wc + posS p c.val) :
    (placedSelectivePerm hK active s hs f i).val.testBit q.val =
      Bool.xor (i.val.testBit q.val)
        (active c && (s c).physical (selectiveView p X (f i).val).y (selectiveView p X (f i).val).x) := by
  have hbase : (f i).val.testBit (p.wc + posS p c.val) = i.val.testBit q.val := by
    rw [← hq, hf]
    simp
  change (f.symm (selectiveIdealPerm hK active s R hs (f i))).val.testBit q.val = _
  rw [inverseRank_bit f e hf]
  change (selectiveIdealIdx p X active s (f i).val).testBit (e.symm q).val = _
  rw [hq, selectiveIdealIdx_target_bit active s hK, hbase]

theorem placedSelectivePerm_other_bit
    (f : Equiv.Perm (Fin (R * 2 ^ fieldsLen (selectiveLen p X))))
    (e : Equiv.Perm (Fin (fieldsLen (selectiveLen p X))))
    (hf : ∀ i q, (f i).val.testBit q.val = i.val.testBit (e q).val)
    (i : Fin (R * 2 ^ fieldsLen (selectiveLen p X))) (q : Fin (fieldsLen (selectiveLen p X)))
    (hq : ∀ c : Fin p.n, active c = true → (e.symm q).val ≠ p.wc + posS p c.val) :
    (placedSelectivePerm hK active s hs f i).val.testBit q.val = i.val.testBit q.val := by
  change (f.symm (selectiveIdealPerm hK active s R hs (f i))).val.testBit q.val = _
  rw [inverseRank_bit f e hf]
  change (selectiveIdealIdx p X active s (f i).val).testBit (e.symm q).val = _
  rw [selectiveIdealIdx_other_bit active s hK _ _ hq, hf]
  simp

/-- The literal record output of the executed placement/R2/inverse program is
the conjugated permutation whose target and spectator bits are proved above. -/
theorem reservoirPlacedSelective_records {α : Type*} (H : ℕ)
    (hfit : 9 * H ≤ fieldsLen (selectiveLen p X)) (w : ℕ) (hw : w ≤ H) (reservoir : Fin 3)
    (l : List (List α)) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p X)) :
    moveRecs (reservoirExchangeAction (fieldsLen (selectiveLen p X)) H hfit w hw reservoir R true)
      (moveRecs (selectiveIdealPerm hK active s R hs)
        (moveRecs (reservoirExchangeAction (fieldsLen (selectiveLen p X)) H hfit w hw reservoir R false) l)) =
      moveRecs (placedSelectivePerm hK active s hs
        (reservoirExchangeRank (fieldsLen (selectiveLen p X)) H hfit w hw reservoir R)) l := by
  symm
  rw [placedSelectivePerm, moveRecs_trans _ _ l hl, moveRecs_trans _ _ l hl]
  rfl

end IntegerMultBounds.MathlibTM2.Routing
