import IntegerMultBounds.Machine.ActivePrefixSelectedOffsetData
import IntegerMultBounds.Machine.BinaryVaryingControlOffsetGather
import IntegerMultBounds.Machine.BinaryVaryingControlOffsetData

/-! Exact control-mask offset stream from physically projected source bits.
The auxiliary width-n prefix projection is only a physical scan clock; every
emitted bit depends on the current address's selected source control. -/
namespace IntegerMultBounds.Machine.ActivePrefixControlOffsetData

def offsets (W startT startX q b rho n f : ℕ) (hT : startT+n≤W) (hX : startX+f*q≤W)
    (hb : 1≤b) (hbq : b+1≤q) :=
  BinaryVaryingControlOffsetGather.word q b hb hbq (BinaryPrefixFieldTableData.word W startT n hT)
    (SelectedSourceBitsStreamData.selected (BinaryPrefixFieldTableData.word W startX (f*q) hX)
      q rho n f (2^W))

theorem offsets_length (W startT startX q b rho n f : ℕ)
    (hT : startT+n≤W) (hX : startX+f*q≤W) (hb : 1≤b) (hbq : b+1≤q) :
    (offsets W startT startX q b rho n f hT hX hb hbq).length=2^W*(n*q) := by
  simp [offsets,Nat.mul_assoc]

/-- The mask for each prefix uses exactly that address's physical controls. -/
theorem offset_row (W startT startX q b rho n f i : ℕ)
    (hT : startT+n≤W) (hX : startX+f*q≤W) (hb : 1≤b) (hbq : b+1≤q)
    (hnf : n+1=f) (hr : rho<q) (hi : i<2^W) :
    Gather.field (offsets W startT startX q b rho n f hT hX hb hbq) (i*(n*q)) (n*q)=
      Compact.PowerTwo.toggleMask q (ActivePrefixSelectedOffsetData.controls W startX q rho n f i) := by
  unfold offsets
  rw [ActivePrefixSelectedOffsetData.extracted_controls W startX q rho n f hX hnf hr]
  exact BinaryVaryingControlOffsetData.field_eq q b n (2^W) i _ _ hb hbq
    (by intro k hk; exact SelectedSourceBitsData.selected_length _ _ _ _) hi

end IntegerMultBounds.Machine.ActivePrefixControlOffsetData
