module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloBatchProgram
public import IntegerMultBounds.MathlibTM2.Host.StackStock

/-! Persistent archive storage at a prefix of the actual numerical batch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main

theorem PackedHaloInputTrace.stock_le {Q A : ℕ} {U X : Type}
    {Result : X → Stacks 248 A → Stacks 248 A → Prop} {L : ℕ}
    (hresult : ∀ x S F, Result x S F → (F.R 132).length = L+(S.R 132).length)
    {xs : List X} {S F : Stacks 248 A} (h : PackedHaloInputTrace Result xs S F)
    (v vf : HS 248 Q A U)
    (hframe : hostFrameStock F ≤ hostFrameStock S)
    (hother : ∀ i, i ≠ 132 → (F.R i).length ≤ (S.R i).length) :
    mnSize (mk vf F) ≤ mnSize (mk v S)+xs.length*L := by
  apply mnSize_mk_le_archive v vf S F 132 (xs.length*L) hframe
  · have hlen := h.output_length hresult
    omega
  · exact hother

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
