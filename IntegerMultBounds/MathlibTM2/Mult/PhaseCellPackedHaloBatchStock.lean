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

/-- The cursor allowance is retained once, independently of the prefix length. -/
theorem PackedHaloInputTrace.stock_le_cursor {Q A : ℕ} {U X : Type}
    {Result : X → Stacks 248 A → Stacks 248 A → Prop} {L : ℕ}
    (hresult : ∀ x S F, Result x S F → (F.R 132).length = L+(S.R 132).length)
    {xs : List X} {S F : Stacks 248 A} (h : PackedHaloInputTrace Result xs S F)
    (v vf : HS 248 Q A U) (V : ℕ)
    (hframe : hostFrameStock F ≤ hostFrameStock S)
    (hcursor : (F.R 157).length ≤ V)
    (hother : ∀ i, i ≠ 132 → i ≠ 157 → (F.R i).length ≤ (S.R i).length) :
    mnSize (mk vf F) ≤ mnSize (mk v S)+xs.length*L+V := by
  have hb := mnSize_mk_le_allowance v vf S F
    (fun i => (if i = 132 then xs.length*L else 0)+(if i = 157 then V else 0)) hframe (by
      intro i
      by_cases ho : i = 132
      · subst i
        have hlen := h.output_length hresult
        simp only [ite_true,show (132 : Fin 248) ≠ 157 by decide,ite_false,Nat.add_zero]
        omega
      · by_cases hc : i = 157
        · subst i
          simp only [show (157 : Fin 248) ≠ 132 by decide,ite_false,ite_true,Nat.zero_add]
          omega
        · simpa [ho,hc] using hother i ho hc)
  simpa [Finset.sum_add_distrib,Nat.add_assoc] using hb

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
