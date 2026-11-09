module

public import IntegerMultBounds.NLogN.PhaseCellBoundaryCropSchedule

/-! The first two boundary slots have full width; only the final slot clips.
Their narrow count masters can therefore share one full-width product. -/
@[expose] public section
set_option autoImplicit false
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

theorem boundaryCropLengths (s width : ℕ) (hw : 0 < width) (hroom : 3*width < s) :
    ∀ slot : Fin 3, coreLength s width (boundaryCropIndex s width slot) =
      ![width,width,(s-1)%width+1] slot := by
  have hs : 1 ≤ s := by omega
  have hq : 1 ≤ (s-1)/width := (Nat.le_div_iff_mul_le hw).mpr (by omega)
  have hceil : (s+width-1)/width = (s-1)/width+1 := by
    rw [show s+width-1 = (s-1)+width by omega,Nat.add_div_right _ hw]
  have hprod := Nat.div_mul_le_self (s-1) width
  have hpen : ((s-1)/width-1)*width+width = ((s-1)/width)*width := by
    rw [Nat.sub_mul,Nat.one_mul]
    exact Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ hq)
  have hpenRoom : width ≤ s-(((s-1)/width-1)*width) := by omega
  have hm := Nat.mod_lt (s-1) hw
  have hd := Nat.div_add_mod (s-1) width
  rw [Nat.mul_comm width] at hd
  have htail : s-((s-1)/width)*width = (s-1)%width+1 := by omega
  intro slot
  fin_cases slot
  · change min width (s-0*width) = width
    simp only [Nat.zero_mul,Nat.sub_zero]
    exact Nat.min_eq_left (by omega)
  · change min width (s-(((s+width-1)/width-2)*width)) = width
    rw [hceil,show (s-1)/width+1-2 = (s-1)/width-1 by omega]
    exact Nat.min_eq_left hpenRoom
  · change min width (s-(((s+width-1)/width-1)*width)) = (s-1)%width+1
    rw [hceil,Nat.add_sub_cancel_right,htail]
    exact Nat.min_eq_right (by omega)

end IntegerMultBounds.NLogN.PhaseCellMatrix
