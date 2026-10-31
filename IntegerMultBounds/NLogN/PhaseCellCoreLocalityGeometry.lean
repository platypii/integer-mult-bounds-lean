module

public import IntegerMultBounds.NLogN.PhaseCellCoreWindowCost
public import IntegerMultBounds.NLogN.PhaseCellCoreGather
public import IntegerMultBounds.NLogN.PhaseCellLocalityPrecision
public import IntegerMultBounds.NLogN.PhaseCellBand

/-! Choose each core as wide as its locality guard. This gives linear overlap
and a polynomial bound for the separated-boundary solver's required room. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

/-- Equal core and guard widths meet the structural overlap bound directly. -/
def localityCoreWidth (p u target : ℕ) : ℕ := localityDepth p target*PhaseCellBand.width p u

theorem localityCoreWidth_pos {p : ℕ} (hp : 1 ≤ p) (u target : ℕ) : 0 < localityCoreWidth p u target := by
  have hb := PhaseCellBand.width_pos p u
  unfold localityCoreWidth localityDepth
  positivity

/-- A coarse polynomial estimate suffices for uniform selected-axis room. -/
theorem localityCoreGeometry_poly (ct p u target : ℕ) (hp : 1 ≤ p) (htarget : target ≤ ct*p) :
    3*localityCoreWidth p u target+PhaseCellBand.width p u ≤ (816*(ct+5)+17)*p^3 := by
  have hb : PhaseCellBand.width p u ≤ 17*p := by
    have hs := Nat.sqrt_le_self (16*p/u)
    have hd := Nat.div_le_self (16*p) u
    unfold PhaseCellBand.width
    omega
  have hsum : target+(p+4) ≤ (ct+5)*p := by nlinarith only [hp,htarget]
  have hdepth : localityDepth p target ≤ 16*(ct+5)*p^2 := by
    have hm := Nat.mul_le_mul_left (16*p) hsum
    unfold localityDepth
    nlinarith only [hm]
  have hw : localityCoreWidth p u target ≤ 272*(ct+5)*p^3 := by
    calc
      _ ≤ (16*(ct+5)*p^2)*(17*p) := Nat.mul_le_mul hdepth hb
      _ = _ := by ring
  have hp3 : p ≤ p^3 := by
    calc
      p = p*1 := by omega
      _ ≤ p*p^2 := Nat.mul_le_mul_left p (Nat.one_le_pow _ _ hp)
      _ = p^3 := by ring
  have hb3 := hb.trans (Nat.mul_le_mul_left 17 hp3)
  nlinarith only [hw,hb3]

theorem coreGatherLength_le (s width radius L : ℕ) (hw : 0 < width)
    (hL : L ∈ coreGatherLengths s width radius) : L ≤ width+2*radius := by
  simp only [coreGatherLengths,List.mem_dedup,List.mem_cons,List.not_mem_nil,or_false] at hL
  rcases hL with rfl | rfl
  · exact le_rfl
  · have hm := Nat.mod_lt s hw
    omega

end IntegerMultBounds.NLogN.PhaseCellMatrix
