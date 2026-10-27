module

public import IntegerMultBounds.MathlibTM2.Cost.Growth
public import Mathlib.Data.Nat.Size
public import IntegerMultBounds.NLogN.PhaseCellHaloGroups

/-! A ring length selected from the ambient phase gap pays all clipped cells
and has total padded volume linear in the ambient line length. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def haloInverseRingLog (s t : ℕ) : ℕ := Nat.size (2*(s/(t-s)+1))

theorem haloInverseRingLog_fits (s t band : ℕ) :
    2*((s/(t-s)+1)-2*band) ≤ 2^haloInverseRingLog s t+1 := by
  have h := Nat.lt_size_self (2*(s/(t-s)+1))
  have hsub := Nat.sub_le (s/(t-s)+1) (2*band)
  dsimp only [haloInverseRingLog]
  omega

theorem haloInverseRingSize_le (s t : ℕ) :
    2^haloInverseRingLog s t ≤ 4*(s/(t-s)+1) := by
  have hpos : 1 ≤ 2*(s/(t-s)+1) :=
    (by decide : 1 ≤ 2).trans (Nat.le_mul_of_pos_right 2 (Nat.succ_pos (s/(t-s))))
  have h := gr_two_pow_size_le hpos
  dsimp only [haloInverseRingLog]
  omega

/-- The phase-gap premise already present in the inverse ABI bounds each cell. -/
theorem phaseGap_cellLength_le {p s t : ℕ} [NeZero s] (hp : 1 ≤ p) (hst : s < t)
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) : s/(t-s) ≤ 4*p := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast NeZero.pos s
  have hpR : (0 : ℝ) < 4*(p : ℝ) := by positivity
  have hgap : (t : ℝ)/s-1 = ((t-s : ℕ) : ℝ)/s := by
    rw [Nat.cast_sub (by omega : s ≤ t)]
    field_simp
  rw [hgap] at hθ
  have hcross := (div_le_div_iff₀ hpR hsR).mp hθ
  have hratio : s ≤ 4*p*(t-s) := by
    exact_mod_cast (by nlinarith only [hcross] : (s : ℝ) ≤ 4*(p : ℝ)*((t-s : ℕ) : ℝ))
  have hdiv := Nat.mul_div_le s (t-s)
  have hg : 1 ≤ t-s := by omega
  nlinarith only [hratio,hdiv,hg]

theorem haloInverseRingLog_bounds {p s t : ℕ} [NeZero s] (hp : 1 ≤ p) (hst : s < t)
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) :
    haloInverseRingLog s t ≤ 20*p ∧ 2^haloInverseRingLog s t ≤ 20*p := by
  have hcell := phaseGap_cellLength_le hp hst hθ
  have hring := haloInverseRingSize_le s t
  have hlog : haloInverseRingLog s t ≤ 2^haloInverseRingLog s t := Nat.lt_two_pow_self.le
  constructor <;> omega

/-- All clipped phases together pay at most eight ambient lines of padding. -/
theorem haloInverseRing_paddedVolume_le {s t : ℕ} (hst : s < t) :
    (t-s+1)*2^haloInverseRingLog s t ≤ 8*t := by
  have hr := Nat.mul_le_mul_left (t-s+1) (haloInverseRingSize_le s t)
  have hdiv := Nat.mul_div_le s (t-s)
  have hg : 1 ≤ t-s := by omega
  have hdup : (t-s+1)*(s/(t-s)+1) ≤ 2*((t-s)*(s/(t-s)+1)) := by
    nlinarith only [hg,Nat.zero_le (s/(t-s))]
  have hsum : (t-s)*(s/(t-s)+1) ≤ t := by nlinarith only [hdiv,Nat.sub_add_cancel (by omega : s ≤ t)]
  nlinarith only [hr,hdup,hsum]

end IntegerMultBounds.MathlibTM2.Cost
