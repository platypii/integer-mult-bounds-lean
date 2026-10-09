import IntegerMultBounds.Machine.CountedTapeRepairBudget
import IntegerMultBounds.Compact.Density

/-! The paid reusable repair machine's density coefficient is bounded by the
actual exceptional set, rather than supplied as a repair oracle assumption. -/
namespace IntegerMultBounds.Machine.CountedTapeRepairDensity
noncomputable section
open IntegerMultBounds.Compact
open IntegerMultBounds.Compact.PowerTwo
open CountedTapeRepairBank
open CountedTapeRepairBudget

def density (q b : ℕ) (Z : List Bool) : ℝ :=
  Z.length/(2:ℝ)^b+8*Z.length*(2:ℝ)^b/(2:ℝ)^q

theorem bad_count (q b : ℕ) (hbq : b+3≤q) (Z : List Bool) :
    (badCount q b Z : ℝ)≤density q b Z*Mi q b Z := by
  have hq : 1≤q := by omega
  have hM : 0<Mi q b Z := by rw [Mi_eq q b Z hq]; positivity
  have hcard : Nat.card (Address q b Z)=Mi q b Z := by
    rw [Nat.card_congr (rankEquiv q b Z),Nat.card_fin]
  have hpos : 0<(Nat.card (Address q b Z) : ℝ) := by rw [hcard]; exact_mod_cast hM
  have hc := card_bad_eq_fraction (earlyGood (Bi b) (Li q) (controls Z).length) hpos
  rw [hcard] at hc
  have hguard : 4*Bi b≤Li q := by
    calc
      4*Bi b=(2:ℤ)^(b+2) := by unfold Bi; rw [pow_add]; norm_num; ring
      _≤Li q := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (by omega)
  have hf := early_bad_fraction_le (Bi b) (Li q) (by positivity) (Li_pos q) hguard (controls Z).length
  have hden : (2:ℝ)*(Li q : ℝ)=(2:ℝ)^q := by exact_mod_cast two_Li q hq
  have he : ((controls Z).length : ℝ)/(Bi b : ℝ)+8*(controls Z).length*(Bi b : ℝ)/(2*(Li q : ℝ))=density q b Z := by
    rw [hden,controls_length]
    simp only [density,Bi,Int.cast_pow,Int.cast_ofNat]
  rw [he] at hf
  calc
    (badCount q b Z : ℝ)=badFraction (earlyGood (Bi b) (Li q) (controls Z).length)*Mi q b Z := hc
    _≤density q b Z*Mi q b Z := mul_le_mul_of_nonneg_right hf (Nat.cast_nonneg _)

theorem full_cost_le (q b : ℕ) (hbq : b+3≤q) (Z : List Bool) (data : Address q b Z → List Bool)
    (w : ℕ) (hw : ∀ x,(data x).length≤w) :
    (fullCost q b Z data : ℝ)≤base q b Z w+density q b Z*Mi q b Z*coefficient q b Z w := by
  have h := CountedTapeRepairBudget.full_cost_le q b Z data w hw
  have hr : (fullCost q b Z data : ℝ)≤(bound q b Z w (badCount q b Z) : ℝ) := by exact_mod_cast h
  simp only [bound,Nat.cast_add,Nat.cast_mul] at hr
  have hd := mul_le_mul_of_nonneg_right (bad_count q b hbq Z) (Nat.cast_nonneg (coefficient q b Z w))
  linarith

end
end IntegerMultBounds.Machine.CountedTapeRepairDensity
