module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFormattedClassSetup
import Mathlib.Tactic.Linarith

/-! Structural pricing for shared class setup. Only the number of exported
formats matters; scalar values and the numerical bank are absent. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CommonClassGeometry

private theorem sum_map_affine_le {α : Type} (rs : List α) (f : α → ℕ) (D a b : ℕ)
    (hf : ∀ r ∈ rs, f r ≤ D) :
    (rs.map (fun r => a*f r+b)).sum ≤ rs.length*(a*D+b) := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    have hr := Nat.mul_le_mul_left a (hf r (by simp))
    have hs := ih (fun q hq => hf q (by simp [hq]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]
    omega

def classSetupTimeBound (D : ℕ) : ℕ := 5*tblC D 0+174*D+186

def classSetupStockBound (D : ℕ) : ℕ := 15*tblC D 0+426*D+458

def classSetupRetireBound (D : ℕ) : ℕ := 10*D+12

theorem formattedClassSetupCosts_le {T A D p u l target s t B W N radius width : ℕ}
    {S : Stacks T A} (c : FormattedClassSetup D p u l target s t B W N radius width S)
    (hcount : c.formats.length ≤ 3) :
    c.timeCost ≤ classSetupTimeBound D ∧ c.stock ≤ classSetupStockBound D ∧
      c.retireCost ≤ classSetupRetireBound D := by
  have hformats := sum_map_affine_le c.formats (fun r => c.bits r.1) D 10 10 c.bitsFit
  have hbits := sum_map_affine_le c.formats (fun r => c.bits r.1) D 1 0 c.bitsFit
  have hcountCost := Nat.mul_le_mul_right (10*D+10) hcount
  have hcountBits := Nat.mul_le_mul_right D hcount
  simp only [one_mul,Nat.add_zero] at hbits
  unfold FormattedClassSetup.timeCost FormattedClassSetup.stock FormattedClassSetup.retireCost
    prepareMastersTimeCost prepareMastersStock seedLoadCost masterTimeCost masterStock binaryFormatsCost
    classSetupTimeBound classSetupStockBound classSetupRetireBound
  constructor
  · nlinarith only [hformats,hcountCost]
  constructor
  · nlinarith only [hformats,hcountCost]
  · nlinarith only [hbits,hcountBits,hcount]

end IntegerMultBounds.MathlibTM2.Cost
