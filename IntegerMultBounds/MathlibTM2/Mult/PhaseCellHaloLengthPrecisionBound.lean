module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSolveHaloInteriorWorkspaceBound
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! The manuscript's gap condition bounds all selected cell lengths by precision. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem axis_ratio_le_precision {p s t : ℕ} (hp : 0 < p) (hs : 0 < s) (hst : s < t)
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) : s/(t-s) ≤ 4*p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hθ' : 1/(4*(p : ℝ)) ≤ ((t : ℝ)-s)/s := by
    simpa only [sub_div,div_self hsR.ne'] using hθ
  have hm := (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4*p) hsR).mp hθ'
  have hnat : s ≤ 4*p*(t-s) := by
    have hcast : (s : ℝ) ≤ 4*p*((t-s : ℕ) : ℝ) := by
      rw [Nat.cast_sub hst.le]
      simpa only [one_mul,mul_one,mul_comm] using hm
    exact_mod_cast hcast
  have hd : 0 < t-s := Nat.sub_pos_of_lt hst
  calc
    s/(t-s) ≤ (4*p*(t-s))/(t-s) := Nat.div_le_div_right hnat
    _ = 4*p := Nat.mul_div_left _ hd

theorem generatedHaloKeysWorkspace_le_precision
    (J R K p l s t u target rhsExp V a b : ℕ)
    (hp : 0 < p) (hs : 0 < s) (hst : s < t) (ha : a ≤ s) (hb : b ≤ s)
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) :
    haloLengthKeyLoopWorkspace J R K p l s t u target rhsExp V a b
      (IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloLengthKeys s t
        (IntegerMultBounds.NLogN.PhaseCellBand.width p u) a b) ≤
      haloKeySharedSetup J R K p l s t u target rhsExp (4*p+1)+
        haloKeyAuxWorkspace R K p l s t u target rhsExp V := by
  have hratio := axis_ratio_le_precision hp hs hst hθ
  apply (generatedHaloKeysWorkspace_le_uniform J R K p l s t u target rhsExp V a b hst ha hb).trans
  exact Nat.add_le_add_right (haloKeySharedSetup_mono J R K p l s t u target rhsExp _ (4*p+1)
    (by omega)) _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
