import IntegerMultBounds.Machine.CompactFallbackAxisRun
import IntegerMultBounds.Machine.CompactFallbackBudget
import IntegerMultBounds.Machine.CompactFallbackScalars

/-! The fallback cost row is supplied by a genuine original-input coefficient
machine. Header construction, the whole selected-bit split/arithmetic/merge,
cleanup and original ordinal advancement are all charged per selected axis. -/
namespace IntegerMultBounds.Machine.CompactFallbackAxisBudget
noncomputable section
open CompactFallbackHeaders CompactFallbackAxisRun
open ButterflyAxisHeadersArithmetic

def scalar (D K ell q : ℕ) := bits D K+q+polynomials ell+1

theorem header_cost (D K rho ell q i : ℕ) (hK : 0<K) (hr : rho<K) (hi : i<D) :
    scheduleCost setup (initial D K rho ell q i)+scheduleCost cleanup (prepared D K rho ell q i 1)+2≤
      (5000+FixedBasePowerDescriptor.constant 2)*scalar D K ell q := by
  have ht := selected_lt D K rho i hK hr hi
  have hiB : i≤bits D K := (Nat.le_mul_of_pos_right i hK).trans (Nat.mul_le_mul_right K hi.le)
  have hone : RecursiveChildQuotientsConstant.cost 1≤100 := by decide
  have hR : 0<polynomials ell := pow_pos (by decide) ell
  simp [setup,cleanup,scheduleCost,ButterflyAxisHeadersArithmetic.cost,eval,CompactChildHeadersArithmetic.cost,
    CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,
    initial,prepared,Function.update]
  simp only [scalar,bits,selected,polynomials,reservation] at *
  nlinarith

theorem scalar_le_volume (D K ell q : ℕ) : scalar D K ell q≤4*volume D K ell q := by
  have hpow : 1≤2^(bits D K) := Nat.one_le_two_pow
  have hR : 1≤polynomials ell := Nat.one_le_two_pow
  have hm : 1≤2^(bits D K)*polynomials ell := Nat.mul_le_mul hpow hR
  have hw : bits D K+q+1≤ButterflyAxisHeadersData.recordLength (bits D K) (reservation D K q) := by
    unfold ButterflyAxisHeadersData.recordLength ButterflyAxisHeadersData.width reservation
    omega
  have hv := Nat.mul_le_mul_right (ButterflyAxisHeadersData.recordLength (bits D K) (reservation D K q)) hm
  have hr := Nat.mul_le_mul_right (polynomials ell) hpow
  have hl : 1≤ButterflyAxisHeadersData.recordLength (bits D K) (reservation D K q) := by
    unfold ButterflyAxisHeadersData.recordLength
    omega
  have hp := Nat.mul_le_mul_left (2^(bits D K)*polynomials ell) hl
  unfold scalar volume ButterflyAxisHeadersBudget.logicalVolume
  nlinarith

def constant := ButterflyAxisOriginal.constant+4*(5000+FixedBasePowerDescriptor.constant 2)

theorem cost_linear (D K rho ell q i : ℕ) (hK : 0<K) (hr : rho<K) (hi : i<D) :
    CompactFallbackAxisRun.cost D K rho ell q i≤constant*volume D K ell q := by
  have hh := header_cost D K rho ell q i hK hr hi
  have hs := Nat.mul_le_mul_left (5000+FixedBasePowerDescriptor.constant 2) (scalar_le_volume D K ell q)
  unfold CompactFallbackAxisRun.cost constant
  nlinarith

theorem runs_linear (D K rho ell q i : ℕ) (hK : 0<K) (hr : rho<K) (hi : i<D)
    (f : Array D K ell) (hw : Width D K ell q f) :
    HoareTime CompactFallbackAxisRun.program
      (fun v => v=bank (initial D K rho ell q i) (word f))
      (fun v => v=bank (initial D K rho ell q (i+1))
        (word (applyAxis D K rho ell q i (selected_lt D K rho i hK hr hi) f)))
      (constant*volume D K ell q) :=
  (CompactFallbackAxisRun.runs D K rho ell q i (selected_lt D K rho i hK hr hi) f hw).consequence
    (fun _ h => h) (fun _ h => h) (cost_linear D K rho ell q i hK hr hi)

end
end IntegerMultBounds.Machine.CompactFallbackAxisBudget
