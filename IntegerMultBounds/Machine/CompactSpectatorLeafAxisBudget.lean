import IntegerMultBounds.Machine.ButterflySpectatorBudget
import IntegerMultBounds.Machine.CompactSpectatorInverseLeafAxis
import IntegerMultBounds.Machine.CompactSpectatorLeafAxis

/-! Every actual leaf-body descriptor is bounded by the immutable full address
geometry, including the final selected position. Both forward and inverse
native bodies have a uniform linear whole-word bound with paid scalar work. -/
namespace IntegerMultBounds.Machine.CompactSpectatorLeafAxisBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactSpectatorLeafHeaders
open ButterflyAxisHeadersArithmetic

def scalar (s : Shape) (ell p : ℕ) := s.bits+p+2^ell+1
abbrev volume (s : Shape) (rows ell p : ℕ) := ButterflySpectatorBudget.volume rows s.bits (2^ell) p

theorem descriptors (s : Shape) (rho ordinal : ℕ) (hr : rho<s.chunk) (ho : ordinal<s.active) :
    s.H≤s.bits ∧ s.B≤s.bits ∧ s.active≤s.bits ∧ s.chunk≤s.bits ∧ rho≤s.bits ∧
    ordinal≤s.bits ∧ (s.active-1-ordinal)*s.chunk≤s.bits ∧ selected s rho ordinal<s.bits := by
  have hK : 0<s.chunk := by omega
  have ha : 0<s.active := by omega
  have hA := Nat.le_mul_of_pos_right s.active hK
  have hchunk := Nat.le_mul_of_pos_left s.chunk ha
  have he : s.active-1-ordinal+1≤s.active := by omega
  have hm := Nat.mul_le_mul_right s.chunk he
  unfold selected CompactSpectatorVisitGeometry.selected Shape.bits
  simp only [Nat.add_zero]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals nlinarith only [hA,hchunk,hm,hr,ho]

theorem header_cost (s : Shape) (rows ell p rho ordinal count : ℕ) (hr : rho<s.chunk) (ho : ordinal<s.active) :
    scheduleCost setup (initial s rows ell p rho ordinal count)+
    scheduleCost cleanup (prepared s rows ell p rho ordinal count 1)+2≤
      (5000+FixedBasePowerDescriptor.constant 2)*scalar s ell p := by
  obtain ⟨hH,hB,hA,hK,hr',ho',hm,hs⟩ := descriptors s rho ordinal hr ho
  have hc : RecursiveChildQuotientsConstant.cost 1≤100 := by decide
  have hp : 0<2^ell := pow_pos (by decide) _
  simp [setup,cleanup,scheduleCost,ButterflyAxisHeadersArithmetic.cost,eval,CompactChildHeadersArithmetic.cost,
    CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,
    initial,prepared,Function.update]
  have hsuba : s.active-1≤s.bits := (Nat.sub_le _ _).trans hA
  have hsubo : s.active-1-ordinal≤s.bits := (Nat.sub_le _ _).trans hsuba
  simp only [scalar,selected,CompactSpectatorVisitGeometry.selected,Nat.add_zero,Nat.add_mul,Nat.mul_add] at *
  omega

theorem scalar_le_volume (s : Shape) (rows ell p : ℕ) (hr : 0<rows) :
    scalar s ell p≤4*volume s rows ell p := by
  have hpow : 1≤2^s.bits := Nat.one_le_two_pow
  have hR : 1≤2^ell := Nat.one_le_two_pow
  have hprod : 1≤rows*2^s.bits*2^ell := by
    have h0 := Nat.mul_le_mul (show 1≤rows by omega) hpow
    simpa using Nat.mul_le_mul h0 hR
  have hw : s.bits+p+1≤ButterflyAxisHeadersData.recordLength s.bits p := by
    unfold ButterflyAxisHeadersData.recordLength ButterflyAxisHeadersData.width
    omega
  have hv := Nat.mul_le_mul_right (ButterflyAxisHeadersData.recordLength s.bits p) hprod
  have hrp : 2^ell≤rows*2^s.bits*2^ell := Nat.le_mul_of_pos_left _ (by positivity)
  have hl : 1≤ButterflyAxisHeadersData.recordLength s.bits p := by
    unfold ButterflyAxisHeadersData.recordLength
    omega
  have hlast := Nat.mul_le_mul_left (rows*2^s.bits*2^ell) hl
  unfold scalar volume ButterflySpectatorBudget.volume ButterflyAxisHeadersBudget.logicalVolume
  nlinarith only [hw,hv,hrp,hlast]

def constant := ButterflySpectatorBudget.constant+4*(5000+FixedBasePowerDescriptor.constant 2)

theorem cost_linear (s : Shape) (rows ell p rho ordinal count : ℕ)
    (hrows : 0<rows) (hr : rho<s.chunk) (ho : ordinal<s.active) :
    CompactSpectatorLeafAxis.cost s rows ell p rho ordinal count≤constant*volume s rows ell p := by
  have hh := header_cost s rows ell p rho ordinal count hr ho
  have ht := (descriptors s rho ordinal hr ho).2.2.2.2.2.2.2
  have ha := ButterflySpectatorBudget.cost_linear rows s.bits (selected s rho ordinal) (2^ell) p hrows ht
    (pow_pos (by decide) _)
  have hs := Nat.mul_le_mul_left (5000+FixedBasePowerDescriptor.constant 2) (scalar_le_volume s rows ell p hrows)
  unfold CompactSpectatorLeafAxis.cost constant
  nlinarith only [hh,ha,hs]

theorem inverse_cost_linear (s : Shape) (rows ell p rho ordinal count : ℕ)
    (hrows : 0<rows) (hr : rho<s.chunk) (ho : ordinal<s.active) :
    CompactSpectatorInverseLeafAxis.cost s rows ell p rho ordinal count≤constant*volume s rows ell p := by
  exact cost_linear s rows ell p rho ordinal count hrows hr ho

end
end IntegerMultBounds.Machine.CompactSpectatorLeafAxisBudget
