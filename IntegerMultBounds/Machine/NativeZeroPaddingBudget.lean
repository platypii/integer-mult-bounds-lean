import IntegerMultBounds.Machine.NativeZeroPaddingArray
import IntegerMultBounds.Machine.CompactGlobalReservation

/-! One genuine native zero pad is uniformly linear in the original complete
native word. The factor-two row allowance is charged once, before role descent. -/
namespace IntegerMultBounds.Machine.NativeZeroPaddingBudget
noncomputable section
open NativeZeroPaddingHeaders
open ButterflyAxisHeadersArithmetic
open RecursiveChildQuotientsConstant (bits)

def volume (rows D ell w : ℕ) := rows*2^D*2^ell*(2*(w+1))
def constant := 2500+2*FixedBasePowerDescriptor.constant 2

theorem header_cost_eq (rows target D ell w : ℕ) :
    scheduleCost schedule (initial rows target D ell w)+scheduleCost cleanup (output rows target D ell w)=
      100*(target+rows+(target-rows)+2^D+2^ell+2^D*2^ell+count rows target D ell+6)+
      FixedBasePowerDescriptor.constant 2*(2^D+2^ell)+53*(2^D*2^ell+count rows target D ell)+66 := by
  dsimp [schedule,cleanup,scheduleCost,cost,eval,CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,initial,output,count,Function.update]
  simp only [Option.getD_some]
  ring

theorem padding_cost_le (xs : List (Fin 6)) (w n : ℕ) :
    NativeZeroPadding.cost xs (bits w) (bits n) w n≤
      2*xs.length+58*(n*(2*(w+1)))+50 := by
  have hw := ActiveRepairRankHeadersCommands.bits_length w
  have hn := ActiveRepairRankHeadersCommands.bits_length n
  unfold NativeZeroPadding.cost
  rw [List.length_append,NativeZeroStream.length]
  have hm := Nat.mul_le_mul_left (22*n) hw
  nlinarith

theorem cost_linear (rows target D ell w : ℕ) (hr : 0<rows) (hpad : rows≤target)
    (ht : target≤2*rows) (xs : List (Fin 6)) (hx : xs.length=volume rows D ell w) :
    NativeZeroPaddingPlaced.cost rows target D ell w xs≤constant*volume rows D ell w := by
  let V := volume rows D ell w
  have hA : 0<2^D := pow_pos (by decide) _
  have hB : 0<2^ell := pow_pos (by decide) _
  have hW : 0<2*(w+1) := by omega
  have hV : 0<V := by unfold V volume; positivity
  have hAB : 2^D*2^ell≤V := by
    calc
      _ ≤ rows*(2^D*2^ell) := Nat.le_mul_of_pos_left _ hr
      _ ≤ rows*(2^D*2^ell)*(2*(w+1)) := Nat.le_mul_of_pos_right _ hW
      _ = V := by unfold V volume; ring
  have ha : 2^D≤V := (Nat.le_mul_of_pos_right _ hB).trans hAB
  have hb : 2^ell≤V := (Nat.le_mul_of_pos_left _ hA).trans hAB
  have hrows : 2*rows≤V := by
    have hp : 1≤2^D*2^ell := Nat.mul_pos hA hB
    have hm := Nat.mul_le_mul_left (2*rows) hp
    have hw := Nat.mul_le_mul_left (rows*(2^D*2^ell)) (show 2≤2*(w+1) by omega)
    unfold V volume
    nlinarith
  have hd : target-rows≤rows := by omega
  have hn : count rows target D ell≤V := by
    unfold count
    exact (Nat.mul_le_mul_right (2^D*2^ell) hd).trans (by
      unfold V volume
      have hh := Nat.le_mul_of_pos_right (rows*(2^D*2^ell)) hW
      nlinarith)
  have hs : count rows target D ell*(2*(w+1))≤V := by
    have hh := Nat.mul_le_mul_right ((2^D*2^ell)*(2*(w+1))) hd
    unfold count V volume
    nlinarith
  have hpow := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2) (show 2^D+2^ell≤2*V by omega)
  have hh := header_cost_eq rows target D ell w
  have hz := padding_cost_le xs w (count rows target D ell)
  rw [hx] at hz
  unfold NativeZeroPaddingPlaced.cost constant
  change _≤(2500+2*FixedBasePowerDescriptor.constant 2)*V
  nlinarith

/-- The global pad's single factor two is available before any role division. -/
theorem global_cost_linear (c m d K D ell w : ℕ) (hc : 0<c) (hK : 0<K) (xs : List (Fin 6))
    (hx : xs.length=volume (CompactGlobalRowPadding.originalRows c m d K) D ell w) :
    NativeZeroPaddingPlaced.cost (CompactGlobalRowPadding.originalRows c m d K)
      (CompactGlobalRowPadding.initialRows c m d K) D ell w xs≤
      constant*volume (CompactGlobalRowPadding.originalRows c m d K) D ell w := by
  have hb := CompactGlobalRowPadding.initial_bounds c m d K hc hK
  exact cost_linear _ _ D ell w (pow_pos (by decide) _) hb.1 hb.2.2.1 xs hx

/-- Existing row reservation bits exactly recover the original global binary
volume. One native pad therefore costs a uniform constant times that volume,
independently of subsequent role depth. -/
theorem original_dimension_cost (c m d D G K ell w : ℕ) (hc : 0<c) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D) (xs : List (Fin 6))
    (hx : xs.length=2^(D*K)*2^ell*(2*(w+1))) :
    NativeZeroPaddingPlaced.cost (CompactGlobalRowPadding.originalRows c m d K)
      (CompactGlobalRowPadding.initialRows c m d K)
      (CompactGlobalReservation.shape c m d D G K 1).bits ell w xs≤
      constant*(2^(D*K)*2^ell*(2*(w+1))) := by
  have he := CompactGlobalReservation.original_bits c m d D G K 1 hK hD
  have hv : volume (CompactGlobalRowPadding.originalRows c m d K)
      (CompactGlobalReservation.shape c m d D G K 1).bits ell w=2^(D*K)*2^ell*(2*(w+1)) := by
    unfold volume CompactGlobalRowPadding.originalRows
    rw [←pow_add,he]
  have hh := global_cost_linear c m d K (CompactGlobalReservation.shape c m d D G K 1).bits ell w hc hK xs (hx.trans hv.symm)
  rwa [hv] at hh

end
end IntegerMultBounds.Machine.NativeZeroPaddingBudget
