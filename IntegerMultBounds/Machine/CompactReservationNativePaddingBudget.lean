import IntegerMultBounds.Machine.CompactReservationPaddingHeaderBudget
import IntegerMultBounds.Machine.CompactReservationNativePadding
import IntegerMultBounds.Machine.NativeZeroPaddingBudget

/-! Uniform original-volume budget for the fixed reservation machine, paid
adapter synthesis, one genuine native zero pad and complete header cleanup. -/
namespace IntegerMultBounds.Machine.CompactReservationNativePaddingBudget
noncomputable section
open CompactReservationPaddingHeaders
open CompactFallbackAxisRun (Array Width volume)
open CompactGlobalRowPadding

def constant (c m : ℕ) := CompactReservedVolumeBudget.constant c m+
  CompactReservationPaddingHeaderBudget.constant c m+NativeZeroPaddingBudget.constant+3

theorem word_length {N : ℕ} (w : ℕ) (f : Fin N → ButterflyStreamData.Coefficient)
    (hw : ∀ i,(f i).1.length=w ∧ (f i).2.length=w) :
    (NativeZeroPaddingArray.word f).length=N*(2*(w+1)) := by
  unfold NativeZeroPaddingArray.word
  rw [List.length_flatten]
  have hh : (List.ofFn (fun i => ButterflyStreamData.encoded (f i))).map List.length=
      List.replicate N (2*(w+1)) := by
    rw [←List.ofFn_comp']
    have he : (fun i : Fin N => (ButterflyStreamData.encoded (f i)).length)=fun _ => 2*(w+1) := by
      funext i
      simp [ButterflyStreamData.encoded,DelimitedRadixRecord.complex,DelimitedRadixRecord.field,(hw i).1,(hw i).2]
      omega
    rw [he,List.ofFn_const]
  rw [hh,List.sum_replicate]
  simp

theorem original_word_length (D K ell q : ℕ) (f : Array D K ell) (hw : Width D K ell q f) :
    (NativeZeroPaddingArray.word f).length=volume D K ell q := by
  have hh := word_length (width D K q) f (by
    intro i
    have hi := hw i
    simp only [CompactFallbackHeaders.reservation,CompactFallbackHeaders.bits,ButterflyGuard.width,ButterflyGuard.halfWidth] at hi
    unfold width
    omega)
  rw [hh]
  unfold volume ButterflyAxisHeadersBudget.logicalVolume ButterflyAxisHeadersData.recordLength
    ButterflyAxisHeadersData.width CompactFallbackHeaders.reservation CompactFallbackHeaders.polynomials
    CompactFallbackHeaders.bits width
  unfold ButterflyAxisArray.Size
  ring

theorem cost_linear (inverse : Bool) (c m D K rho ell q d G : ℕ) (hc : 2≤c) (hm : 2≤m)
    (hd : 0<d) (hG : 0<G) (hK : 0<K)
    (hres : CompactReservedHeaders.reserved c m d G K≤D)
    (f : Array D K ell) (hw : Width D K ell q f) :
    CompactReservationNativePadding.cost inverse c m D K rho ell q d G f≤
      constant c m*volume D K ell q*CompactReservedHeaders.reserved c m d G K := by
  have h0 := CompactReservedVolumeBudget.cost_linear c m D K rho ell q d G hc hd hG hK hres
  have h1 := CompactReservationPaddingHeaderBudget.cost_linear c m D K rho ell q d G hc hm hd hG hK hres
  have hrow : rowAxes c m d≤D := by unfold CompactReservedHeaders.reserved CompactReservedHeaders.high at hres; omega
  let xs := NativeZeroPaddingArray.word (CompactReservedOriginal.result inverse c m D K rho ell q d G f)
  have hx := original_word_length D K ell q _ (CompactReservedOriginal.width_result inverse c m D K rho ell q d G f hw)
  have hv : NativeZeroPaddingBudget.volume (originalRows c m d K) ((D-rowAxes c m d)*K) ell (width D K q)=volume D K ell q := by
    have he := congrArg (fun n => n*K) (Nat.add_sub_of_le hrow)
    simp only [Nat.add_mul] at he
    unfold NativeZeroPaddingBudget.volume originalRows
    rw [←pow_add,he]
    unfold volume ButterflyAxisHeadersBudget.logicalVolume ButterflyAxisHeadersData.recordLength
      ButterflyAxisHeadersData.width CompactFallbackHeaders.reservation CompactFallbackHeaders.polynomials
      CompactFallbackHeaders.bits width
    ring
  have h2 := NativeZeroPaddingBudget.global_cost_linear c m d K ((D-rowAxes c m d)*K) ell (width D K q)
    (by omega) hK xs (hx.trans hv.symm)
  rw [hv] at h2
  have hV : 0<volume D K ell q := ButterflyAxisHeadersInstall.volume_pos _ _ _ (pow_pos (by decide) ell)
  have hr := (CompactReservedVolumeBudget.geometry c m D K d G hd hG hK hres).1
  have hVN := Nat.le_mul_of_pos_right (volume D K ell q) hr
  have hc1 := Nat.mul_le_mul_left (CompactReservationPaddingHeaderBudget.constant c m) hVN
  have hc2 := Nat.mul_le_mul_left NativeZeroPaddingBudget.constant hVN
  unfold CompactReservationNativePadding.cost constant
  dsimp only [xs] at h2
  nlinarith

end
end IntegerMultBounds.Machine.CompactReservationNativePaddingBudget
