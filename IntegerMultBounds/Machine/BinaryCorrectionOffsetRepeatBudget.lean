import IntegerMultBounds.Machine.BinaryCorrectionOffsetRepeatConstruct
import IntegerMultBounds.Machine.BinarySelectedOffsetRepeatBudget

/-! Correction repetition has the same paid metadata/copying layout as parity
repetition, with the correction producer's
larger constant. Its allowance is explicitly charged to record width. -/
namespace IntegerMultBounds.Machine.BinaryCorrectionOffsetRepeatBudget

def constant := BinarySelectedOffsetRepeatBudget.constant+1000
def volume (q b n P H L B : ℕ) := (P*2^(n*q))*(H*2^(n*b)*L)*2^(n*q)*B

theorem cost_eq (hs : Fin 6 → List Bool) (q b n P H L : ℕ) :
    BinaryCorrectionOffsetRepeatConstruct.cost hs q b n P H L=
      BinarySelectedOffsetRepeatConstruct.cost hs q b n P H L+
        1000*(2^(n*b)*BinaryCorrectionOffset.allowance q b n) := by
  unfold BinaryCorrectionOffsetRepeatConstruct.cost BinarySelectedOffsetRepeatConstruct.cost
  have hd : BinaryCorrectionOffsetRepeatConstruct.descriptors hs q b n P H=
      BinarySelectedOffsetRepeatConstruct.descriptors hs q b n P H := rfl
  have hc : BinaryDescriptorCleanupList.cost BinaryCorrectionOffsetRepeatConstruct.cleanupSlots
      (BinaryCorrectionOffsetRepeatConstruct.cleanupBits q b n P H)=
      BinaryDescriptorCleanupList.cost BinarySelectedOffsetRepeatConstruct.cleanupSlots
        (BinarySelectedOffsetRepeatConstruct.cleanupBits q b n P H) := rfl
  rw [hd,hc]
  unfold BinaryCorrectionOffset.constant BinarySelectedOffset.constant BinaryCorrectionOffset.allowance BinarySelectedOffset.allowance
  ring

theorem cost_volume (hs : Fin 6 → List Bool) (q b n P H L B : ℕ)
    (hP : 0<P) (hH : 0<H) (hL : 0<L) (hvL : Counter.value (hs 5)=L)
    (hcL : GrowingCounterData.Canonical (hs 5)) (hB : BinaryCorrectionOffset.allowance q b n≤B) :
    BinaryCorrectionOffsetRepeatConstruct.cost hs q b n P H L≤constant*volume q b n P H L B := by
  have hA : BinarySelectedOffset.allowance q b n=BinaryCorrectionOffset.allowance q b n := by
    unfold BinarySelectedOffset.allowance BinaryCorrectionOffset.allowance; ring
  have hmain := BinarySelectedOffsetRepeatBudget.cost_volume hs q b n P H L B
    hP hH hL hvL hcL (by rwa [hA])
  have hNV : 2^(n*b)*B≤volume q b n P H L B := by
    have hK : 0<(P*H)*2^(n*q) := Nat.mul_pos (Nat.mul_pos hP hH) (by positivity)
    have hN : 2^(n*b)≤((P*H)*2^(n*q))*2^(n*b) := Nat.le_mul_of_pos_left _ hK
    have hL' := Nat.le_mul_of_pos_right (((P*H)*2^(n*q))*2^(n*b)) hL
    have hT := Nat.le_mul_of_pos_right ((((P*H)*2^(n*q))*2^(n*b))*L) (by positivity : 0<2^(n*q))
    have h := Nat.mul_le_mul_right B (hN.trans (hL'.trans hT))
    convert h using 1; unfold volume; ring
  have hAV := (Nat.mul_le_mul_left (2^(n*b)) hB).trans hNV
  have hextra := Nat.mul_le_mul_left 1000 hAV
  change BinarySelectedOffsetRepeatConstruct.cost hs q b n P H L≤
    BinarySelectedOffsetRepeatBudget.constant*volume q b n P H L B at hmain
  rw [cost_eq]
  unfold constant
  nlinarith

end IntegerMultBounds.Machine.BinaryCorrectionOffsetRepeatBudget
