import IntegerMultBounds.Machine.BinaryParityXorOffsetRepeatConstruct
import IntegerMultBounds.Machine.BinarySelectedOffsetRepeatBudget

/-! Negative parity-XOR repetition has the same paid metadata/copying layout as parity
repetition, with the negative parity-XOR producer's
larger constant. Its allowance is explicitly charged to record width. -/
namespace IntegerMultBounds.Machine.BinaryParityXorOffsetRepeatBudget

def constant := BinarySelectedOffsetRepeatBudget.constant+1000
def volume (q b n P H L B : ℕ) := (P*2^(n*b))*(H*2^(n*q)*L)*2^(n*b)*B

theorem cost_eq (hs : Fin 6 → List Bool) (q b n P H L : ℕ) :
    BinaryParityXorOffsetRepeatConstruct.cost hs q b n P H L=
      BinarySelectedOffsetRepeatConstruct.cost hs b q n P H L+
        1000*(2^(n*q)*BinaryParityXorOffset.allowance q b n) := by
  unfold BinaryParityXorOffsetRepeatConstruct.cost BinarySelectedOffsetRepeatConstruct.cost
  have hd : BinaryParityXorOffsetRepeatConstruct.descriptors hs q b n P H=
      BinarySelectedOffsetRepeatConstruct.descriptors hs b q n P H := rfl
  have hc : BinaryDescriptorCleanupList.cost BinaryParityXorOffsetRepeatConstruct.cleanupSlots
      (BinaryParityXorOffsetRepeatConstruct.cleanupBits q b n P H)=
      BinaryDescriptorCleanupList.cost BinarySelectedOffsetRepeatConstruct.cleanupSlots
        (BinarySelectedOffsetRepeatConstruct.cleanupBits b q n P H) := rfl
  rw [hd,hc]
  unfold BinaryParityXorOffset.constant BinarySelectedOffset.constant BinaryParityXorOffset.allowance BinarySelectedOffset.allowance
  ring

theorem cost_volume (hs : Fin 6 → List Bool) (q b n P H L B : ℕ)
    (hP : 0<P) (hH : 0<H) (hL : 0<L) (hvL : Counter.value (hs 5)=L)
    (hcL : GrowingCounterData.Canonical (hs 5)) (hB : BinaryParityXorOffset.allowance q b n≤B) :
    BinaryParityXorOffsetRepeatConstruct.cost hs q b n P H L≤constant*volume q b n P H L B := by
  have hA : BinarySelectedOffset.allowance b q n=BinaryParityXorOffset.allowance q b n := by
    unfold BinarySelectedOffset.allowance BinaryParityXorOffset.allowance; ring
  have hmain := BinarySelectedOffsetRepeatBudget.cost_volume hs b q n P H L B
    hP hH hL hvL hcL (by rwa [hA])
  have hNV : 2^(n*q)*B≤volume q b n P H L B := by
    have hK : 0<(P*H)*2^(n*b) := Nat.mul_pos (Nat.mul_pos hP hH) (by positivity)
    have hN : 2^(n*q)≤((P*H)*2^(n*b))*2^(n*q) := Nat.le_mul_of_pos_left _ hK
    have hL' := Nat.le_mul_of_pos_right (((P*H)*2^(n*b))*2^(n*q)) hL
    have hT := Nat.le_mul_of_pos_right ((((P*H)*2^(n*b))*2^(n*q))*L) (by positivity : 0<2^(n*b))
    have h := Nat.mul_le_mul_right B (hN.trans (hL'.trans hT))
    convert h using 1; unfold volume; ring
  have hAV := (Nat.mul_le_mul_left (2^(n*q)) hB).trans hNV
  have hextra := Nat.mul_le_mul_left 1000 hAV
  change BinarySelectedOffsetRepeatConstruct.cost hs b q n P H L≤
    BinarySelectedOffsetRepeatBudget.constant*volume q b n P H L B at hmain
  rw [cost_eq]
  unfold constant
  nlinarith

end IntegerMultBounds.Machine.BinaryParityXorOffsetRepeatBudget
