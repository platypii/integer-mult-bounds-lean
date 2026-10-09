import IntegerMultBounds.Machine.BinarySelectedOffsetRepeatConstruct

/-! Selected repetition has the same paid metadata/copying layout as parity
repetition, with exchanged source/target widths and the selected producer's
larger constant. Its allowance is explicitly charged to record width. -/
namespace IntegerMultBounds.Machine.BinarySelectedOffsetRepeatBudget

def constant := BinaryAddressOffsetRepeatConstructBudget.constant+50
def volume (q b n P H L B : ℕ) := (P*2^(n*q))*(H*2^(n*b)*L)*2^(n*q)*B

theorem cost_eq (hs : Fin 6 → List Bool) (q b n P H L : ℕ) :
    BinarySelectedOffsetRepeatConstruct.cost hs q b n P H L=
      BinaryAddressOffsetRepeatConstruct.cost hs b q n P H L+
        50*(2^(n*b)*BinarySelectedOffset.allowance q b n) := by
  unfold BinarySelectedOffsetRepeatConstruct.cost BinaryAddressOffsetRepeatConstruct.cost
  have hd : BinarySelectedOffsetRepeatConstruct.descriptors hs q b n P H=
      BinaryAddressOffsetRepeatConstruct.descriptors hs b q n P H := rfl
  have hc : BinaryDescriptorCleanupList.cost BinarySelectedOffsetRepeatConstruct.cleanupSlots
      (BinarySelectedOffsetRepeatConstruct.cleanupBits q b n P H)=
      BinaryDescriptorCleanupList.cost BinaryAddressOffsetRepeatConstruct.cleanupSlots
        (BinaryAddressOffsetRepeatConstruct.cleanupBits b q n P H) := rfl
  rw [hd,hc]
  unfold BinarySelectedOffset.constant BinaryAddressOffset.constant BinarySelectedOffset.allowance BinaryAddressOffset.allowance
  ring

theorem cost_volume (hs : Fin 6 → List Bool) (q b n P H L B : ℕ)
    (hP : 0<P) (hH : 0<H) (hL : 0<L) (hvL : Counter.value (hs 5)=L)
    (hcL : GrowingCounterData.Canonical (hs 5)) (hB : BinarySelectedOffset.allowance q b n≤B) :
    BinarySelectedOffsetRepeatConstruct.cost hs q b n P H L≤constant*volume q b n P H L B := by
  have hA : BinaryAddressOffset.allowance b q n=BinarySelectedOffset.allowance q b n := by
    unfold BinaryAddressOffset.allowance BinarySelectedOffset.allowance; ring
  have hmain := BinaryAddressOffsetRepeatConstructBudget.cost_volume hs b q n P H L B
    hP hH hL hvL hcL (by rwa [hA])
  have hNV : 2^(n*b)*B≤volume q b n P H L B := by
    have hK : 0<(P*H)*2^(n*q) := Nat.mul_pos (Nat.mul_pos hP hH) (by positivity)
    have hN : 2^(n*b)≤((P*H)*2^(n*q))*2^(n*b) := Nat.le_mul_of_pos_left _ hK
    have hL' := Nat.le_mul_of_pos_right (((P*H)*2^(n*q))*2^(n*b)) hL
    have hT := Nat.le_mul_of_pos_right ((((P*H)*2^(n*q))*2^(n*b))*L) (by positivity : 0<2^(n*q))
    have h := Nat.mul_le_mul_right B (hN.trans (hL'.trans hT))
    convert h using 1; unfold volume; ring
  have hAV := (Nat.mul_le_mul_left (2^(n*b)) hB).trans hNV
  have hextra := Nat.mul_le_mul_left 50 hAV
  change BinaryAddressOffsetRepeatConstruct.cost hs b q n P H L≤
    BinaryAddressOffsetRepeatConstructBudget.constant*volume q b n P H L B at hmain
  rw [cost_eq]
  unfold constant
  nlinarith

end IntegerMultBounds.Machine.BinarySelectedOffsetRepeatBudget
