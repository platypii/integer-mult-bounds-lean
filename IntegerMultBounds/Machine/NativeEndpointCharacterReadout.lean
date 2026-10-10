import IntegerMultBounds.Machine.NativeEndpointCharacterAddress
import IntegerMultBounds.Networks.ComplexEndpoints

/-! The literal low-first aggregate scanner computes the actual product of
binary sign characters on every original runtime column. No address or
phase compatibility assumption is supplied. -/
namespace IntegerMultBounds.Machine.NativeEndpointCharacterReadout
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open ActivePrefixStageRuntimeOrdinal (highCoordinates reverseAxis)
open NativeEndpointCharacterAddress (reverseSlot)
open Networks
variable {s : Shape}

def weights (v : Stage s) (u : BinaryWalsh.Address v.slots) : List (ZMod 4) :=
  List.ofFn (fun i : Fin v.slots => BinaryPhase.doubleLift (u (reverseSlot v i)))

def coordinates (v : Stage s) {rows : ℕ} (k : Fin (rows*s.recordWidth)) (j : Fin v.f) :=
  BinaryRowColumns.coordinates (highCoordinates v k) j

private theorem weighted_bit (u : ZMod 2) (b : Bool) :
    (if b then BinaryPhase.doubleLift u else 0)=
      BinaryPhase.doubleLift (u*BinaryRowColumns.scalar b) := by
  cases b <;> simp [BinaryRowColumns.scalar]

theorem accumulator (v : Stage s) (u : BinaryWalsh.Address v.slots)
    {rows : ℕ} (k : Fin (rows*s.recordWidth)) :
    ((AllAxisPhaseFlagsCaller.phase v v.slots (weights v u)
      (BinaryAddressTableData.row s.bits (k.val/s.payload))).val : ZMod 4)=
      ∑ j : Fin v.f,BinaryPhase.doubleLift (Labels.binary v.slots u (coordinates v k j)) := by
  unfold AllAxisPhaseFlagsCaller.phase
  rw [RepeatedWeightedPhaseAccumulator.accumulate_cast,RepeatedWeightedPhaseTensor.total_eq_fin_sum]
  simp only [Fin.val_zero,Nat.cast_zero,zero_add]
  have hlen : (weights v u).length=v.slots := by simp [weights]
  rw [hlen]
  change (∑ i : Fin v.slots,∑ j : Fin v.f,
    if (AllAxisPhaseFlagsCaller.controls v v.slots
      (BinaryAddressTableData.row s.bits (k.val/s.payload))).getD (i.val*v.f+j.val) false
    then (List.ofFn (fun i : Fin v.slots => BinaryPhase.doubleLift (u (reverseSlot v i)))).getD i.val 0 else 0)=_
  rw [Finset.sum_comm]
  have hinner (j : Fin v.f) :
      (∑ i : Fin v.slots,if (AllAxisPhaseFlagsCaller.controls v v.slots
        (BinaryAddressTableData.row s.bits (k.val/s.payload))).getD (i.val*v.f+j.val) false
        then (List.ofFn (fun i : Fin v.slots => BinaryPhase.doubleLift (u (reverseSlot v i)))).getD i.val 0 else 0)=
      BinaryPhase.doubleLift (Labels.binary v.slots u (coordinates v k (reverseAxis j))) := by
    have he (i : Fin v.slots) :
        (if (AllAxisPhaseFlagsCaller.controls v v.slots
          (BinaryAddressTableData.row s.bits (k.val/s.payload))).getD (i.val*v.f+j.val) false
          then (List.ofFn (fun i : Fin v.slots => BinaryPhase.doubleLift (u (reverseSlot v i)))).getD i.val 0 else 0)=
        BinaryPhase.doubleLift (u (reverseSlot v i)*
          BinaryRowColumns.scalar (highCoordinates v k (reverseAxis j) (reverseSlot v i))) := by
      rw [NativeEndpointCharacterAddress.selected,
        List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt),List.getElem_ofFn]
      exact weighted_bit _ _
    simp_rw [he]
    have hr := (CompactAllAxisPhaseReadout.reversal v.slots).sum_comp
      (fun i => BinaryPhase.doubleLift (u i*BinaryRowColumns.scalar (highCoordinates v k (reverseAxis j) i)))
    change (∑ i : Fin v.slots,BinaryPhase.doubleLift (u (reverseSlot v i)*
      BinaryRowColumns.scalar (highCoordinates v k (reverseAxis j) (reverseSlot v i))))=_ at hr
    rw [hr]
    simp only [Labels.binary,Labels.form_apply,zero_mul,sub_zero,coordinates,BinaryRowColumns.coordinates]
    exact (map_sum BinaryPhase.doubleLift _ _).symm
  simp_rw [hinner]
  exact (CompactAllAxisPhaseReadout.reversal v.f).sum_comp
    (fun j => BinaryPhase.doubleLift (Labels.binary v.slots u (coordinates v k j)))

private theorem phase_double (b : ZMod 2) :
    BinaryPhase.phase (BinaryPhase.doubleLift b)=BinaryWalsh.sign b := by
  fin_cases b
  · change BinaryPhase.phase 0=BinaryWalsh.sign 0
    simp
  · change Complex.I^2=(-1 : ℂ)
    exact Complex.I_sq

theorem character (v : Stage s) (u : BinaryWalsh.Address v.slots)
    {rows : ℕ} (k : Fin (rows*s.recordWidth)) :
    BinaryPhase.phase ((AllAxisPhaseFlagsCaller.phase v v.slots (weights v u)
      (BinaryAddressTableData.row s.bits (k.val/s.payload))).val : ZMod 4)=
      ∏ j : Fin v.f,BinaryWalsh.chi u (coordinates v k j) := by
  rw [accumulator,BinaryPhase.phase_sum]
  apply Finset.prod_congr rfl
  intro j _
  exact phase_double _

/-- Genuine signed-word arithmetic applies the entire endpoint character to
one polynomial coefficient; the strict signed guard is the existing codec guard. -/
theorem coefficient (v : Stage s) (u : BinaryWalsh.Address v.slots)
    {rows : ℕ} (k : Fin (rows*s.recordWidth))
    (xs : ℕ → List (Fin 2)) (b n : ℕ) (hw : ∀ j,(xs j).length=b+1)
    (hg : ∀ j : Fin 2,|ButterflySigned.signedValue b (xs j.val)|<(2^b : ℕ)) :
    let p := AllAxisPhaseFlagsCaller.phase v v.slots (weights v u)
      (BinaryAddressTableData.row s.bits (k.val/s.payload))
    ButterflySigned.complexValue
      (ButterflySigned.signedValue b (UnitPhaseNumerator.words p 0 xs))
      (ButterflySigned.signedValue b (UnitPhaseNumerator.words p 1 xs)) n=
      (∏ j : Fin v.f,BinaryWalsh.chi u (coordinates v k j))*
        ButterflySigned.complexValue (ButterflySigned.signedValue b (xs 0))
          (ButterflySigned.signedValue b (xs 1)) n := by
  have h := UnitPhaseSigned.words_phase
    (AllAxisPhaseFlagsCaller.phase v v.slots (weights v u)
      (BinaryAddressTableData.row s.bits (k.val/s.payload))) xs b n hw hg
  rw [character] at h
  exact h

end
end IntegerMultBounds.Machine.NativeEndpointCharacterReadout
