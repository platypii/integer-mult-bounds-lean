import IntegerMultBounds.Machine.ActiveRepairLayoutPermutation
import IntegerMultBounds.Machine.ActiveRepairLayoutPermutationWords
import IntegerMultBounds.Machine.ActiveRepairEarlyKeyValue

/-! Global repaired low-bit ideals change precisely the target row by the
literal selected XOR mask; every other original address coordinate survives. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutIdealCoordinates
noncomputable section
open CompactGadgetReservationShape CompactActiveTargetLayout
open ActiveRepairLayoutPermutation ActiveRepairLayoutPermutationFields
open ActiveRepairLayoutPermutationWords
open IntegerMultBounds.Compact IntegerMultBounds.Compact.PowerTwo
open BinaryAddressTableData (row)

def targetFin (q n : ℕ) (Z : List Bool) (hq : 1≤q) (hZ : Z.length=n)
    (v : Fin (2^(n*q))) : Fin (2^(n*q)) :=
  wordFin _ (CountedIdealToggle.word q (row (n*q) v.val) Z)
    ((CountedIdealToggle.word_length q _ Z hq (by simp [hZ])).trans (by simp))

theorem target_native (q n : ℕ) (Z : List Bool) (hq : 1≤q) (hZ : Z.length=n)
    (v : Fin (2^(n*q))) :
    idealTarget (Li q) (Li_pos q) (controls Z) (controls_bits Z)
      (targetEquiv q n Z hq hZ v)=targetEquiv q n Z hq hZ (targetFin q n Z hq hZ v) := by
  apply Subtype.ext
  have h := idealTarget_value (Li q) (Li_pos q) (controls Z) (controls_bits Z)
    (targetEquiv q n Z hq hZ v)
  rw [target_value] at h
  have hpack (v : ℤ) : Radix.pack (2*Li q)
      (toggleList (Radix.digits (2*Li q) (controls Z).length v) (controls Z))=
      Radix.pack ((2 : ℤ)^q) (toggleList (Radix.digits ((2 : ℤ)^q) Z.length v) (controls Z)) := by
    rw [two_Li q hq,controls_length]
  rw [hpack] at h
  have ht := CountedIdealToggle.value q hq (row (n*q) v.val) Z (by simp [hZ])
  rw [BinaryAddressTableData.row_rank _ _ v.isLt] at ht
  exact h.trans ht.symm

theorem target_row (q n : ℕ) (Z : List Bool) (hq : 1≤q) (hZ : Z.length=n)
    (v : Fin (2^(n*q))) :
    row (n*q) (targetFin q n Z hq hZ v).val=
      CountedIdealToggle.word q (row (n*q) v.val) Z := by
  have hl : (CountedIdealToggle.word q (row (n*q) v.val) Z).length=n*q := by
    rw [CountedIdealToggle.word_length q _ Z hq (by simp [hZ])]
    simp
  have h := ActiveRepairEarlyKeyValue.word_row (CountedIdealToggle.word q (row (n*q) v.val) Z)
  rw [hl] at h
  exact h.symm

variable (s : Shape) (q b n before after rows rho offset width : ℕ)
variable (side : ActiveRepairRankHeadersData.SourceSide) (hq : 1≤q)
local notation "Addr" => Address s (n*b) (n*q) before after rows
local notation "ctrl" => ActiveRepairLayoutPermutationFiber.controlWord before after q rho n offset width side

def destination (x : Addr) : Addr :=
  {x with target := (targetFin q n (ctrl (x.activeBefore,x.activeAfter)) hq
    (ActiveRepairLayoutPermutationFiber.control_length _ _ _ _ _ _ _ _ _) x.target)}

theorem early_fields (x : Addr) :
    earlyIdeal s q b n before after rows rho offset width side hq x=
      destination s q b n before after rows rho offset width side hq x := by
  apply (earlyFiber s q b n before after rows rho offset width side hq).injective
  rw [early_ideal_fiber]
  refine Sigma.ext ?_ ?_
  · rfl
  · apply heq_of_eq
    apply Prod.ext
    · apply Prod.ext
      · exact target_native q n _ hq _ x.target
      · rfl
    · rfl

theorem late_fields (x : Addr) :
    lateIdeal s q b n before after rows rho offset width side hq x=
      destination s q b n before after rows rho offset width side hq x := by
  apply (lateFiber s q b n before after rows rho offset width side hq).injective
  rw [late_ideal_fiber]
  refine Sigma.ext ?_ ?_
  · rfl
  · apply heq_of_eq
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · exact target_native q n _ hq _ x.target
        · rfl
    · rfl

theorem early_target_row (x : Addr) :
    row (n*q) (earlyIdeal s q b n before after rows rho offset width side hq x).target.val=
      CountedIdealToggle.word q (row (n*q) x.target.val) (ctrl (x.activeBefore,x.activeAfter)) := by
  rw [early_fields]
  exact target_row q n _ hq (ActiveRepairLayoutPermutationFiber.control_length _ _ _ _ _ _ _ _ _) x.target

theorem late_target_row (x : Addr) :
    row (n*q) (lateIdeal s q b n before after rows rho offset width side hq x).target.val=
      CountedIdealToggle.word q (row (n*q) x.target.val) (ctrl (x.activeBefore,x.activeAfter)) := by
  rw [late_fields]
  exact target_row q n _ hq (ActiveRepairLayoutPermutationFiber.control_length _ _ _ _ _ _ _ _ _) x.target

end
end IntegerMultBounds.Machine.ActiveRepairLayoutIdealCoordinates
