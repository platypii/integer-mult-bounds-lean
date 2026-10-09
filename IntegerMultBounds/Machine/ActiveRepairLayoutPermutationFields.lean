import IntegerMultBounds.Machine.VaryingControlRepairPacked
import IntegerMultBounds.Machine.ActiveRepairLateFieldsValue
import IntegerMultBounds.Machine.ActiveRepairEarlyFieldsValue
import IntegerMultBounds.Machine.ActiveRepairRankHeadersData

/-! Exact binary-field equivalences for the varying-control packed address.
The target remains in active coordinates; neither wide field is reserved in H. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutPermutationFields
noncomputable section
open IntegerMultBounds.Compact IntegerMultBounds.Compact.PowerTwo

abbrev RawEarly (q b n : ℕ) := Fin (2^(n*q)) × Fin (2^(n*b))
abbrev RawLate (q b n : ℕ) := Fin (2^(n*b)) × RawEarly q b n

theorem target_size (q n : ℕ) (Z : List Bool) (hq : 1≤q) (hZ : Z.length=n) :
    ((2*Li q)^(controls Z).length).toNat=2^(n*q) := by
  rw [twoL_pow q Z hq,hZ]
  norm_cast

theorem temp_size (b n : ℕ) (Z : List Bool) (hZ : Z.length=n) :
    ((Bi b)^(controls Z).length).toNat=2^(n*b) := by
  rw [B_pow b Z,hZ]
  norm_cast

def targetEquiv (q n : ℕ) (Z : List Bool) (hq : 1≤q) (hZ : Z.length=n) :
    Fin (2^(n*q)) ≃ Compact.Field ((2*Li q)^(controls Z).length) :=
  (finCongr (target_size q n Z hq hZ).symm).trans
    (fieldFin ((2*Li q)^(controls Z).length) (by positivity)).symm

def tempEquiv (b n : ℕ) (Z : List Bool) (hZ : Z.length=n) :
    Fin (2^(n*b)) ≃ Compact.Field ((Bi b)^(controls Z).length) :=
  (finCongr (temp_size b n Z hZ).symm).trans
    (fieldFin ((Bi b)^(controls Z).length) (by positivity)).symm

def earlyEquiv (q b n : ℕ) (Z : List Bool) (hq : 1≤q) (hZ : Z.length=n) :
    RawEarly q b n ≃ EarlyAddress (Bi b) (Li q) (controls Z).length :=
  Equiv.prodCongr (targetEquiv q n Z hq hZ) (tempEquiv b n Z hZ)
def lateEquiv (q b n : ℕ) (Z : List Bool) (hq : 1≤q) (hZ : Z.length=n) :
    RawLate q b n ≃ LateAddress (Bi b) (Li q) (controls Z).length :=
  Equiv.prodCongr (tempEquiv b n Z hZ) (earlyEquiv q b n Z hq hZ)

@[simp] theorem target_value (q n : ℕ) (Z : List Bool) (hq : 1≤q) (hZ : Z.length=n)
    (v : Fin (2^(n*q))) : (targetEquiv q n Z hq hZ v).val=(v.val : ℤ) := rfl
@[simp] theorem temp_value (b n : ℕ) (Z : List Bool) (hZ : Z.length=n)
    (v : Fin (2^(n*b))) : (tempEquiv b n Z hZ v).val=(v.val : ℤ) := rfl

end
end IntegerMultBounds.Machine.ActiveRepairLayoutPermutationFields
