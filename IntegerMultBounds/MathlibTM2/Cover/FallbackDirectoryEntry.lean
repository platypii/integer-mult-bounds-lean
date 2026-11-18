module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPhysicalLabel
public import IntegerMultBounds.MathlibTM2.Cover.LabelDirectory

/-! Locate one full prime-power matrix entry in a physical directory record. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine RadixDigits FlatCoordinateLayout
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)

private theorem splitValue {q : ℕ} (xs : List (Fin q)) (k : ℕ) (hk : k ≤ xs.length) :
    value xs = value (xs.take k) + q^k * value (xs.drop k) := by
  induction k generalizing xs with
  | zero => simp [value]
  | succ k ih =>
    cases xs with
    | nil => simp at hk
    | cons x xs =>
      simp only [List.take_succ_cons,List.drop_succ_cons,value,pow_succ]
      rw [ih xs (by simpa using hk)]
      ring

theorem directoryEntry_value (m w j : ℕ) (r c : Fin m) :
    let offset := w * suffixFields (finProdFinEquiv (c,r))
    value (((LabelDirectory.digits m w j).drop offset).take w) = (physicalLabel m w j r c).val := by
  intro offset
  let xs := LabelDirectory.digits m w j
  have len : xs.length = w*(m*m) := by simp [xs,LabelDirectory.digits]
  have bound : offset+w ≤ xs.length := by
    rw [len,← Nat.mul_one w,← Nat.mul_add,Nat.mul_one]
    apply Nat.mul_le_mul_left
    have h := (finProdFinEquiv (c,r)).isLt
    change m*m-1- _ + 1 ≤ m*m
    omega
  have lowDigits := splitValue xs offset (by omega)
  have middle := splitValue (xs.drop offset) w (by simp; omega)
  have lo := value_lt prime_prime.two_le (xs.take offset)
  have hi := value_lt prime_prime.two_le ((xs.drop offset).take w)
  rw [List.length_take,Nat.min_eq_left (by omega)] at lo
  rw [List.length_take,Nat.min_eq_left (by simp; omega)] at hi
  have coeff := LabelDirectory.coefficient_at m w (j/(prime^w)^(m*m)) (physicalLabel m w j) r c
  rw [physicalLabel_index,← pow_mul] at coeff
  change value xs / prime^offset % prime^w = _ at coeff
  rw [lowDigits,Nat.add_mul_div_left _ _ (pow_pos prime_prime.pos _),Nat.div_eq_of_lt lo,Nat.zero_add,
    middle,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hi] at coeff
  exact coeff

end IntegerMultBounds.MathlibTM2.Cover.Fallback
