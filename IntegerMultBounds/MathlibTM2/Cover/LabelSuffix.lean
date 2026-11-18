module

public import IntegerMultBounds.MathlibTM2.Cover.LabelView
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Routines

/-! The suffix header of the label view, including the parent payload. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.LabelSuffix
noncomputable section

open IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2.M8.RevMachine
open FlatCoordinateSchedule (bits bits_value bits_canonical)
open RecursiveInterchangeLayout (Descriptor)
variable {q : ℕ} (hq : 2 ≤ q)

def program :=
  seq (seq (seq (seq (seq (seq (Headers.productAt (q := q) 6 14 20 (by decide))
    (Headers.powerAt hq 14 15 (by decide)))
    (Headers.powerAt hq 10 16 (by decide)))
    (Headers.productAt (q := q) 11 17 16 (by decide)))
    (Headers.productAt (q := q) 16 18 17 (by decide)))
    (Headers.productAt (q := q) 12 19 18 (by decide)))
    (Headers.productAt (q := q) 19 13 15 (by decide))

/-- The arithmetic fills slots 14 through 19, then slot 13. -/
def ready (d : Fin 22 → Option (List Bool)) (v : Descriptor) (n c : ℕ) :=
  let d := Function.update d 14 (some (bits (n*c)))
  let d := Function.update d 15 (some (bits (q^(n*c))))
  let d := Function.update d 16 (some (bits (q^v.width)))
  let d := Function.update d 17 (some (bits (q^v.width*v.between)))
  let d := Function.update d 18 (some (bits (q^v.width*v.between*q^v.width)))
  let d := Function.update d 19 (some (bits (q^v.width*v.between*q^v.width*v.afterD)))
  Function.update d 13 (some (bits (q^(n*c)*(q^v.width*v.between*q^v.width*v.afterD))))

@[simp] theorem ready_suffix (d : Fin 22 → Option (List Bool)) (v : Descriptor)
    (c k s t B : ℕ) :
    ready (q := q) d v (k-1-t) c 13 =
      some (bits (LabelView.colView q c k s t B v).afterD) := rfl

/-- The runtime counters give the column width and the number of columns to the right.
The last product in slot 13 is the complete suffix of the column view. -/
theorem suffix_hoare {d : Fin 22 → Option (List Bool)} (v : Descriptor) (n c : ℕ)
    (hc : 0 < c) (hm : 0 < v.between) (he : 0 < v.afterD)
    (h6 : d 6 = some (bits c)) (h10 : d 10 = some (bits v.width))
    (h11 : d 11 = some (bits v.between)) (h12 : d 12 = some (bits v.afterD))
    (h20 : d 20 = some (bits n))
    (hb : ∀ i : Fin 22, i ∈ [0,1,2,14,15,16,17,18,19,13] → d i = none) :
    HoareTime (program hq) (fun x => x = Headers.bank d)
      (fun x => x = Headers.bank (ready (q := q) d v n c))
      (700 * (q^(n*c)*(q^v.width*v.between*q^v.width*v.afterD))) := by
  have hq' : 0 < q := by omega
  let d1 := Function.update d (14 : Fin 22) (some (bits (n*c)))
  have h1 := Headers.product_step (q := q) (d := d) (m := 20) (w := 6) (o := 14) (by decide)
    (by positivity : 0 < c) (bits_value (n)) (bits_canonical _) (bits_value (c)) (bits_canonical _)
    h6 h20 (hb 0 (by simp)) (hb 1 (by simp)) (hb 2 (by simp)) (hb 14 (by simp))
  rw [Routines.canon (DimensionProductDescriptor.bits_canonical _ _), DimensionProductDescriptor.bits_value] at h1
  let d2 := Function.update d1 (15 : Fin 22) (some (bits (q^(n*c))))
  have h2 := Headers.power_step hq (d := d1) (e := 14) (o := 15) (by decide) (bits_value (n*c)) (bits_canonical _)
    rfl (hb 0 (by simp)) (hb 1 (by simp)) (hb 15 (by simp))
  rw [Routines.canon (RadixPowerDescriptor.bits_canonical _ _), RadixPowerDescriptor.bits_value] at h2
  let d3 := Function.update d2 (16 : Fin 22) (some (bits (q^v.width)))
  have h3 := Headers.power_step hq (d := d2) (e := 10) (o := 16) (by decide) (bits_value (v.width)) (bits_canonical _)
    h10 (hb 0 (by simp)) (hb 1 (by simp)) (hb 16 (by simp))
  rw [Routines.canon (RadixPowerDescriptor.bits_canonical _ _), RadixPowerDescriptor.bits_value] at h3
  let d4 := Function.update d3 (17 : Fin 22) (some (bits (q^v.width*v.between)))
  have h4 := Headers.product_step (q := q) (d := d3) (m := 16) (w := 11) (o := 17) (by decide)
    (by positivity : 0 < v.between) (bits_value (q^v.width)) (bits_canonical _) (bits_value (v.between)) (bits_canonical _)
    h11 rfl (hb 0 (by simp)) (hb 1 (by simp)) (hb 2 (by simp)) (hb 17 (by simp))
  rw [Routines.canon (DimensionProductDescriptor.bits_canonical _ _), DimensionProductDescriptor.bits_value] at h4
  let d5 := Function.update d4 (18 : Fin 22) (some (bits (q^v.width*v.between*q^v.width)))
  have h5 := Headers.product_step (q := q) (d := d4) (m := 17) (w := 16) (o := 18) (by decide)
    (by positivity : 0 < q^v.width) (bits_value (q^v.width*v.between)) (bits_canonical _) (bits_value (q^v.width)) (bits_canonical _)
    rfl rfl (hb 0 (by simp)) (hb 1 (by simp)) (hb 2 (by simp)) (hb 18 (by simp))
  rw [Routines.canon (DimensionProductDescriptor.bits_canonical _ _), DimensionProductDescriptor.bits_value] at h5
  let d6 := Function.update d5 (19 : Fin 22) (some (bits (q^v.width*v.between*q^v.width*v.afterD)))
  have h6' := Headers.product_step (q := q) (d := d5) (m := 18) (w := 12) (o := 19) (by decide)
    (by positivity : 0 < v.afterD) (bits_value (q^v.width*v.between*q^v.width)) (bits_canonical _) (bits_value (v.afterD)) (bits_canonical _)
    h12 rfl (hb 0 (by simp)) (hb 1 (by simp)) (hb 2 (by simp)) (hb 19 (by simp))
  rw [Routines.canon (DimensionProductDescriptor.bits_canonical _ _), DimensionProductDescriptor.bits_value] at h6'
  let d7 := Function.update d6 (13 : Fin 22) (some (bits (q^(n*c)*(q^v.width*v.between*q^v.width*v.afterD))))
  have h7 := Headers.product_step (q := q) (d := d6) (m := 15) (w := 19) (o := 13) (by decide)
    (by positivity : 0 < q^v.width*v.between*q^v.width*v.afterD) (bits_value (q^(n*c))) (bits_canonical _) (bits_value (q^v.width*v.between*q^v.width*v.afterD)) (bits_canonical _)
    rfl rfl (hb 0 (by simp)) (hb 1 (by simp)) (hb 2 (by simp)) (hb 13 (by simp))
  rw [Routines.canon (DimensionProductDescriptor.bits_canonical _ _), DimensionProductDescriptor.bits_value] at h7
  apply ((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6').seq h7).consequence
    (fun _ h => h) (fun _ h => h) ?_
  have hn := Nat.lt_pow_self (n := n*c) (by omega : 1 < q)
  have hp : 0 < q^(n*c) := pow_pos hq' _
  have hw : 0 < q^v.width := pow_pos hq' _
  have h₁ := Nat.le_mul_of_pos_right (q^v.width) hm
  have h₂ := Nat.le_mul_of_pos_right (q^v.width*v.between) hw
  have h₃ := Nat.le_mul_of_pos_right (q^v.width*v.between*q^v.width) he
  have h₄ := Nat.le_mul_of_pos_left (q^v.width*v.between*q^v.width*v.afterD) hp
  have h₅ := Nat.le_mul_of_pos_right (q^(n*c)) (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hw hm) hw) he)
  omega

end
end IntegerMultBounds.MathlibTM2.Cover.LabelSuffix
