module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Arith
public import IntegerMultBounds.MathlibTM2.Cover.LabelView

/-! Extracting the prefix header of a label-column view by exact division. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.LabelHeaders

open IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2.M8.RevMachine
open RecursiveInterchangeLayout (Descriptor)
variable {q : ℕ} (hq : 2 ≤ q)

/-- The divisor varies with the column width. Both word lengths are bounded by the
canonical width of the dividend, giving a uniform linear cost. -/
theorem div_cost (ys ds : List Bool) (cy : GrowingCounterData.Canonical ys)
    (cd : GrowingCounterData.Canonical ds) (hle : Counter.value ds ≤ Counter.value ys) :
    BinaryDescriptorDivMod.cost ys ds ≤ 16000 * (Counter.value ys + 1) := by
  have hy := BinaryDescriptorDivMod.descriptor_square ys cy
  have hd := BinaryDescriptorDivMod.descriptor_square ds cd
  have h := BinaryDescriptorDivMod.cost_le ys ds
  rcases le_total ys.length ds.length with hlen | hlen
  · nlinarith [Nat.mul_le_mul_right ds.length hlen, Nat.le_self_pow (by decide : 2 ≠ 0) ds.length]
  · nlinarith [Nat.mul_le_mul_left ys.length hlen, Nat.le_self_pow (by decide : 2 ≠ 0) ys.length]

noncomputable def prefixProgram :=
  seq (seq (Headers.productAt (q := q) 6 5 7 (by decide)) (Headers.powerAt hq 5 4 (by decide)))
    (Arith.split (q := q))

/-- From the parent prefix, column width and number of remaining columns,
compute the view prefix in slot 8. Slot 4 retains the power and slot 9 the zero remainder. -/
theorem prefix_hoare {k s t c B : ℕ} {v : Descriptor}
    (hs : s ≤ k) (hc : 0 < c) (hv : v.beforeH = B * q^(k*c)) (hb : 0 < B)
    {d : Fin 22 → Option (List Bool)} {ys cs ns : List Bool}
    (cy : GrowingCounterData.Canonical ys) (cc : GrowingCounterData.Canonical cs)
    (cn : GrowingCounterData.Canonical ns)
    (hy : Counter.value ys = v.beforeH) (hwidth : Counter.value cs = c) (hn : Counter.value ns = k-s)
    (h3 : d 3 = some ys) (h6 : d 6 = some cs) (h7 : d 7 = some ns)
    (h5 : d 5 = none)
    (hblank : ∀ i : Fin 22, i ∈ [0,1,2,4,8,9,13,14,15,16,17,18,19] → d i = none) :
    let p := RadixPowerDescriptor.bits hq ((k-s)*c)
    ∃ zs rs, GrowingCounterData.Canonical zs ∧ GrowingCounterData.Canonical rs ∧
      Counter.value zs = (LabelView.colView q c k s t B v).beforeH ∧ Counter.value rs = 0 ∧
      HoareTime (prefixProgram hq) (fun x => x = Headers.bank d)
        (fun x => x = Headers.bank (Function.update (Function.update
          (Function.update (Function.update d 5 (some (DimensionProductDescriptor.bits (k-s) c))) 4 (some p)) 8 (some zs)) 9 (some rs))) (16200*(v.beforeH+1)) := by
  let p := RadixPowerDescriptor.bits hq ((k-s)*c)
  let e := DimensionProductDescriptor.bits (k-s) c
  let de := Function.update d 5 (some e)
  let d' := Function.update de 4 (some p)
  have hv' : Counter.value ys = (B*q^(s*c))*q^((k-s)*c) := by
    rw [hy, hv, Nat.mul_assoc, ← pow_add, ← Nat.add_mul, Nat.add_sub_of_le hs]
  have hpos : 0 < Counter.value p := by simp [p]; positivity
  have hprod := Headers.product_step (q := q) (w := 6) (o := 5) (m := 7) (by decide) hc hn cn hwidth cc h6 h7
    (hblank _ (by simp)) (hblank _ (by simp)) (hblank _ (by simp)) h5
  have hpow := Headers.power_step hq (e := 5) (o := 4) (d := de) (by decide)
    (DimensionProductDescriptor.bits_value (k-s) c) (DimensionProductDescriptor.bits_canonical _ _)
    (by simp [de, e])
    (by simpa [de] using hblank 0 (by simp)) (by simpa [de] using hblank 1 (by simp))
    (by simpa [de] using hblank 4 (by simp))
  obtain ⟨zs, rs, cz, cr, hz, hr, hdiv⟩ := Arith.split_hoare (q := q) (d := d') hpos
    (by simpa [d', de] using h3) (by simp [d', de]) (by simpa [d', de] using hblank 8 (by simp))
    (by simpa [d', de] using hblank 9 (by simp)) (by
      intro i hi
      have hn : i ≠ 4 := by rintro rfl; simp at hi
      rw [show d' i = de i from Function.update_of_ne hn _ _]
      have hn5 : i ≠ 5 := by rintro rfl; simp at hi
      rw [show de i = d i from Function.update_of_ne hn5 _ _]
      apply hblank
      simp only [List.mem_cons] at hi ⊢
      tauto)
  have hd : Counter.value p ≤ Counter.value ys := by
    rw [hv', RadixPowerDescriptor.bits_value]
    exact Nat.le_mul_of_pos_left _ (Nat.mul_pos hb (pow_pos (by omega) _))
  refine ⟨zs, rs, cz, cr, ?_, ?_, ((hprod.seq hpow).seq hdiv).consequence (fun _ h => h) (fun _ h => h) ?_⟩
  · rw [hz, hv', RadixPowerDescriptor.bits_value, Nat.mul_div_cancel _ (by simpa [p] using hpos)]
    rfl
  · rw [hr, hv', RadixPowerDescriptor.bits_value, Nat.mul_mod_left]
  · have hc := div_cost ys p cy (RadixPowerDescriptor.bits_canonical hq _) hd
    rw [RadixPowerDescriptor.bits_value] at hd
    have := Nat.lt_pow_self (n := (k-s)*c) (by omega : 1 < q)
    omega

end IntegerMultBounds.MathlibTM2.Cover.LabelHeaders
