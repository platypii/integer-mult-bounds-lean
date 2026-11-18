module

public import IntegerMultBounds.MathlibTM2.Cover.LabelHeaders
public import IntegerMultBounds.MathlibTM2.Cover.LabelSuffix

/-! Joint computation of the column-view dimensions on one descriptor bank. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.LabelPrepare
noncomputable section

open IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2.M8.RevMachine
open RecursiveInterchangeLayout (Descriptor volume)
open FlatCoordinateSchedule (bits bits_value bits_canonical)
variable {q : ℕ} (hq : 2 ≤ q)

/-- Reuse the suffix exponent and power slots for the middle field. -/
def middle :=
  seq (seq (seq (Headers.eraseAt (q := q) 14) (Headers.eraseAt 15))
    (Headers.productAt (q := q) 6 14 21 (by decide))) (Headers.powerAt hq 14 15 (by decide))

def program := seq (seq (LabelHeaders.prefixProgram hq) (LabelSuffix.program hq)) (middle hq)

def input (v : Descriptor) (k s t c : ℕ) : Fin 22 → Option (List Bool) :=
  ![none, none, none, some (bits v.beforeH), none, none, some (bits c), some (bits (k-s)),
    none, none, some (bits v.width), some (bits v.between), some (bits v.afterD), none, none,
    none, none, none, none, none, some (bits (k-1-t)), some (bits (t-s-1))]

theorem factors (v : Descriptor) (hp : 0 < volume q v) :
    v.beforeH ≤ volume q v ∧ v.between ≤ volume q v ∧ v.afterD ≤ volume q v := by
  refine ⟨Nat.le_of_dvd hp ⟨v.beforeRows*v.rows*q^v.width*v.between*q^v.width*v.afterD, ?_⟩,
    Nat.le_of_dvd hp ⟨v.beforeRows*v.rows*v.beforeH*q^v.width*q^v.width*v.afterD, ?_⟩,
    Nat.le_of_dvd hp ⟨v.beforeRows*v.rows*v.beforeH*q^v.width*v.between*q^v.width, ?_⟩⟩ <;>
    unfold volume <;> ac_rfl

theorem prepares (v : Descriptor) (k s t c B : ℕ) (hs : s < t) (ht : t < k)
    (hc : 0 < c) (hb : 0 < B) (hp : v.Positive) (hv : v.beforeH = B*q^(k*c)) :
    let u := LabelView.colView q c k s t B v
    ∃ d : Fin 22 → Option (List Bool),
      d 8 = some (bits u.beforeH) ∧ d 6 = some (bits u.width) ∧
      d 15 = some (bits u.between) ∧ d 13 = some (bits u.afterD) ∧
      (∀ i, (input v k s t c i).isSome = true → d i = input v k s t c i) ∧
      HoareTime (program hq) (fun x => x = Headers.bank (input v k s t c))
        (fun x => x = Headers.bank d)
        (34000 * volume q v) := by
  let d := input v k s t c
  obtain ⟨zs, rs, cz, _, hz, _, hpre⟩ := LabelHeaders.prefix_hoare hq (t := t)
    (d := d) (le_trans hs.le ht.le) hc hv hb (bits_canonical _) (bits_canonical _)
    (bits_canonical _) (bits_value _) (bits_value _) (bits_value _) rfl rfl rfl rfl
    (by intro i hi; fin_cases i <;> first | rfl | simp at hi)
  let p := RadixPowerDescriptor.bits hq ((k-s)*c)
  let dp := Function.update (Function.update (Function.update (Function.update d 5
    (some (DimensionProductDescriptor.bits (k-s) c))) 4 (some p)) 8 (some zs)) 9 (some rs)
  have hsuf := LabelSuffix.suffix_hoare hq (d := dp) v (k-1-t) c hc hp.2.2.2.1 hp.2.2.2.2
    rfl rfl rfl rfl rfl (by intro i hi; fin_cases i <;> first | rfl | simp at hi)
  let ds := LabelSuffix.ready (q := q) dp v (k-1-t) c
  have he := Headers.erase_step (q := q) (d := ds) (j := 14) (xs := bits ((k-1-t)*c)) rfl
  let de := Function.update ds (14 : Fin 22) none
  have hf := Headers.erase_step (q := q) (d := de) (j := 15) (xs := bits (q^((k-1-t)*c))) rfl
  let df := Function.update de (15 : Fin 22) none
  have hm := Headers.product_step (q := q) (d := df) (w := 6) (o := 14) (m := 21)
    (by decide) hc (bits_value (t-s-1)) (bits_canonical _) (bits_value c) (bits_canonical _)
    rfl rfl rfl rfl rfl rfl
  let e := DimensionProductDescriptor.bits (t-s-1) c
  let dm := Function.update df (14 : Fin 22) (some e)
  have hw := Headers.power_step hq (d := dm) (e := 14) (o := 15) (by decide)
    (DimensionProductDescriptor.bits_value (t-s-1) c) (DimensionProductDescriptor.bits_canonical _ _)
    rfl rfl rfl rfl
  refine ⟨_, ?_, rfl, ?_, rfl, ?_, ((hpre.seq hsuf).seq (((he.seq hf).seq hm).seq hw)).consequence
    (fun _ h => h) (fun _ h => h) ?_⟩
  · exact congrArg some ((Routines.canon cz).trans (congrArg bits hz))
  · exact congrArg some ((Routines.canon (RadixPowerDescriptor.bits_canonical hq _)).trans
      (congrArg bits (RadixPowerDescriptor.bits_value hq _)))
  · intro i hi
    fin_cases i <;> first | rfl | contradiction
  · let u := LabelView.colView q c k s t B v
    have hV := RecursiveAffinePrepare.volume_positive hq v hp
    have hvol : volume q u = volume q v := LabelView.colView_volume _ _ _ _ _ _ _ hv hs ht
    have hf := factors v hV
    have hu := factors u (hvol ▸ hV)
    rw [hvol] at hu
    have hq' : 0 < q := by omega
    have htail : q^((k-1-t)*c) ≤ u.afterD := Nat.le_mul_of_pos_right _
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (pow_pos hq' _) hp.2.2.2.1) (pow_pos hq' _)) hp.2.2.2.2)
    have hm : (t-s-1)*c ≤ u.between := (Nat.lt_pow_self (by omega : 1 < q)).le
    have he := Nat.lt_pow_self (n := (k-1-t)*c) (by omega : 1 < q)
    have hl := FlatCoordinateDimensions.bits_length_le_twice (htail.trans hu.2.2) hV
    have hl' := FlatCoordinateDimensions.bits_length_le_twice (he.le.trans (htail.trans hu.2.2)) hV
    change _ ≤ 34000 * volume q v
    obtain ⟨_, hmid, hend⟩ := hu
    change q^((k-1-t)*c)*(q^v.width*v.between*q^v.width*v.afterD) ≤ _ at hend
    change q^((t-s-1)*c) ≤ _ at hmid
    change (t-s-1)*c ≤ q^((t-s-1)*c) at hm
    omega

end
end IntegerMultBounds.MathlibTM2.Cover.LabelPrepare
