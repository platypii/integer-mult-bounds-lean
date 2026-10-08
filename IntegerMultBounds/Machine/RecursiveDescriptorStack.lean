import IntegerMultBounds.Machine.RecursiveDescriptorSize
import IntegerMultBounds.Machine.BinaryDescriptorStackRoundtrip

/-! Charge real variable-length binary stack scans to the current recursive
child's logical volume. Older frames remain unchanged and never contribute to
the volume denominator. Integration around an intervening recursive call is
separate from this literal stack roundtrip. -/
namespace IntegerMultBounds.Machine.RecursiveDescriptorStack
open RecursiveInterchangeLayout RecursiveInterchangeVolume
variable {a : ℕ}

/-- The actual delimiter-based push/pop machine needs no length input. Even a
root-sized canonical header can be saved/restored within a fixed multiple of
logical child volume because all original chunk digits are retained. -/
theorem roundtrip_hoare_linear {q roles m n k : ℕ} {root v : Descriptor}
    (path : Path q roles m root n v) (hq : 2 ≤ q) (hr : 0 < roles)
    (hm : 2 ≤ m) (hw : root.width = m^k) (hv : root.Positive)
    (xs : List Bool) (hc : GrowingCounterData.Canonical xs)
    (hb : Counter.value xs ≤ volume q root) (f : ℤ → Fin (a+4)) (p : ℤ)
    (hf : ∀ z, p ≤ z → z < p+1+xs.length → f z = blank) :
    HoareTime BinaryDescriptorStackRoundtrip.program
      (fun w => w = BinaryDescriptorStackRoundtrip.bank
        (BinaryDescriptorStack.descriptor xs) f (fun _ => blank) 1 p 0)
      (fun w => w = BinaryDescriptorStackRoundtrip.bank
        (BinaryDescriptorStack.descriptor xs) f (BinaryDescriptorStack.descriptor xs) 1 p 1)
      ((8*(Nat.log2 roles+2)+15)*volume q v) := by
  apply (BinaryDescriptorStackRoundtrip.roundtrip_hoare xs f p hf).consequence
    (fun _ h => h) (fun _ h => h)
  have hlen := RecursiveDescriptorSize.descriptor_length_le_volume path hq hr hm hw hv xs hc hb
  have hl := path.original_chunks (by omega) hr hv
  have hp : 0 < volume q v := lt_of_lt_of_le (pow_pos (by omega : 0 < q) _) hl
  nlinarith

end IntegerMultBounds.Machine.RecursiveDescriptorStack
