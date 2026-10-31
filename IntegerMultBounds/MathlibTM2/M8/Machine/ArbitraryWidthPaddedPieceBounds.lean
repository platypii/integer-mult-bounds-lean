module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPaddedPiecePadding
public import IntegerMultBounds.Machine.RunInvariant

/-! The actual padding and cropping components have linear-volume head
intervals at every reachable configuration. RunInvariant.post supplies their
exact padded/cropped banks at the controller's halting boundaries. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPaddedPiecePadding
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
  Networks.Shared50ModularControl RecursiveInterchangeLayout RecursiveRowPadding

theorem pad_heads (v : Descriptor) (R' : ℕ) (hs : Fin 4 → List Bool)
    (hp : v.Positive) (hR : v.rows ≤ R') (hv : Headers v R' hs)
    (x : Fin (volume prime v) → ZMod 2) {c : Config 12 215 prime}
    (hc : RunInvariant (RowPaddingConstructedAlphabet.program (a := prime)) (· = input x hs) c) :
    ∀ i, (input x hs).head i-413*volume prime (withRows v R') ≤ c.head i ∧
      c.head i ≤ (input x hs).head i+413*volume prime (withRows v R') := by
  exact hc.heads_eq (pad_hoare v R' hs hp hR hv x)

theorem crop_heads (v : Descriptor) (R' : ℕ) (hs : Fin 4 → List Bool)
    (hp : v.Positive) (hR : v.rows ≤ R') (hv : Headers v R' hs)
    (x : Fin (volume prime (withRows v R')) → ZMod 2) {c : Config 12 215 prime}
    (hc : RunInvariant cropProgram (· = middle x hs) c) :
    ∀ i, (middle x hs).head i-413*volume prime (withRows v R') ≤ c.head i ∧
      c.head i ≤ (middle x hs).head i+413*volume prime (withRows v R') := by
  exact hc.heads_eq (crop_hoare v R' hs hp hR hv x)

end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPaddedPiecePadding
