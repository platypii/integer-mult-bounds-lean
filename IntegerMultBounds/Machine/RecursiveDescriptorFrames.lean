import IntegerMultBounds.Machine.BinaryDescriptorFrames
import IntegerMultBounds.Machine.RecursiveDescriptorSize

/-! Fixed-many runtime descriptor stack operations charged to the recursive
child's logical volume. The constant depends only on the compiled field count
and role count, not recursion depth, tape positions, or ancestor storage size. -/
namespace IntegerMultBounds.Machine.RecursiveDescriptorFrames
open RecursiveInterchangeLayout RecursiveInterchangeVolume BinaryDescriptorFrames
variable {t a q roles m n k : ℕ} {root child : Descriptor}

private theorem child_positive (path : Path q roles m root n child)
    (hq : 2 ≤ q) (hr : 0 < roles) (hv : root.Positive) : 0 < volume q child := by
  have hl := path.original_chunks (by omega) hr hv
  exact lt_of_lt_of_le (pow_pos (by omega : 0 < q) _) hl

/-- Charge each scanned canonical field using its root-volume value bound. -/
theorem cost_le_linear (path : Path q roles m root n child) (hq : 2 ≤ q) (hr : 0 < roles)
    (hm : 2 ≤ m) (hw : root.width = m^k) (hv : root.Positive)
    (stack : Fin t) (ops : List (Slot stack)) (xs : Fin t → List Bool)
    (hc : ∀ i ∈ ops, GrowingCounterData.Canonical (xs i))
    (hb : ∀ i ∈ ops, Counter.value (xs i) ≤ volume q root) :
    cost ops xs ≤ (ops.length*(4*(Nat.log2 roles+2)+8))*volume q child := by
  have h := cost_le ops xs ((2*(Nat.log2 roles+2))*volume q child) (by
    intro i hi
    exact RecursiveDescriptorSize.descriptor_length_le_volume path hq hr hm hw hv (xs i) (hc i hi) (hb i hi))
  have hp := child_positive path hq hr hv
  have he : 2*(2*(Nat.log2 roles+2)*volume q child)+8 ≤
      (4*(Nat.log2 roles+2)+8)*volume q child := by nlinarith
  calc
    _ ≤ ops.length*(2*(2*(Nat.log2 roles+2)*volume q child)+8) := h
    _ ≤ ops.length*((4*(Nat.log2 roles+2)+8)*volume q child) := Nat.mul_le_mul_left _ he
    _ = _ := by ring

theorem roundtrip_cost_le_linear (path : Path q roles m root n child) (hq : 2 ≤ q) (hr : 0 < roles)
    (hm : 2 ≤ m) (hw : root.width = m^k) (hv : root.Positive)
    (stack : Fin t) (src dst : List (Slot stack)) (xs : Fin t → List Bool)
    (he : List.Forall₂ (fun i j : Slot stack => xs i = xs j) src dst)
    (hc : ∀ i ∈ src, GrowingCounterData.Canonical (xs i))
    (hb : ∀ i ∈ src, Counter.value (xs i) ≤ volume q root) :
    cost src xs+1+cost dst xs ≤
      (src.length*(8*(Nat.log2 roles+2)+16)+1)*volume q child := by
  rw [← cost_same_words src dst xs he]
  have h := cost_le_linear path hq hr hm hw hv stack src xs hc hb
  have hp := child_positive path hq hr hv
  nlinarith

/-- Actual fixed-list push, with its exact whole-bank postcondition. -/
theorem push_hoare_linear (path : Path q roles m root n child) (hq : 2 ≤ q) (hr : 0 < roles)
    (hm : 2 ≤ m) (hw : root.width = m^k) (hv : root.Positive)
    (stack : Fin t) (ops : List (Slot stack)) (xs : Fin t → List Bool) (v : Tapes t a)
    (hc : ∀ i ∈ ops, GrowingCounterData.Canonical (xs i))
    (hb : ∀ i ∈ ops, Counter.value (xs i) ≤ volume q root)
    (hs : ∀ i ∈ ops, v.head i = 1 ∧ v.tape i = BinaryDescriptorStack.descriptor (xs i)) :
    HoareTime (pushProgram stack ops) (fun w => w = v) (fun w => w = saved stack ops xs v)
      ((ops.length*(4*(Nat.log2 roles+2)+8))*volume q child) :=
  (BinaryDescriptorFrames.push_hoare stack ops xs v hs).consequence (fun _ h => h) (fun _ h => h)
    (cost_le_linear path hq hr hm hw hv stack ops xs hc hb)

/-- Actual reverse-order pop; all restored field words and older stack
contents remain literal in the postcondition. Destinations start blank. -/
theorem pop_hoare_linear (path : Path q roles m root n child) (hq : 2 ≤ q) (hr : 0 < roles)
    (hm : 2 ≤ m) (hw : root.width = m^k) (hv : root.Positive)
    (stack : Fin t) (ops : List (Slot stack)) (hu : ops.Nodup)
    (xs : Fin t → List Bool) (v : Tapes t a)
    (hc : ∀ i ∈ ops, GrowingCounterData.Canonical (xs i))
    (hb : ∀ i ∈ ops, Counter.value (xs i) ≤ volume q root)
    (hd : ∀ i ∈ ops, v.head i = 0 ∧ v.tape i = fun _ => blank)
    (hf : Free stack ops xs v) :
    HoareTime (popProgram stack ops) (fun w => w = saved stack ops xs v)
      (fun w => w = restored ops xs v)
      ((ops.length*(4*(Nat.log2 roles+2)+8))*volume q child) :=
  (BinaryDescriptorFrames.pop_hoare stack ops hu xs v hd hf).consequence (fun _ h => h) (fun _ h => h)
    (cost_le_linear path hq hr hm hw hv stack ops xs hc hb)

/-- One real same-bank push/pop program, including its joining transition. -/
theorem roundtrip_hoare_linear (path : Path q roles m root n child) (hq : 2 ≤ q) (hr : 0 < roles)
    (hm : 2 ≤ m) (hw : root.width = m^k) (hv : root.Positive)
    (stack : Fin t) (src dst : List (Slot stack)) (hu : dst.Nodup)
    (xs : Fin t → List Bool) (v : Tapes t a)
    (he : List.Forall₂ (fun i j : Slot stack => xs i = xs j) src dst)
    (hc : ∀ i ∈ src, GrowingCounterData.Canonical (xs i))
    (hb : ∀ i ∈ src, Counter.value (xs i) ≤ volume q root)
    (hs : ∀ i ∈ src, v.head i = 1 ∧ v.tape i = BinaryDescriptorStack.descriptor (xs i))
    (hd : ∀ i ∈ dst, v.head i = 0 ∧ v.tape i = fun _ => blank)
    (hf : Free stack dst xs v) :
    HoareTime (roundtripProgram stack src dst) (fun w => w = v) (fun w => w = restored dst xs v)
      ((src.length*(8*(Nat.log2 roles+2)+16)+1)*volume q child) :=
  (BinaryDescriptorFrames.roundtrip_hoare stack src dst hu xs v he hs hd hf).consequence
    (fun _ h => h) (fun _ h => h) (roundtrip_cost_le_linear path hq hr hm hw hv stack src dst xs he hc hb)

/-- Six seven-factor runtime headers have a fixed child-volume charge. -/
theorem six_field_roundtrip_cost (path : Path q roles m root n child) (hq : 2 ≤ q) (hr : 0 < roles)
    (hm : 2 ≤ m) (hw : root.width = m^k) (hv : root.Positive)
    (stack : Fin t) (src dst : List (Slot stack)) (hlen : src.length = 6) (xs : Fin t → List Bool)
    (he : List.Forall₂ (fun i j : Slot stack => xs i = xs j) src dst)
    (hc : ∀ i ∈ src, GrowingCounterData.Canonical (xs i))
    (hb : ∀ i ∈ src, Counter.value (xs i) ≤ volume q root) :
    cost src xs+1+cost dst xs ≤ (48*(Nat.log2 roles+2)+97)*volume q child := by
  have h := roundtrip_cost_le_linear path hq hr hm hw hv stack src dst xs he hc hb
  rw [hlen] at h
  convert h using 1; ring

end IntegerMultBounds.Machine.RecursiveDescriptorFrames
