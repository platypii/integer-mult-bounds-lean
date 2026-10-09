import IntegerMultBounds.Machine.CountedPackedReusable
import IntegerMultBounds.Compact.ToggleValue

/-! Exact word semantics of the fixed runtime-driven early packed gadget on
its guarded set. The temporary word is restored literally, and the target
word changes only at the selected low bits. The unguarded arithmetic machine
is unchanged; this theorem supplies the guarded contract used by repair. -/
namespace IntegerMultBounds.Machine.CountedPackedGuarded
noncomputable section
open Compact Compact.Radix Compact.PowerTwo
open PackedArith

/-- Padding is allowed: equal width and equal value determine a bit word. -/
theorem word_eq_of_length_value (xs ys : List Bool) (hl : xs.length = ys.length)
    (hv : Counter.value xs = Counter.value ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    exact (List.eq_nil_of_length_eq_zero (by simpa using hl.symm)).symm
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      have ht : xs.length = ys.length := by simpa using hl
      cases x <;> cases y <;> simp only [Counter.value, Bool.false_eq_true,
        ite_false, ite_true, zero_add] at hv
      · exact congrArg (List.cons false) (ih ys ht (by omega))
      · omega
      · omega
      · exact congrArg (List.cons true) (ih ys ht (by omega))

/-- The literal block words and control bits read by the packed program. -/
def states (q b : ℕ) (V W Z : List Bool) : List DigitState :=
  (List.range Z.length).map fun i =>
    ⟨Counter.value (Gather.field V (i*q) q),
      Counter.value (Gather.field W (i*b) b), ctrl (Z.getD i false)⟩

theorem states_target (q b : ℕ) (V W Z : List Bool) :
    (states q b V W Z).map DigitState.v = blockValues V q Z.length := by
  simp only [states, List.map_map, blockValues]
  rfl

theorem states_temp (q b : ℕ) (V W Z : List Bool) :
    (states q b V W Z).map DigitState.w = blockValues W b Z.length := by
  simp only [states, List.map_map, blockValues]
  rfl

theorem states_control (q b : ℕ) (V W Z : List Bool) :
    (states q b V W Z).map DigitState.z = Z.map ctrl := by
  simp only [states, List.map_map]
  conv_rhs => rw [list_eq_range Z, List.map_map]
  rfl

private theorem packed_word (q n : ℕ) (V : List Bool) (hV : V.length = n*q) :
    pack ((2 : ℤ)^q) (blockValues V q n) = (Counter.value V : ℤ) := by
  rw [← digits_blocks V q n hV]
  apply pack_digits _ (by positivity) _ _
  constructor
  · positivity
  · rw [pow_blocks, ← hV]
    exact_mod_cast Counter.value_lt V

private theorem radix_twice (q : ℕ) (hq : 1 ≤ q) :
    2*((2 : ℤ)^(q-1)) = (2 : ℤ)^q := by
  have hq' : q = (q-1)+1 := by omega
  conv_rhs => rw [hq', pow_succ]
  ring

/-- On good literal input blocks, all temporary bits are restored and exactly
one low bit per target block is conditionally toggled, with no hidden carry
or padding premise. -/
theorem guarded_words (q b : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q)
    (V W Z : List Bool) (hV : V.length = Z.length*q) (hW : W.length = Z.length*b)
    (hgood : ∀ d ∈ states q b V W Z,
      d.Good ((2 : ℤ)^b) ((2 : ℤ)^(q-1))) :
    v2 q b hb hbq V W Z = List.zipWith xor V (toggleMask q Z) ∧
      w2 q b hb hbq V W Z = W := by
  have hq : 1 ≤ q := by omega
  have ht := packedEarly_correct ((2 : ℤ)^b) ((2 : ℤ)^(q-1))
    (by
      have hp : (0 : ℤ) < 2^b := by positivity
      omega)
    (by positivity) (states q b V W Z) hgood
  rw [radix_twice q hq, states_control, states_target, states_temp,
    packed_word q Z.length V hV, packed_word b Z.length W hW] at ht
  have hv := forward_value q b hb hbq V W Z hV hW
  rw [ht] at hv
  have hvs : (states q b V W Z).map (fun d => toggle d.v d.z) =
      toggleList (blockValues V q Z.length) (Z.map ctrl) := by
    rw [← states_target q b V W Z, ← states_control q b V W Z]
    simp only [states, List.map_map, toggleList]
    rw [zip_maps]
    rfl
  rw [hvs] at hv
  have htoggle := toggle_word_value q hq V Z hV
  rw [digits_blocks V q Z.length hV] at htoggle
  obtain ⟨_,_,_,_,_,_,_,hvl,_,hwl⟩ := lengths q b hb hbq V W Z hV hW
  constructor
  · apply word_eq_of_length_value
    · rw [hvl, List.length_zipWith, hV, toggleMask_length q hq, min_self]
    · have he : (Counter.value (v2 q b hb hbq V W Z) : ℤ) =
          (Counter.value (List.zipWith xor V (toggleMask q Z)) : ℤ) :=
        (congrArg Prod.fst hv).trans htoggle.symm
      exact_mod_cast he
  · apply word_eq_of_length_value
    · exact hwl.trans hW.symm
    · have he : (Counter.value (w2 q b hb hbq V W Z) : ℤ) =
          (Counter.value W : ℤ) := congrArg Prod.snd hv
      exact_mod_cast he


/-- The actual fixed-control run has the exact guarded word semantics. The
remaining intermediate payload tapes are tracked by the literal output bank;
this contract does not silently erase them. -/
theorem guarded_hoare {a : ℕ} (q b : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q)
    (V W Z : List Bool) (f g z : ℤ → Fin (a+4))
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 : ℤ) (hs : Fin 3 → List Bool)
    (hV : V.length = Z.length*q) (hW : W.length = Z.length*b)
    (hf : f (p0-1) = blank) (hf' : f (p0+V.length) = blank)
    (hg : g (p1-1) = blank) (hg' : g (p1+W.length) = blank) (hz : z (p2-1) = blank)
    (hv : ∀ i, Counter.value (hs i) = CountedPackedShapeHeaders.originalValues q b Z.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hgood : ∀ d ∈ states q b V W Z,
      d.Good ((2 : ℤ)^b) ((2 : ℤ)^(q-1))) :
    HoareTime (CountedPackedArith.program a)
      (fun v => v = CountedPackedArith.bank
        (PackedArith.input V W Z f g z p0 p1 p2 p3 p4 p5 p6 p7 p8) hs)
      (fun v => v = CountedPackedArith.bank
        (PackedArith.output q b hb hbq V W Z f g z p0 p1 p2 p3 p4 p5 p6 p7 p8) hs ∧
        v2 q b hb hbq V W Z = List.zipWith xor V (toggleMask q Z) ∧
        w2 q b hb hbq V W Z = W)
      (2669*((Z.length+1)*(q+b+1))) := by
  refine (CountedPackedArith.forward_hoare q b hb hbq V W Z f g z
    p0 p1 p2 p3 p4 p5 p6 p7 p8 hs hV hW hf hf' hg hg' hz hv hc).consequence
    (fun _ h => h) ?_ (le_refl _)
  intro v h
  exact ⟨h, guarded_words q b hb hbq V W Z hV hW hgood⟩


/-- The reusable physical early gadget restores the original temporary word,
updates only selected low target bits, and returns every scratch tape blank.
All descriptor setup, copy-back and erasure costs are included. -/
theorem guarded_reusable_hoare {a : ℕ} (q b : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q)
    (V W Z : List Bool) (f g z : ℤ → Fin (a+4))
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 : ℤ) (hs : Fin 3 → List Bool)
    (hV : V.length = Z.length*q) (hW : W.length = Z.length*b)
    (hf : f (p0-1) = blank) (hf' : f (p0+V.length) = blank)
    (hg : g (p1-1) = blank) (hg' : g (p1+W.length) = blank) (hz : z (p2-1) = blank)
    (hv : ∀ i, Counter.value (hs i) = CountedPackedShapeHeaders.originalValues q b Z.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hgood : ∀ d ∈ states q b V W Z,
      d.Good ((2 : ℤ)^b) ((2 : ℤ)^(q-1))) :
    HoareTime (CountedPackedReusable.forwardProgram a)
      (fun v => v = CountedPackedArith.bank
        (PackedArith.input V W Z f g z p0 p1 p2 p3 p4 p5 p6 p7 p8) hs)
      (fun v => v = CountedPackedArith.bank
        (PackedArith.input (List.zipWith xor V (toggleMask q Z)) W Z
          f g z p0 p1 p2 p3 p4 p5 p6 p7 p8) hs)
      (2720*((Z.length+1)*(q+b+1))) := by
  have h := CountedPackedReusable.forward_hoare q b hb hbq V W Z f g z
    p0 p1 p2 p3 p4 p5 p6 p7 p8 hs hV hW hf hf' hg hg' hz hv hc
  obtain ⟨hvt,hwt⟩ := guarded_words q b hb hbq V W Z hV hW hgood
  simpa only [hvt,hwt] using h

end
end IntegerMultBounds.Machine.CountedPackedGuarded
