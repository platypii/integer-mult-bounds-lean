import IntegerMultBounds.Machine.PrefixCounterInitPlacement
import IntegerMultBounds.Machine.FlatControlledShift

/-! Physical blank-prefix initialization followed by a complete controlled
shift. Width descriptors are supplied; their mutable clocks and generated radix
fields start blank. Translation metadata retains the existing marked-workspace
contract. A static whole-bank permutation shares generated fields with the
stream, preserving every initializer descriptor/clock as an exact frame. -/
namespace IntegerMultBounds.Machine.RationalPrefixTranslationInit
open PrefixCounterInitPlacement
variable {radix c B : ℕ} [Fact radix.Prime]

/-- Select the actual prefix suffix of the stream body, leaving fifteen body
metadata tapes and two outer clock tapes as the seventeen-tape complement. -/
def streamPlacement (c : ℕ) : Fin ((c+1)+17) ≃ Fin ((16+c)+2) :=
  (finCongr (show (c+1)+17 = ((c+1)+15)+2 by omega)).trans
    (appendEquiv (RationalPrefixTranslationExecution.prefixPlacement c) 2)

private theorem stream_field (i : Fin (c+1)) :
    streamPlacement c (Fin.castAdd 17 i) =
      Fin.castAdd 2 (RationalPrefixTranslationExecution.prefixPlacement c (Fin.castAdd 15 i)) := by
  change appendEquiv (RationalPrefixTranslationExecution.prefixPlacement c) 2 _ = _
  have he : (Fin.castAdd 17 i : Fin (((c+1)+15)+2)) =
      Fin.castAdd 2 (Fin.castAdd 15 i) := Fin.ext rfl
  rw [he,appendEquiv_left]

omit [Fact radix.Prime] in
private theorem active_stream_append (v : Tapes (16+c) radix) (frame : Tapes 2 radix) :
    Placement.active (streamPlacement c) (v.append frame) =
      Placement.active (RationalPrefixTranslationExecution.prefixPlacement c) v := by
  unfold Placement.active
  apply congrArg₂ Tapes.mk <;> funext i <;> rw [stream_field] <;> simp [Tapes.append]

omit [Fact radix.Prime] in
private theorem body_active (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs supplied old : List Bool)
    (ds : Fin (c+1) → List (Fin radix)) :
    Placement.active (RationalPrefixTranslationExecution.prefixPlacement c)
      (RationalPrefixTranslationExecution.bank source dest p q bs qs supplied old ds) =
      PrefixCounter.tapes (fun _ => MarkedWordCleanup.empty) ds := by
  have hz : RationalPrefixTranslationExecution.prefixPlacement c (Fin.castAdd 15 (0 : Fin (c+1))) =
      Fin.castAdd c (15 : Fin 16) := by
    apply Fin.ext
    simp [RationalPrefixTranslationExecution.prefixPlacement,finAddFlip_apply_castAdd]
  have hs (i : Fin c) : RationalPrefixTranslationExecution.prefixPlacement c (Fin.castAdd 15 i.succ) =
      Fin.natAdd 16 i := by
    apply Fin.ext
    simp [RationalPrefixTranslationExecution.prefixPlacement,finAddFlip_apply_castAdd]
    omega
  unfold Placement.active
  apply congrArg₂ Tapes.mk
  · funext i
    induction i using Fin.cases with
    | zero => rw [hz]; rfl
    | succ i =>
      rw [hs]
      simp only [RationalPrefixTranslationExecution.bank,Tapes.append,Fin.addCases_right,RationalPrefixTranslationExecution.extra]
  · funext i
    induction i using Fin.cases with
    | zero => rw [hz]; rfl
    | succ i =>
      rw [hs]
      simp only [RationalPrefixTranslationExecution.bank,Tapes.append,Fin.addCases_right,RationalPrefixTranslationExecution.extra]
      rfl

/-- The machine consumes exactly the radix fields produced by the initializer. -/
theorem active_initial {P : ℕ} (r : ℚ) (order : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (a : Fin (P*(radix^(width 0)*B)) → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs ns : List Bool) :
    Placement.active (streamPlacement c) (FlatControlledShift.bank r order width a source dest p q bs qs ns 0) =
      PrefixCounter.tapes (fun _ => RadixZeroFill.radixEmpty)
        (fun i => RadixCounterData.zeros (Fact.out : radix.Prime).two_le (width i)) := by
  unfold FlatControlledShift.bank CountedLoopReuseAlphabet.bank
  rw [active_stream_append]
  unfold RationalPrefixTranslationStream.state
  rw [body_active]
  rfl

/-- Shared-tape program; no field copy or uncharged data conversion occurs. -/
def program (r : ℚ) (order : List (Fin (c+1))) (hne : order ≠ []) :=
  PrefixCounterInitPlacement.program (Fact.out : radix.Prime).two_le
    (RationalPrefixTranslationStream.program (radix := radix) r order hne) (streamPlacement c)

/-- Raw generated prefix tapes and supplied canonical dimension descriptors.
The complementary translation metadata uses its explicit marked-bank format. -/
def input {P : ℕ} (r : ℚ) (order : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (ws : Fin (c+1) → List Bool) (a : Fin (P*(radix^(width 0)*B)) → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) :=
  (PrefixCounterInit.input (q := radix) (c+1) ws).append
    (Placement.extra (streamPlacement c) (FlatControlledShift.bank r order width a source dest p q bs qs ns 0))

def output {P : ℕ} (r : ℚ) (order : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (ws : Fin (c+1) → List Bool) (a : Fin (P*(radix^(width 0)*B)) → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) :=
  Placement.replace (handoff (streamPlacement c))
    ((PrefixCounterInit.output (Fact.out : radix.Prime).two_le (c+1) ws width).append
      (Placement.extra (streamPlacement c) (FlatControlledShift.bank r order width a source dest p q bs qs ns 0)))
    (FlatControlledShift.bank r order width a source dest p q bs qs ns P)

/-- The final active bank is exactly the complete executed stream bank. -/
theorem output_active {P : ℕ} (r : ℚ) (order : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (ws : Fin (c+1) → List Bool) (a : Fin (P*(radix^(width 0)*B)) → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) :
    Placement.active (handoff (streamPlacement c)) (output r order width ws a source dest p q bs qs ns) =
      FlatControlledShift.bank r order width a source dest p q bs qs ns P :=
  Placement.active_replace _ _ _

/-- Every payload symbol lands on the actual wired destination tape. -/
theorem output_symbol (r : ℚ) (hden : r.den < radix)
    (low high : List (Fin (c+1))) (hnodup : (low++0::high).Nodup)
    (width : Fin (c+1) → ℕ) (ws : Fin (c+1) → List Bool)
    (a : Fin (radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B)) → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool)
    (i : Fin (radix^PrefixAddressData.widthSum (low++0::high) width))
    (y : Fin (radix^(width 0))) (j : Fin B) :
    (output r (low++0::high) width ws a source dest p q bs qs ns).tape
      (handoff (streamPlacement c) (Fin.castAdd (extras (c+1)) (11 : Fin ((16+c)+2))))
      (q+((i.val*(radix^(width 0)*B)+
        ((y.val+FlatControlledShift.physicalOffset (radix := radix) r low width i.val)%radix^(width 0))*B+j.val : ℕ) : ℤ)) =
      (RadixToBinary.binaryEncoding (q := radix)).encode (a (FiberLayoutData.index i y j)) := by
  change (Placement.active (handoff (streamPlacement c))
    (output r (low++0::high) width ws a source dest p q bs qs ns)).tape 11 _ = _
  rw [output_active]
  exact FlatControlledShift.output_symbol r hden low high hnodup width a source dest p q bs qs ns i y j

/-- Complete physical initialization and controlled shift, including all widths,
while inherited translation sentinels remain explicit in the input bank. -/
theorem realizes_hoare (r : ℚ) (hden : r.den < radix)
    (low high : List (Fin (c+1))) (hfull : (low++0::high).Perm (List.finRange (c+1)))
    (width : Fin (c+1) → ℕ) (ws : Fin (c+1) → List Bool)
    (hw : ∀ i, Counter.value (ws i) = width i) (cw : ∀ i, GrowingCounterData.Canonical (ws i))
    (hB : 0 < B)
    (a : Fin (radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B)) → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^(width 0))
    (hn : Counter.value ns = radix^PrefixAddressData.widthSum (low++0::high) width)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns) :
    HoareTime (program r (low++0::high) (by simp))
      (fun v => v = input r (low++0::high) width ws a source dest p q bs qs ns)
      (fun v => v = output r (low++0::high) width ws a source dest p q bs qs ns)
      (15*(∑ i, width i)+29*(c+1)+
        (536+4*c)*(radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B))+24) := by
  have hh := FlatControlledShift.realizes_hoare r hden low high hfull width hB a source dest p q bs qs ns hb hq hn cb cq cn
  have hh' := hh.consequence (fun _ h => h) (fun _ h => h.1) le_rfl
  have h := initialize_then (Fact.out : radix.Prime).two_le (streamPlacement c) ws width hw cw _ _
    (active_initial r (low++0::high) width a source dest p q bs qs ns) hh'
  exact h.consequence (fun _ h => h) (fun _ h => h) (by omega)

/-- Initialization widths are absorbed by the complete prefix traversal volume. -/
theorem realizes_hoare_linear (r : ℚ) (hden : r.den < radix)
    (low high : List (Fin (c+1))) (hfull : (low++0::high).Perm (List.finRange (c+1)))
    (width : Fin (c+1) → ℕ) (ws : Fin (c+1) → List Bool)
    (hw : ∀ i, Counter.value (ws i) = width i) (cw : ∀ i, GrowingCounterData.Canonical (ws i))
    (hB : 0 < B)
    (a : Fin (radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B)) → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^(width 0))
    (hn : Counter.value ns = radix^PrefixAddressData.widthSum (low++0::high) width)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns) :
    HoareTime (program r (low++0::high) (by simp))
      (fun v => v = input r (low++0::high) width ws a source dest p q bs qs ns)
      (fun v => v = output r (low++0::high) width ws a source dest p q bs qs ns)
      ((551+4*c)*(radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B))+29*(c+1)+24) := by
  apply (realizes_hoare r hden low high hfull width ws hw cw hB a source dest p q bs qs ns hb hq hn cb cq cn).consequence
    (fun _ h => h) (fun _ h => h) _
  have hp : (∑ i, width i) ≤ radix^PrefixAddressData.widthSum (low++0::high) width := by
    rw [PrefixAddressData.full_widthSum _ _ hfull]
    exact RadixToBinaryData.width_le_power (Fact.out : radix.Prime).two_le _
  have hvol : radix^PrefixAddressData.widthSum (low++0::high) width ≤
      radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B) :=
    Nat.le_mul_of_pos_right _ (Nat.mul_pos (pow_pos (Fact.out : radix.Prime).pos _) hB)
  nlinarith

end IntegerMultBounds.Machine.RationalPrefixTranslationInit
