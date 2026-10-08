import IntegerMultBounds.Machine.RationalPrefixTranslationBootstrap
import IntegerMultBounds.Machine.FlatControlledShiftNormalize

/-! A complete controlled shift from blank workspace back to common payload
origins. Width and dimension descriptors are supplied. All marker installation,
prefix generation, arithmetic, shifting, copying, erasure and rewinds are paid.
The initializer's descriptors/clocks and final operation metadata are retained. -/
namespace IntegerMultBounds.Machine.FlatControlledShiftReady
open PrefixCounterInitPlacement
open RationalPrefixTranslationInit (streamPlacement)
variable {radix c B : ℕ} [Fact radix.Prime]

def initializedProgram (r : ℚ) (order : List (Fin (c+1))) (hne : order ≠ []) :=
  PrefixCounterInitPlacement.program (Fact.out : radix.Prime).two_le
    (FlatControlledShiftNormalize.program (radix := radix) r order hne) (streamPlacement c)

def program (r : ℚ) (order : List (Fin (c+1))) (hne : order ≠ []) :=
  seq (RationalPrefixTranslationBootstrap.setup (radix := radix) (PrefixCounterInit.tapeCount (c+1)))
    (initializedProgram (radix := radix) r order hne)

def output (r : ℚ) (low high : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (ws : Fin (c+1) → List Bool)
    (a : Fin (radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B)) → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) :=
  Placement.replace (handoff (streamPlacement c))
    ((PrefixCounterInit.output (Fact.out : radix.Prime).two_le (c+1) ws width).append
      (Placement.extra (streamPlacement c) (FlatControlledShift.bank r (low++0::high) width a source dest p q bs qs ns 0)))
    (FlatControlledShiftNormalize.output r low high width a source dest p q bs qs ns)

/-- Exact active output; every complementary initialization tape is retained. -/
theorem output_active (r : ℚ) (low high : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (ws : Fin (c+1) → List Bool)
    (a : Fin (radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B)) → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) :
    Placement.active (handoff (streamPlacement c)) (output r low high width ws a source dest p q bs qs ns) =
      FlatControlledShiftNormalize.output r low high width a source dest p q bs qs ns :=
  Placement.active_replace _ _ _

/-- The shifted symbols reside on the original input tape, ready for another
operation at another target coordinate. No tape copy or reset is implicit. -/
theorem output_symbol (r : ℚ) (low high : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (ws : Fin (c+1) → List Bool)
    (a : Fin (radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B)) → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool)
    (i : Fin (radix^PrefixAddressData.widthSum (low++0::high) width))
    (y : Fin (radix^(width 0))) (j : Fin B) :
    (output r low high width ws a source dest p q bs qs ns).tape
      (handoff (streamPlacement c) (Fin.castAdd (extras (c+1)) (10 : Fin ((16+c)+2))))
      (p+((i.val*(radix^(width 0)*B)+
        ((y.val+FlatControlledShift.physicalOffset (radix := radix) r low width i.val)%radix^(width 0))*B+j.val : ℕ) : ℤ)) =
      (RadixToBinary.binaryEncoding (q := radix)).encode (a (FiberLayoutData.index i y j)) := by
  change (Placement.active (handoff (streamPlacement c))
    (output r low high width ws a source dest p q bs qs ns)).tape 10 _ = _
  rw [output_active]
  exact FlatControlledShiftNormalize.output_symbol r low high width a source dest p q bs qs ns i y j

/-- Complete blank-workspace execution with common-input restoration and
linear volume bound, including the fixed number of initialization tapes. -/
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
    (cn : GrowingCounterData.Canonical ns)
    (hblank : ∀ z, q ≤ z → z < q+(FlatControlledShiftNormalize.word r low high width a).length → dest z = blank) :
    HoareTime (program r (low++0::high) (by simp))
      (fun v => v = RationalPrefixTranslationBootstrap.input r (low++0::high) width ws a source dest p q bs qs ns)
      (fun v => v = output r low high width ws a source dest p q bs qs ns)
      ((878+4*c)*(radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B))+29*(c+1)+29) := by
  have hs := FlatControlledShiftNormalize.realizes_hoare r hden low high hfull width hB
    a source dest p q bs qs ns hb hq hn cb cq cn hblank
  have hi := initialize_then (Fact.out : radix.Prime).two_le (streamPlacement c) ws width hw cw _ _
    (RationalPrefixTranslationInit.active_initial r (low++0::high) width a source dest p q bs qs ns) hs
  have hm := RationalPrefixTranslationBootstrap.bootstrap_hoare r (low++0::high) width ws a source dest p q bs qs ns
  apply (hm.seq hi).consequence (fun _ h => h) (fun _ h => h) _
  have hp : (∑ i, width i) ≤ radix^PrefixAddressData.widthSum (low++0::high) width := by
    rw [PrefixAddressData.full_widthSum _ _ hfull]
    exact RadixToBinaryData.width_le_power (Fact.out : radix.Prime).two_le _
  have hvol : radix^PrefixAddressData.widthSum (low++0::high) width ≤
      radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B) :=
    Nat.le_mul_of_pos_right _ (Nat.mul_pos (pow_pos (Fact.out : radix.Prime).pos _) hB)
  nlinarith

end IntegerMultBounds.Machine.FlatControlledShiftReady
