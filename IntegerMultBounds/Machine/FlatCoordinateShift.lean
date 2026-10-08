import IntegerMultBounds.Machine.FlatCoordinateLayout
import IntegerMultBounds.Machine.FlatControlledShiftArray

/-! A concrete fastest-first prefix counter for a selected earlier coordinate,
instantiated with the initialized physical shift and canonical common-array output. -/
namespace IntegerMultBounds.Machine.FlatCoordinateShift
open Networks
open FlatCoordinateLayout
noncomputable section
variable {d radix b W : ℕ} [Fact radix.Prime]
local instance : NeZero (radix^b) := ⟨Nat.ne_of_gt (pow_pos (Fact.out : radix.Prime).pos b)⟩

/-- Field zero names the selected control. All other field names are spectators;
the low fields are less significant than the control in the physical prefix. -/
def low (t k : Fin d) : List (Fin ((t.val-1)+1)) :=
  ((List.finRange (t.val-1)).map Fin.succ).take (t.val-1-k.val)

def high (t k : Fin d) : List (Fin ((t.val-1)+1)) :=
  ((List.finRange (t.val-1)).map Fin.succ).drop (t.val-1-k.val)

theorem order_full (t k : Fin d) : (low t k++0::high t k).Perm (List.finRange ((t.val-1)+1)) := by
  rw [List.finRange_succ]
  have h := List.perm_middle (a := (0 : Fin ((t.val-1)+1)))
    (l₁ := low t k) (l₂ := high t k)
  simpa only [low,high,List.take_append_drop] using h

theorem low_width (t k : Fin d) :
    PrefixAddressData.widthSum (low t k) (fun _ => b) = b*(t.val-1-k.val) := by
  unfold PrefixAddressData.widthSum
  rw [List.map_const',List.sum_replicate]
  simp only [low,List.length_take,List.length_map,List.length_finRange,smul_eq_mul]
  rw [Nat.min_eq_left (Nat.sub_le _ _),Nat.mul_comm]

theorem full_width (t k : Fin d) (hk : k < t) :
    PrefixAddressData.widthSum (low t k++0::high t k) (fun _ => b) = b*t.val := by
  rw [PrefixAddressData.full_widthSum _ _ (order_full t k)]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  have hpos : 0 < t.val := lt_of_le_of_lt (Nat.zero_le k.val) hk
  rw [Nat.sub_add_cancel hpos]
  exact Nat.mul_comm _ _

omit [Fact radix.Prime] in
/-- The counter schedule and target fiber have exactly the common physical volume. -/
theorem volume (t k : Fin d) (hk : k < t) :
    (radix^b)^d*W =
      radix^PrefixAddressData.widthSum (low t k++0::high t k) (fun _ => b)*
        (radix^b*suffixSize (Q := radix^b) (W := W) t) := by
  rw [full_width t k hk,pow_mul]
  exact split_volume t

def view (a : Fin ((radix^b)^d*W) → Fin 4) (t k : Fin d) (hk : k < t) :
    Fin (radix^PrefixAddressData.widthSum (low t k++0::high t k) (fun _ => b)*
      (radix^b*suffixSize (Q := radix^b) (W := W) t)) → Fin 4 :=
  fun i => a (Fin.cast (volume t k hk).symm i)

omit [Fact radix.Prime] in
theorem view_word (a : Fin ((radix^b)^d*W) → Fin 4) (t k : Fin d) (hk : k < t) :
    List.ofFn (view a t k hk) = List.ofFn a := (List.ofFn_congr (volume t k hk) a).symm

/-- The actual counter-selected physical slice equals the original earlier
coordinate. The reversal is paid for in the explicit fastest-first field order. -/
theorem physicalOffset_eq (r : ℚ) (x : Fin d → ZMod (radix^b)) (t k : Fin d) (hk : k < t) :
    FlatControlledShift.physicalOffset (radix := radix) r (low t k) (fun _ => b) (prefixIndex x t) =
      (Swap.Modular.ratMod (radix^b) r*x k).val := by
  unfold FlatControlledShift.physicalOffset FlatControlledShift.control
  rw [low_width,earlier_control_radix x t k hk,ZMod.natCast_zmod_val]

def array (r : ℚ) (a : Fin ((radix^b)^d*W) → Fin 4) (t k : Fin d) (hk : k < t) :
    Fin ((radix^b)^d*W) → Fin 4 :=
  fun i => FlatControlledShiftArray.array r (low t k) (high t k) (fun _ => b)
    (view a t k hk) (Fin.cast (volume t k hk) i)

omit [Fact radix.Prime] in
theorem array_word (r : ℚ) (a : Fin ((radix^b)^d*W) → Fin 4) (t k : Fin d) (hk : k < t) :
    List.ofFn (array r a t k hk) =
      List.ofFn (FlatControlledShiftArray.array r (low t k) (high t k) (fun _ => b) (view a t k hk)) :=
  (List.ofFn_congr (volume t k hk).symm _).symm

/-- Concrete initialized shift output has exactly the common-coordinate
ordered-affine semantics, with the actual physical offset equation discharged. -/
theorem array_entry (r : ℚ) (a : Fin ((radix^b)^d*W) → Fin 4) (t k : Fin d) (hk : k < t)
    (x : Fin d → ZMod (radix^b)) (j : Fin W) :
    array r a t k hk (index (OrderedAffine.execute (.shift t k (Swap.Modular.ratMod (radix^b) r)) x) j) =
      a (index x j) := by
  have hp : prefixIndex x t < radix^PrefixAddressData.widthSum (low t k++0::high t k) (fun _ => b) := by
    simpa only [full_width t k hk,pow_mul,prefixSize] using prefix_lt x t
  have hh := FlatControlledShiftArray.array_entry r (low t k) (high t k) (fun _ => b)
    (view a t k hk) ⟨prefixIndex x t,hp⟩ ⟨(x t).val,ZMod.val_lt _⟩
    ⟨suffix x t j,suffix_lt x t j⟩
  have hin : view a t k hk (FiberLayoutData.index ⟨prefixIndex x t,hp⟩
      ⟨(x t).val,ZMod.val_lt _⟩ ⟨suffix x t j,suffix_lt x t j⟩) = a (index x j) := by
    unfold view
    congr 1
    apply Fin.ext
    simpa only [Fin.val_cast,FiberLayoutData.index_val] using (index_split x t j).symm
  rw [hin] at hh
  unfold array
  convert hh using 1
  congr 1
  apply Fin.ext
  simp only [Fin.val_cast,shift_destination,FiberLayoutData.index_val,physicalOffset_eq r x t k hk]


/-- Source slot in the actual initialized prefix-counter bank. -/
def sourceSlot (t : Fin d) :=
  PrefixCounterInitPlacement.handoff (RationalPrefixTranslationInit.streamPlacement (t.val-1))
    (Fin.castAdd (PrefixCounterInitPlacement.extras ((t.val-1)+1)) (10 : Fin ((16+(t.val-1))+2)))

theorem output_source (r : ℚ) (a : Fin ((radix^b)^d*W) → Fin 4) (t k : Fin d) (hk : k < t)
    (ws : Fin ((t.val-1)+1) → List Bool) (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) :
    (FlatControlledShiftReady.output r (low t k) (high t k) (fun _ => b) ws
      (view a t k hk) source dest p q bs qs ns).tape (sourceSlot t) =
      fun z => (RadixToBinary.binaryEncoding (q := radix)).encode
        (putWord source p (List.ofFn (array r a t k hk)) z) := by
  rw [sourceSlot,FlatControlledShiftArray.output_source,array_word]

/-- All initialization, shift, copying and head restoration run on the actual
finite-tape machine; the resulting source carries the common-coordinate array. -/
theorem realizes_hoare (r : ℚ) (hden : r.den < radix)
    (a : Fin ((radix^b)^d*W) → Fin 4) (t k : Fin d) (hk : k < t) (hW : 0 < W)
    (ws : Fin ((t.val-1)+1) → List Bool)
    (hw : ∀ i, Counter.value (ws i) = b) (cw : ∀ i, GrowingCounterData.Canonical (ws i))
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool)
    (hb : Counter.value bs = suffixSize (Q := radix^b) (W := W) t)
    (hq : Counter.value qs = radix^b) (hn : Counter.value ns = (radix^b)^t.val)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns)
    (hblank : ∀ z, q ≤ z → z < q+(((radix^b)^d*W : ℕ) : ℤ) → dest z = blank) :
    HoareTime (FlatControlledShiftReady.program (radix := radix) r (low t k++0::high t k) (by simp))
      (fun v => v = RationalPrefixTranslationBootstrap.input r (low t k++0::high t k) (fun _ => b)
        ws (view a t k hk) source dest p q bs qs ns)
      (fun v => v = FlatControlledShiftReady.output r (low t k) (high t k) (fun _ => b)
          ws (view a t k hk) source dest p q bs qs ns ∧
        v.tape (sourceSlot t) = (fun z => (RadixToBinary.binaryEncoding (q := radix)).encode
          (putWord source p (List.ofFn (array r a t k hk)) z)) ∧
        ∀ (x : Fin d → ZMod (radix^b)) (j : Fin W),
          array r a t k hk (index (OrderedAffine.execute (.shift t k (Swap.Modular.ratMod (radix^b) r)) x) j) =
            a (index x j))
      ((878+4*(t.val-1))*((radix^b)^d*W)+29*t.val+29) := by
  have hv := volume (radix := radix) (b := b) (W := W) t k hk
  have hs := FlatControlledShiftReady.realizes_hoare (B := suffixSize (Q := radix^b) (W := W) t) r hden (low t k) (high t k) (order_full t k)
    (fun _ => b) ws hw cw
    (Nat.mul_pos (pow_pos (pow_pos (Fact.out : radix.Prime).pos b) _) hW)
    (view a t k hk) source dest p q bs qs ns hb hq
    (by simpa only [full_width t k hk,pow_mul] using hn) cb cq cn
    (by
      intro z hz hz'
      apply hblank z hz
      rw [FlatControlledShiftNormalize.word_length] at hz'
      simpa only [← hv] using hz')
  apply hs.consequence (fun _ h => h) ?_ ?_
  · intro v hv
    subst v
    exact ⟨rfl,output_source r a t k hk ws source dest p q bs qs ns,array_entry r a t k hk⟩
  · rw [← hv]
    have hpos : 0 < t.val := lt_of_le_of_lt (Nat.zero_le k.val) hk
    rw [Nat.sub_add_cancel hpos]

end
end IntegerMultBounds.Machine.FlatCoordinateShift
