import IntegerMultBounds.Machine.CompactActiveTargetLayout
import IntegerMultBounds.Machine.FiberLayoutData
import IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedData

/-! Target-fiber and compact front/back-swap views of one unchanged array.
The target occupies its literal active subinterval; all translations of a
compact field after exchange have the entire active block in their prefix. -/
namespace IntegerMultBounds.Machine.CompactActiveTargetGeometry
open CompactGadgetReservationShape
open CompactActiveTargetLayout
open RecursiveInterchangeRows (pack pack_val)

def targetPrefix (s : Shape) (w before rows : ℕ) :=
  (((((rows*2^w)*2^(s.H-w))*2^w)*2^(s.H-w))*2^s.F)*2^before

def targetSuffix (s : Shape) (after : ℕ) := (2^after*2^(s.H+s.B))*s.payload

def targetPrefixIndex (s : Shape) (w m before after rows : ℕ)
    (x : Address s w m before after rows) : Fin (targetPrefix s w before rows) :=
  pack (pack (pack (pack (pack (pack x.row x.u) x.uTail) x.t) x.tTail) x.frontSlack) x.activeBefore

def targetSuffixIndex (s : Shape) (w m before after rows : ℕ)
    (x : Address s w m before after rows) : Fin (targetSuffix s after) :=
  pack (pack x.activeAfter x.back) x.payload

def targetIndex (s : Shape) (w m before after rows : ℕ) (x : Address s w m before after rows) :=
  FiberLayoutData.index (targetPrefixIndex s w m before after rows x) x.target
    (targetSuffixIndex s w m before after rows x)

theorem target_volume (s : Shape) (w m before after rows : ℕ) (hw : w≤s.H)
    (hactive : before+m+after=s.active*s.chunk) :
    targetPrefix s w before rows*(2^m*targetSuffix s after)=rows*s.recordWidth := by
  rw [←size_eq s w m before after rows hw hactive]
  unfold targetPrefix targetSuffix size
  ring

/-- The direct target fiber is already contiguous on the original tape. -/
theorem target_index (s : Shape) (w m before after rows : ℕ) (hw : w≤s.H)
    (hactive : before+m+after=s.active*s.chunk) (x : Address s w m before after rows) :
    Fin.cast (target_volume s w m before after rows hw hactive)
      (targetIndex s w m before after rows x)=index s w m before after rows hw hactive x := by
  apply Fin.ext
  change (targetIndex s w m before after rows x).val=(index s w m before after rows hw hactive x).val
  rw [index_val]
  unfold targetIndex
  rw [FiberLayoutData.index_val]
  simp only [targetPrefixIndex,targetSuffixIndex,pack_val]
  unfold targetSuffix
  ring

theorem target_prefix_bits (s : Shape) (w before rows : ℕ) (hw : w≤s.H) :
    targetPrefix s w before rows=rows*2^(2*s.H+s.F+before) := by
  have he : w+(s.H-w)+w+(s.H-w)+s.F+before=2*s.H+s.F+before := by omega
  unfold targetPrefix
  calc
    _ = rows*2^(w+(s.H-w)+w+(s.H-w)+s.F+before) := by simp only [pow_add]; ring
    _ = _ := by rw [he]

def uCopies (s : Shape) (w before : ℕ) :=
  (((2^(s.H-w)*2^w)*2^(s.H-w))*2^s.F)*2^before

def tCopies (s : Shape) (w before : ℕ) := (2^(s.H-w)*2^s.F)*2^before

theorem u_prefix_repetitions (s : Shape) (w before rows : ℕ) :
    targetPrefix s w before rows=(rows*2^w)*uCopies s w before := by
  unfold targetPrefix uCopies; ring

theorem t_prefix_repetitions (s : Shape) (w before rows : ℕ) :
    targetPrefix s w before rows=(((rows*2^w)*2^(s.H-w))*2^w)*tCopies s w before := by
  unfold targetPrefix tCopies; ring

/-- Neither front field is in the target or suffix: its whole range lies in
this literal target prefix, with the shown repetition after its own address. -/
theorem target_prefix_value (s : Shape) (w m before after rows : ℕ)
    (x : Address s w m before after rows) :
    (targetPrefixIndex s w m before after rows x).val=
      ((((((x.row.val*2^w+x.u.val)*2^(s.H-w)+x.uTail.val)*2^w+x.t.val)*
        2^(s.H-w)+x.tTail.val)*2^s.F+x.frontSlack.val)*2^before+x.activeBefore.val) := by
  simp only [targetPrefixIndex,pack_val]

def uRestIndex (s : Shape) (w m before after rows : ℕ)
    (x : Address s w m before after rows) : Fin (uCopies s w before) :=
  pack (pack (pack (pack x.uTail x.t) x.tTail) x.frontSlack) x.activeBefore

def tRestIndex (s : Shape) (w m before after rows : ℕ)
    (x : Address s w m before after rows) : Fin (tCopies s w before) :=
  pack (pack x.tTail x.frontSlack) x.activeBefore

/-- The U word's address repeats through precisely the remaining front and
active-prefix ranges; the repetition includes the independently dirty T. -/
theorem u_prefix_index (s : Shape) (w m before after rows : ℕ)
    (x : Address s w m before after rows) :
    Fin.cast (u_prefix_repetitions s w before rows)
      (targetPrefixIndex s w m before after rows x)=
        pack (pack x.row x.u) (uRestIndex s w m before after rows x) := by
  apply Fin.ext
  change (targetPrefixIndex s w m before after rows x).val=
    (pack (pack x.row x.u) (uRestIndex s w m before after rows x)).val
  rw [target_prefix_value]
  unfold uCopies
  simp only [uRestIndex,pack_val]
  ring

/-- The current T word repeats only through its own tail, front slack and
active prefix. Earlier U coordinates remain part of the enclosing row. -/
theorem t_prefix_index (s : Shape) (w m before after rows : ℕ)
    (x : Address s w m before after rows) :
    Fin.cast (t_prefix_repetitions s w before rows)
      (targetPrefixIndex s w m before after rows x)=
        pack (pack (pack (pack x.row x.u) x.uTail) x.t) (tRestIndex s w m before after rows x) := by
  apply Fin.ext
  change (targetPrefixIndex s w m before after rows x).val=
    (pack (pack (pack (pack x.row x.u) x.uTail) x.t) (tRestIndex s w m before after rows x)).val
  rw [target_prefix_value]
  unfold tCopies
  simp only [tRestIndex,pack_val]
  ring

def compactSuffix (s : Shape) (w : ℕ) := 2^(s.H-w+s.B)*s.payload

def tPrefix (s : Shape) (w rows : ℕ) := (rows*2^w)*2^(s.H-w)
def tGap (s : Shape) (w m before after : ℕ) :=
  ((((2^(s.H-w)*2^s.F)*2^before)*2^m)*2^after)
def uGap (s : Shape) (w m before after : ℕ) :=
  (((((((2^(s.H-w)*2^w)*2^(s.H-w))*2^s.F)*2^before)*2^m)*2^after))

theorem back_size (s : Shape) (w : ℕ) (hw : w≤s.H) :
    2^(s.H+s.B)=2^w*2^(s.H-w+s.B) := by
  rw [←pow_add]; congr 1; omega

def splitBack (s : Shape) (w : ℕ) (hw : w≤s.H) (v : Fin (2^(s.H+s.B))) :=
  finProdFinEquiv.symm (Fin.cast (back_size s w hw) v)

theorem splitBack_value (s : Shape) (w : ℕ) (hw : w≤s.H) (v : Fin (2^(s.H+s.B))) :
    (splitBack s w hw v).1.val*2^(s.H-w+s.B)+(splitBack s w hw v).2.val=v.val := by
  have h := congrArg Fin.val (finProdFinEquiv.apply_symm_apply (Fin.cast (back_size s w hw) v))
  change (pack (splitBack s w hw v).1 (splitBack s w hw v).2).val=v.val at h
  simpa only [pack_val] using h

theorem t_volume (s : Shape) (w m before after rows : ℕ) (hw : w≤s.H)
    (hactive : before+m+after=s.active*s.chunk) :
    RadixRangePadding.volume (tPrefix s w rows) (2^w) (tGap s w m before after)
      (compactSuffix s w)=rows*s.recordWidth := by
  rw [←size_eq s w m before after rows hw hactive]
  unfold RadixRangePadding.volume tPrefix tGap compactSuffix size
  rw [back_size s w hw]
  ring

theorem u_volume (s : Shape) (w m before after rows : ℕ) (hw : w≤s.H)
    (hactive : before+m+after=s.active*s.chunk) :
    RadixRangePadding.volume rows (2^w) (uGap s w m before after)
      (compactSuffix s w)=rows*s.recordWidth := by
  rw [←size_eq s w m before after rows hw hactive]
  unfold RadixRangePadding.volume uGap compactSuffix size
  rw [back_size s w hw]
  ring

def tIndex (s : Shape) (w m before after rows : ℕ) (hw : w≤s.H)
    (x : Address s w m before after rows) :=
  RadixRangePadding.index (pack (pack x.row x.u) x.uTail) x.t
    (pack (pack (pack (pack x.tTail x.frontSlack) x.activeBefore) x.target) x.activeAfter)
    (splitBack s w hw x.back).1 (pack (splitBack s w hw x.back).2 x.payload)

def uIndex (s : Shape) (w m before after rows : ℕ) (hw : w≤s.H)
    (x : Address s w m before after rows) :=
  RadixRangePadding.index x.row x.u
    (pack (pack (pack (pack (pack (pack x.uTail x.t) x.tTail) x.frontSlack) x.activeBefore) x.target) x.activeAfter)
    (splitBack s w hw x.back).1 (pack (splitBack s w hw x.back).2 x.payload)

theorem t_index (s : Shape) (w m before after rows : ℕ) (hw : w≤s.H)
    (hactive : before+m+after=s.active*s.chunk) (x : Address s w m before after rows) :
    Fin.cast (t_volume s w m before after rows hw hactive)
      (tIndex s w m before after rows hw x)=index s w m before after rows hw hactive x := by
  apply Fin.ext
  change (tIndex s w m before after rows hw x).val=(index s w m before after rows hw hactive x).val
  rw [index_val]
  simp only [tIndex,RadixRangePadding.index,pack_val]
  rw [←splitBack_value s w hw x.back,back_size s w hw]
  ring

theorem u_index (s : Shape) (w m before after rows : ℕ) (hw : w≤s.H)
    (hactive : before+m+after=s.active*s.chunk) (x : Address s w m before after rows) :
    Fin.cast (u_volume s w m before after rows hw hactive)
      (uIndex s w m before after rows hw x)=index s w m before after rows hw hactive x := by
  apply Fin.ext
  change (uIndex s w m before after rows hw x).val=(index s w m before after rows hw hactive x).val
  rw [index_val]
  simp only [uIndex,RadixRangePadding.index,pack_val]
  rw [←splitBack_value s w hw x.back,back_size s w hw]
  ring

/-- Both compact exchanges expose the same complete pre-back prefix: the
entire active block is before the compact rotation target. -/
theorem compact_rotation_prefix (s : Shape) (w m before after rows : ℕ) (hw : w≤s.H)
    (hactive : before+m+after=s.active*s.chunk) :
    rows*2^w*uGap s w m before after=
      rows*2^(2*s.H+s.F+s.active*s.chunk) ∧
    tPrefix s w rows*2^w*tGap s w m before after=
      rows*2^(2*s.H+s.F+s.active*s.chunk) := by
  have he : w+(s.H-w)+w+(s.H-w)+s.F+before+m+after=2*s.H+s.F+s.active*s.chunk := by omega
  constructor
  all_goals calc
    _ = rows*2^(w+(s.H-w)+w+(s.H-w)+s.F+before+m+after) := by
      dsimp [uGap,tPrefix,tGap]
      simp only [pow_add]
      ring
    _ = _ := by rw [he]

theorem t_prefix_carved (s : Shape) (w rows : ℕ) (hw : w≤s.H) :
    tPrefix s w rows=s.prefixRange rows .control := by
  unfold tPrefix Shape.prefixRange Shape.prefixBits
  rw [Nat.mul_assoc,←pow_add,Nat.add_sub_of_le hw]

theorem t_gap_carved (s : Shape) (w m before after : ℕ)
    (hactive : before+m+after=s.active*s.chunk) :
    tGap s w m before after=CompactGadgetReservationHeadersCarvedData.gap s w .control := by
  have he : (s.H-w)+s.F+before+m+after=(s.H-w)+s.F+s.active*s.chunk := by omega
  unfold tGap CompactGadgetReservationHeadersCarvedData.gap
    CompactGadgetReservationHeadersCarvedData.gapBits
  rw [←pow_add,←pow_add,←pow_add,←pow_add,he]

theorem u_gap_carved (s : Shape) (w m before after : ℕ) (hw : w≤s.H)
    (hactive : before+m+after=s.active*s.chunk) :
    uGap s w m before after=CompactGadgetReservationHeadersCarvedData.gap s w .temp := by
  have he : (s.H-w)+w+(s.H-w)+s.F+before+m+after=(s.H-w)+s.H+s.F+s.active*s.chunk := by omega
  unfold uGap CompactGadgetReservationHeadersCarvedData.gap
    CompactGadgetReservationHeadersCarvedData.gapBits
  rw [←pow_add,←pow_add,←pow_add,←pow_add,←pow_add,←pow_add,he]

theorem compact_suffix_carved (s : Shape) (w : ℕ) :
    compactSuffix s w=CompactGadgetReservationHeadersCarvedData.suffix s w := rfl

def backPrefix (s : Shape) (w m before after rows : ℕ) :=
  (targetPrefix s w before rows*2^m)*2^after

def backPrefixIndex (s : Shape) (w m before after rows : ℕ)
    (x : Address s w m before after rows) : Fin (backPrefix s w m before after rows) :=
  pack (pack (targetPrefixIndex s w m before after rows x) x.target) x.activeAfter

/-- A back rotation reads the complete original front/active prefix. Its
source may be any coordinate in the active block, without a gather move. -/
theorem back_prefix_bits (s : Shape) (w m before after rows : ℕ) (hw : w≤s.H)
    (hactive : before+m+after=s.active*s.chunk) :
    backPrefix s w m before after rows=rows*2^(2*s.H+s.F+s.active*s.chunk) := by
  unfold backPrefix
  rw [target_prefix_bits s w before rows hw]
  rw [Nat.mul_assoc,←pow_add,Nat.mul_assoc,←pow_add]
  congr 2
  omega

theorem back_prefix_value (s : Shape) (w m before after rows : ℕ)
    (x : Address s w m before after rows) :
    (backPrefixIndex s w m before after rows x).val=
      ((targetPrefixIndex s w m before after rows x).val*2^m+x.target.val)*2^after+x.activeAfter.val := by
  simp only [backPrefixIndex,pack_val]

def backIndex (s : Shape) (w m before after rows : ℕ) (hw : w≤s.H)
    (x : Address s w m before after rows) :=
  FiberLayoutData.index (backPrefixIndex s w m before after rows x)
    (splitBack s w hw x.back).1 (pack (splitBack s w hw x.back).2 x.payload)

theorem back_volume (s : Shape) (w m before after rows : ℕ) (hw : w≤s.H)
    (hactive : before+m+after=s.active*s.chunk) :
    backPrefix s w m before after rows*(2^w*compactSuffix s w)=rows*s.recordWidth := by
  rw [←size_eq s w m before after rows hw hactive]
  unfold backPrefix targetPrefix compactSuffix size
  rw [back_size s w hw]
  ring

theorem back_index (s : Shape) (w m before after rows : ℕ) (hw : w≤s.H)
    (hactive : before+m+after=s.active*s.chunk) (x : Address s w m before after rows) :
    Fin.cast (back_volume s w m before after rows hw hactive)
      (backIndex s w m before after rows hw x)=index s w m before after rows hw hactive x := by
  apply Fin.ext
  change (backIndex s w m before after rows hw x).val=(index s w m before after rows hw hactive x).val
  rw [index_val]
  unfold backIndex
  rw [FiberLayoutData.index_val]
  rw [back_prefix_value,target_prefix_value,pack_val]
  rw [←splitBack_value s w hw x.back,back_size s w hw]
  ring

end IntegerMultBounds.Machine.CompactActiveTargetGeometry
