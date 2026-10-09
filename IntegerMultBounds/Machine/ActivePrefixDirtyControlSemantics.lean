import IntegerMultBounds.Machine.ActivePrefixDirtyControlPlaced
import IntegerMultBounds.Machine.GatherStreamData
import IntegerMultBounds.Machine.CountedPackedParityValue
import IntegerMultBounds.Machine.BinaryVaryingControlOffsetData

/-! The generated control stream reads precisely bit zero of each compact
b-bit U digit in each original prefix row. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlSemantics
open ActivePrefixDirtyControlData
open BinaryVaryingSelectedOffsetData (stream)
open BinaryVaryingOffsetGatherPlaced (Kind sourceWidth)
variable {k : Kind}

def sourceRow (s : Shape k) (i : ℕ) := Gather.field (BinaryAddressTableData.row s.W i) s.startU (s.n*s.b)
def tempRow (s : Shape k) (i : ℕ) := Gather.field (BinaryAddressTableData.row s.W i) s.startT (tempWidth s)
def controls (s : Shape k) (i : ℕ) := CountedPackedParityRun.parities s.b (sourceRow s i) s.n

@[simp] theorem controls_length (s : Shape k) (i : ℕ) : (controls s i).length=s.n := by simp [controls]

theorem controls_entry (s : Shape k) (i j : ℕ) (hi : i<2^s.W) (hj : j<s.n) :
    (controls s i)[j]'(by simpa using hj)=Nat.testBit i (s.startU+j*s.b) := by
  simp only [controls,CountedPackedParityRun.parities,List.getElem_map,List.getElem_range,sourceRow]
  rw [ActivePrefixSelectedOffsetData.field_bit _ s.startU (s.n*s.b) (j*s.b) (by nlinarith [s.hb])]
  rw [←Compact.PowerTwo.testBit_value,BinaryAddressTableData.row_rank s.W i hi]

theorem parities_stream (N n b : ℕ) (hb : 1≤b) (rows : ℕ → List Bool)
    (hw : ∀ i<N, (rows i).length=n*b) :
    CountedPackedParityRun.parities b (stream N rows) (N*n)=
      stream N (fun i => CountedPackedParityRun.parities b (rows i) n) := by
  have hlen := BinaryVaryingSelectedOffsetData.stream_length N n
    (fun i => CountedPackedParityRun.parities b (rows i) n) (by intros; simp)
  apply List.ext_getElem
  · simpa using hlen.symm
  · intro r hr hr'
    have hrn : r<N*n := by simpa using hr
    have hn : 0<n := by nlinarith
    have hi : r/n<N := (Nat.div_lt_iff_lt_mul hn).mpr hrn
    have hj : r%n<n := Nat.mod_lt _ hn
    have hsplit : r/n*n+r%n=r := by simpa [Nat.mul_comm] using Nat.div_add_mod r n
    have h := BinaryVaryingSelectedOffsetData.stream_entry N (n*b) rows hw
      (r/n) ((r%n)*b) hi (by nlinarith)
    have hindex : r*b=r/n*(n*b)+(r%n)*b := by nlinarith
    simp only [CountedPackedParityRun.parities,List.getElem_map,List.getElem_range]
    rw [hindex,h]
    have hh := BinaryVaryingSelectedOffsetData.stream_entry N n
      (fun i => CountedPackedParityRun.parities b (rows i) n) (by intros; simp) (r/n) (r%n) hi hj
    rw [hsplit,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hr',Option.getD_some] at hh
    have he : (CountedPackedParityRun.parities b (rows (r/n)) n).getD (r%n) false=
        (rows (r/n)).getD ((r%n)*b) false := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa using hj),Option.getD_some]
      simp only [CountedPackedParityRun.parities,List.getElem_map,List.getElem_range]
    simpa only [CountedPackedParityRun.parities] using (hh.trans he).symm

theorem extracted_controls (s : Shape k) : controlWord s=stream (2^s.W) (controls s) := by
  unfold controlWord sourceWord
  rw [show (clockWord s).length=2^s.W*s.n by simp [clockWord],BinaryPrefixFieldTableData.word_rows]
  exact parities_stream (2^s.W) s.n s.b s.hb (sourceRow s) (by intros; exact Gather.field_length _ _ _)

theorem controls_eq_digit_parities (s : Shape k) (i : ℕ) :
    (controls s i).map Compact.PowerTwo.ctrl=
      (Compact.Radix.digits ((2 : ℤ)^s.b) s.n (Counter.value (sourceRow s i))).map (· % 2) :=
  CountedPackedParityValue.controls_eq_digit_parities s.b s.hb (sourceRow s i) s.n (Gather.field_length _ _ _)

theorem selected_row (s : Shape .selected) (i : ℕ) (hi : i<2^s.W) :
    Gather.field (offsetWord s) (i*(s.n*s.q)) (s.n*s.q)=
      Gather.gather (fun x z => x && z) (PackedArith.maskShift s.q s.b s.hb s.hbq)
        (tempRow s i) (controls s i) s.n := by
  change Gather.field (BinaryVaryingSelectedOffsetGather.word s.q s.b s.hb s.hbq
    (BinaryPrefixFieldTableData.word s.W s.startT (s.n*s.b) s.tempFits) (controlWord s)) _ _=_
  rw [extracted_controls,BinaryPrefixFieldTableData.word_rows s.W s.startT (s.n*s.b) s.tempFits]
  exact BinaryVaryingSelectedOffsetData.field_eq s.q s.b s.n (2^s.W) i (tempRow s) (controls s)
    s.hb s.hbq (by intros; exact Gather.field_length _ _ _) (by intros; simp) hi

theorem control_row (s : Shape .control) (i : ℕ) (hi : i<2^s.W) :
    Gather.field (offsetWord s) (i*(s.n*s.q)) (s.n*s.q)=
      Compact.PowerTwo.toggleMask s.q (controls s i) := by
  change Gather.field (BinaryVaryingControlOffsetGather.word s.q s.b s.hb s.hbq
    (tempWord s) (controlWord s)) _ _=_
  rw [extracted_controls]
  exact BinaryVaryingControlOffsetData.field_eq s.q s.b s.n (2^s.W) i (tempWord s) (controls s)
    s.hb s.hbq (by intros; simp) hi

theorem parity_row (s : Shape .parity) (i : ℕ) (hi : i<2^s.W) :
    Gather.field (offsetWord s) (i*(s.n*s.b)) (s.n*s.b)=
      Gather.gather xor (PackedArith.parity s.q s.b s.hb s.hbq)
        (tempRow s i) (controls s i) s.n := by
  change Gather.field (Gather.gather xor (PackedArith.parity s.q s.b s.hb s.hbq)
    (BinaryPrefixFieldTableData.word s.W s.startT (s.n*s.q) s.tempFits) (controlWord s)
    (controlWord s).length) _ _=_
  rw [extracted_controls,BinaryPrefixFieldTableData.word_rows s.W s.startT (s.n*s.q) s.tempFits]
  exact GatherStreamData.field_eq xor (PackedArith.parity s.q s.b s.hb s.hbq) s.hb s.n (2^s.W) i
    (tempRow s) (controls s) (by intros; exact Gather.field_length _ _ _) (by intros; simp) hi

end IntegerMultBounds.Machine.ActivePrefixDirtyControlSemantics
