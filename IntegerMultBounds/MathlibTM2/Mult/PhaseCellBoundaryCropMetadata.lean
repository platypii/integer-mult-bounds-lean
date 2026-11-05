module

public import IntegerMultBounds.MathlibTM2.Fast.TableProg
public import IntegerMultBounds.MathlibTM2.Fast.TableNativePush
public import IntegerMultBounds.NLogN.PhaseCellBoundaryCropSchedule

/-! Fixed arithmetic for the two final crop slots. Slot zero has skip zero and
count width*wordWidth; the final slots share the quotient of s-1 by width. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.BoundaryCropMetadata
open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.NLogN.PhaseCellMatrix

/-- Inputs 0,1,2 are s, core width and word width. Outputs 7,8 are bit counts.
The Boolean is a fixed slot choice, not a runtime branch. -/
def ops (last : Bool) : List (TblIns 9) :=
  [.zero 3,.inc 3,.sub 0 3 4,.div 4 1 4,
    if last then .copy 4 4 else .sub 4 3 4,
    .mul 4 1 5,if last then .sub 0 5 6 else .copy 1 6,
    .mul 5 2 7,.mul 6 2 8]

def code (last : Bool) : TblCode 9 :=
  tblBlock 9 (ops last) (.copy 8 8)

def index (last : Bool) (s width : ℕ) : ℕ :=
  (s-1)/width - if last then 0 else 1

theorem index_eq_boundary (last : Bool) (s width : ℕ) (hw : 0 < width)
    (hroom : 3*width < s) :
    index last s width = boundaryCropIndex s width (if last then 2 else 1) := by
  have he : s+width-1 = (s-1)+width := by omega
  have hq : (s+width-1)/width = (s-1)/width+1 := by
    rw [he,Nat.add_div_right _ hw]
  cases last <;> simp [index,boundaryCropIndex,hq]

theorem run_spec (last : Bool) (D s width W A : ℕ) (st : TblSt 9 A)
    (hs : st.val 0 = s) (hw : st.val 1 = width) (hW : st.val 2 = W)
    (hwidth : 0 < width) (hword : 0 < W) (hroom : 3*width < s)
    (hfit : s*W < 2^D) :
    tblFitsList A D 0 (ops last) st ∧
      let final := tblExactList A 0 (ops last) st
      final.val 7 = coreStart width (index last s width)*W ∧
      final.val 8 = coreLength s width (index last s width)*W := by
  have hq : 1 ≤ (s-1)/width := (Nat.le_div_iff_mul_le hwidth).mpr (by omega)
  have hmul := Nat.div_mul_le_self (s-1) width
  have hsfit : s < 2^D := lt_of_le_of_lt (Nat.le_mul_of_pos_right s hword) hfit
  have hstart : ((s-1)/width-1)*width+width ≤ s := by
    have he : ((s-1)/width-1)*width+width = ((s-1)/width)*width := by
      rw [Nat.sub_mul, Nat.one_mul]
      exact Nat.sub_add_cancel (by simpa using Nat.mul_le_mul_right width hq)
    omega
  have hlast : ((s-1)/width)*width < s := by omega
  have hpenW := Nat.mul_le_mul_right W (show ((s-1)/width-1)*width ≤ s by omega)
  have hlastW := Nat.mul_le_mul_right W hlast.le
  have hwidthW := Nat.mul_le_mul_right W (show width ≤ s by omega)
  have htailW := Nat.mul_le_mul_right W (Nat.sub_le s (((s-1)/width)*width))
  have hrem : s-((s-1)/width)*width ≤ width := by
    have hm := Nat.mod_lt (s-1) hwidth
    have hd := Nat.div_add_mod (s-1) width
    rw [Nat.mul_comm width] at hd
    omega
  have hD : D ≠ 0 := by
    intro he
    subst D
    norm_num at hsfit
    omega
  have hqfit := Nat.div_le_self (s-1) width
  have hlenPen : min width (s-((s-1)/width-1)*width) = width := min_eq_left (by omega)
  have hlenLast : min width (s-((s-1)/width)*width) = s-((s-1)/width)*width := min_eq_right hrem
  cases last <;>
    simp [ops,tblFitsList,TblIns.fits,TblIns.exact,tblExactList,hs,hw,hW,
      index,coreStart,coreLength,hlenPen,hlenLast] <;>
    omega


/-- Both slots can reuse the same live input bank. -/
theorem run_inputs (last : Bool) (A : ℕ) (st : TblSt 9 A) :
    (∀ i : Fin 3, (tblExactList A 0 (ops last) st).val (Fin.castAdd 6 i) = st.val (Fin.castAdd 6 i)) ∧
      (tblExactList A 0 (ops last) st).acc = st.acc := by
  constructor
  · intro i
    fin_cases i <;> cases last <;> simp [ops,tblExactList,TblIns.exact]
  · cases last <;> rfl

/-- Ten table atoms suffice, independently of all numerical parameters. -/
theorem code_do (last : Bool) (D s width W A : ℕ) (st : TblSt 9 A)
    (hs : st.val 0 = s) (hw : st.val 1 = width) (hW : st.val 2 = W)
    (hwidth : 0 < width) (hword : 0 < W) (hroom : 3*width < s)
    (hfit : s*W < 2^D) :
    TblDo A D 0 (code last) st (fun z => z = tblExactList A 0 (ops last) st) 10 := by
  have hf := (run_spec last D s width W A st hs hw hW hwidth hword hroom hfit).1
  have hi : TblDo A D 0 (.ins (.copy 8 8)) (tblExactList A 0 (ops last) st)
      (fun z => z = tblExactList A 0 (ops last) st) 1 := by
    apply TblDo.insX
    · trivial
    · simp [TblIns.exact]
  simpa only [code,tblBlock,ops,List.length_cons,List.length_nil] using TblDo.straightX (ops last) hf hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.BoundaryCropMetadata
