module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicRowEmitCode

/-! Enumerate the computed stage count with one fixed selector/emitter body.
The proof is over the prefix of the arithmetic row sequence, not finite cases. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM

def dyadicScheduleRowsCode : TblCode 16 := tblFor 15 3 dyadicRowEmitCode

theorem dyadicScheduleRowsCode_do {A W w a b C : ℕ} (st : TblSt 16 A)
    (ha : st.val 6 = a) (hb : st.val 7 = b) (hC : st.val 4 = C)
    (hn : st.val 3 = dyadicStageCount (a+b) a b)
    (hbits : a+b < W) (hfit : C*2^(a+b) < 2^W) :
    TblDo A W w dyadicScheduleRowsCode st (fun F =>
      F.val 3 = dyadicStageCount (a+b) a b ∧ F.val 15 = dyadicStageCount (a+b) a b ∧
      F.acc = ((dyadicScheduleValues (a+b) a b C).flatMap (fun x => tblPairs A w x 0)).reverse++st.acc ∧
      ∀ j, j ∉ generatedDyadicSelectorWrites → j ≠ 15 → F.val j = st.val j)
      (dyadicStageCount (a+b) a b*((a+b)*(4*(a+b)+19)+18)+3) := by
  let N := dyadicStageCount (a+b) a b
  let packets := fun j => (List.ofFn (selectDyadicStage (a+b) a b C N j).values).flatMap
    (fun x => tblPairs A w x 0)
  let Inv := fun (j : ℕ) (s : TblSt 16 A) => s.acc = ((List.range j).flatMap packets).reverse++st.acc ∧
    ∀ k, k ∉ generatedDyadicSelectorWrites → k ≠ (15 : Fin 16) → s.val k = st.val k
  have hNW : N < 2^W := (dyadicStageCount_le (a+b) a b (by omega)).trans_lt
    (hbits.trans Nat.lt_two_pow_self)
  have hpack : (List.range N).flatMap packets =
      (dyadicScheduleValues (a+b) a b C).flatMap (fun x => tblPairs A w x 0) := by
    simp only [dyadicScheduleValues,dyadicSelectedRows,List.flatMap_map,List.flatMap_assoc,packets,N]
  unfold dyadicScheduleRowsCode
  apply (TblDo.for (i := (15 : Fin 16)) (nv := 3) N ((a+b)*(4*(a+b)+19)+15)
    hn hNW (by decide) Inv ?_ ?_ ?_).mono (fun _ h => h) (by dsimp [N]; apply le_of_eq; ring)
  · refine ⟨by simp,?_⟩
    intro k hk hk15
    exact Function.update_of_ne hk15 _ _
  · intro j hj s hI hsi hsn
    rcases hI with ⟨hacc,hframe⟩
    have haS := (hframe 6 (by decide) (by decide)).trans ha
    have hbS := (hframe 7 (by decide) (by decide)).trans hb
    have hCS := (hframe 4 (by decide) (by decide)).trans hC
    have hrow := dyadicRowEmitCode_do (W := W) (w := w) s haS hbS hCS hsn hsi hbits hfit hj
    exact hrow.mono (fun F hF => by
      rcases hF with ⟨hout,hkeep⟩
      refine ⟨(hkeep 15 (by decide)).trans hsi,(hkeep 3 (by decide)).trans hsn,?_,?_⟩
      · change F.acc = ((List.range (j+1)).flatMap packets).reverse++st.acc
        change F.acc = (packets j).reverse++s.acc at hout
        rw [hout,hacc]
        simp only [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
          List.append_nil,List.reverse_append,List.append_assoc]
      · intro k hk hk15
        change Function.update F.val 15 (j+1) k = st.val k
        rw [Function.update_of_ne hk15,hkeep k hk,hframe k hk hk15]) le_rfl
  · intro s hI hsi hsn
    rcases hI with ⟨hacc,hframe⟩
    exact ⟨hsn,hsi,by rw [←hpack]; exact hacc,hframe⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
