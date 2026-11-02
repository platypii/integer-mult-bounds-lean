module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedDyadicSelector
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableEmitVariables

/-! Compute and emit one complete interchange row in the stream reader's
five-field order. Packet emission preserves the retained table values. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM

def dyadicRowEmitCode : TblCode 16 :=
  .seq generatedDyadicSelectorCode (tblEmitVars 2 11 [14,9,10,10])

theorem dyadicRowEmitCode_do {A W w a b C i : ℕ} (st : TblSt 16 A)
    (ha : st.val 6 = a) (hb : st.val 7 = b) (hC : st.val 4 = C)
    (hn : st.val 3 = dyadicStageCount (a+b) a b) (hi : st.val 15 = i)
    (hbits : a+b < W) (hfit : C*2^(a+b) < 2^W) (hindex : i < dyadicStageCount (a+b) a b) :
    let row := selectDyadicStage (a+b) a b C (dyadicStageCount (a+b) a b) i
    TblDo A W w dyadicRowEmitCode st (fun F =>
      F.acc = ((List.ofFn row.values).flatMap (fun x => tblPairs A w x 0)).reverse++st.acc ∧
      ∀ j, j ∉ generatedDyadicSelectorWrites → F.val j = st.val j)
      ((a+b)*(4*(a+b)+19)+15) := by
  have hs := generatedDyadicSelectorCode_do (W := W) (w := w) st ha hb hC hn hi hbits hfit hindex
  unfold dyadicRowEmitCode
  apply (hs.seq (K₂ := 5) ?_).mono (fun _ h => h) (by omega)
  intro s ⟨h11,h9,h10,h5,hzero,hone,hacc,hframe⟩
  exact (tblEmitVars_do (W := W) (w := w) 2 11 [14,9,10,10] s hzero).mono (fun F hF => by
    rcases hF with ⟨hv,haF⟩
    refine ⟨?_,?_⟩
    · simpa only [DyadicStageRow.values_list,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        h11,h9,h10,hone,hacc,List.append_assoc] using haF
    · intro j hj
      rw [hv]
      exact hframe j hj) le_rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
