module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorEnumeration
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreIntervalCode
public import IntegerMultBounds.NLogN.PhaseCellCoreGather

/-! # Executed ordered core descriptor enumeration

A bounded table loop computes and emits every origin/length pair. The finite
loop count is an explicit scalar input; its generation is charged by the caller.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellMatrix

def coreDescriptorRow : TblCode 16 :=
  coreIntervalCode ;; tblBlock 16 [.emit 9 12] (.emit 11 12)

theorem coreDescriptorRow_do {A W w s width k : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (hw : st.val 1 = width) (hk : st.val 4 = k)
    (hz : st.val 12 = 0) (hstart : coreStart width k ≤ s) (hwide : s < 2^W) :
    TblDo A W w coreDescriptorRow st (fun st' =>
      st'.acc = (tblPairs A w (coreStart width k) 0++tblPairs A w (coreLength s width k) 0).reverse++st.acc ∧
      ∀ i, i ∉ [(8 : Fin 16),9,10,11] → st'.val i = st.val i) 8 := by
  have h := coreIntervalCode_do (A := A) (W := W) (w := w) st hs hw hk hstart hwide
  exact h.seq (K₂ := 2) (fun st₁ ⟨ha,hl,_,hacc,hframe⟩ => by
    apply TblDo.block
    · simp [tblFitsList,TblIns.fits]
    · have hz₁ := (hframe 12 (by simp)).trans hz
      constructor
      · simp [tblExactList,TblIns.exact,ha,hl,hz₁,hacc,List.reverse_append,List.append_assoc]
      · exact hframe)

def coreDescriptorCode : TblCode 16 := tblFor 4 15 coreDescriptorRow

theorem coreDescriptorCode_do {A W w s width : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (hw : st.val 1 = width) (hz : st.val 12 = 0)
    (hcount : st.val 15 = (s+width-1)/width) (hwidth : 0 < width)
    (hwide : s < 2^W) (hcountWide : (s+width-1)/width < 2^W) :
    TblDo A W w coreDescriptorCode st (fun st' =>
      st'.acc = ((coreIndices s width).flatMap (fun k =>
        tblPairs A w (coreStart width k) 0++tblPairs A w (coreLength s width k) 0)).reverse++st.acc)
      (11*((s+width-1)/width)+3) := by
  have h := descriptorEnumeration_do coreDescriptorRow
    (fun k => tblPairs A w (coreStart width k) 0++tblPairs A w (coreLength s width k) 0)
    st hcount hcountWide (K := 8) (fun j hj st₁ hf hindex =>
      coreDescriptorRow_do st₁ ((hf 0 (by simp)).trans hs) ((hf 1 (by simp)).trans hw) hindex
        ((hf 12 (by simp)).trans hz)
        (coreIndex_start_lt s width j hwidth (List.mem_range.mpr hj)).le hwide)
  simpa only [coreDescriptorCode,coreIndices,Nat.mul_comm] using h

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
