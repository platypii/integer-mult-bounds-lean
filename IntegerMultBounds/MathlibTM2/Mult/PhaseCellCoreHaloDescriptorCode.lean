module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorEnumeration
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreHaloCode
public import IntegerMultBounds.NLogN.PhaseCellCoreGather

/-! # Generated halo endpoint stream

The shared enumeration theorem emits the computed start/stop pairs in core
order. Each pair is exactly the interval consumed by the existing S3 ABI.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellMatrix

def coreHaloDescriptorRow : TblCode 16 :=
  coreHaloIntervalCode ;; tblBlock 16 [.emit 9 12] (.emit 10 12)

theorem coreHaloDescriptorRow_do {A W w s width k band n : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (hw : st.val 1 = width) (hk : st.val 4 = k)
    (hr : st.val 2 = n*band) (hz : st.val 12 = 0)
    (hstart : coreStart width k ≤ s) (hwide : s+n*band < 2^W) :
    TblDo A W w coreHaloDescriptorRow st (fun st' =>
      st'.acc = (tblPairs A w (coreHaloEndpoints s width k band n).1 0++
        tblPairs A w (coreHaloEndpoints s width k band n).2 0).reverse++st.acc ∧
      ∀ i, i ∉ [(8 : Fin 16),9,10,11] → st'.val i = st.val i) 13 := by
  have h := coreHaloIntervalCode_do (A := A) (W := W) (w := w) st hs hw hk hr hz hstart hwide
  exact h.seq (K₂ := 2) (fun st₁ ⟨ha,hb,hacc,hframe⟩ => by
    apply TblDo.block
    · simp [tblFitsList,TblIns.fits]
    · have hz₁ := (hframe 12 (by simp)).trans hz
      constructor
      · simp [tblExactList,TblIns.exact,ha,hb,hz₁,hacc,List.reverse_append,List.append_assoc]
      · exact hframe)

def coreHaloDescriptorCode : TblCode 16 := tblFor 4 15 coreHaloDescriptorRow

theorem coreHaloDescriptorCode_do {A W w s width band n : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (hw : st.val 1 = width) (hr : st.val 2 = n*band) (hz : st.val 12 = 0)
    (hcount : st.val 15 = (s+width-1)/width) (hwidth : 0 < width)
    (hwide : s+n*band < 2^W) (hcountWide : (s+width-1)/width < 2^W) :
    TblDo A W w coreHaloDescriptorCode st (fun st' =>
      st'.acc = ((coreIndices s width).flatMap (fun k =>
        tblPairs A w (coreHaloEndpoints s width k band n).1 0++
        tblPairs A w (coreHaloEndpoints s width k band n).2 0)).reverse++st.acc)
      (16*((s+width-1)/width)+3) := by
  have h := descriptorEnumeration_do coreHaloDescriptorRow
    (fun k => tblPairs A w (coreHaloEndpoints s width k band n).1 0++
      tblPairs A w (coreHaloEndpoints s width k band n).2 0)
    st hcount hcountWide (K := 13) (fun j hj st₁ hf hindex =>
      coreHaloDescriptorRow_do st₁ ((hf 0 (by simp)).trans hs) ((hf 1 (by simp)).trans hw) hindex
        ((hf 2 (by simp)).trans hr) ((hf 12 (by simp)).trans hz)
        (coreIndex_start_lt s width j hwidth (List.mem_range.mpr hj)).le hwide)
  simpa only [coreHaloDescriptorCode,coreIndices,Nat.mul_comm] using h

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
