module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreHaloDescriptorCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreDescriptorHost

/-! Emit the same analytic halos as origin/length pairs, matching the packed
coupling descriptor ABI. The full-system seam fallback remains ambient. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellMatrix

def coreHaloPacketValues (s width band n : ℕ) : List ℕ :=
  (coreIndices s width).flatMap (fun k =>
    [(coreHaloEndpoints s width k band n).1,
     (coreHaloEndpoints s width k band n).2-(coreHaloEndpoints s width k band n).1])

def coreHaloPacketRow : TblCode 16 :=
  coreHaloIntervalCode ;; tblBlock 16 [.sub 10 9 11,.emit 9 12] (.emit 11 12)

theorem coreHaloPacketRow_do {A W w s width k band n : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (hw : st.val 1 = width) (hk : st.val 4 = k)
    (hr : st.val 2 = n*band) (hz : st.val 12 = 0)
    (hstart : coreStart width k ≤ s) (hwide : s+n*band < 2^W) :
    TblDo A W w coreHaloPacketRow st (fun st' =>
      st'.acc = (tblPairs A w (coreHaloEndpoints s width k band n).1 0++
        tblPairs A w ((coreHaloEndpoints s width k band n).2-
          (coreHaloEndpoints s width k band n).1) 0).reverse++st.acc ∧
      ∀ i, i ∉ [(8 : Fin 16),9,10,11] → st'.val i = st.val i) 14 := by
  have h := coreHaloIntervalCode_do (A := A) (W := W) (w := w) st hs hw hk hr hz hstart hwide
  have hb := coreHaloEndpoints_bounds s width k band n
  exact h.seq (K₂ := 3) (fun st₁ ⟨ha,hb',hacc,hframe⟩ => by
    apply TblDo.block
    · simp [tblFitsList,TblIns.fits,ha,hb']
      omega
    · have hz₁ := (hframe 12 (by simp)).trans hz
      constructor
      · simp [tblExactList,TblIns.exact,ha,hb',hz₁,hacc,List.reverse_append,List.append_assoc]
      · intro i hi
        have hn : i ≠ 9 ∧ i ≠ 10 ∧ i ≠ 11 := by simp_all
        simpa [tblExactList,TblIns.exact,hn.1,hn.2.1,hn.2.2] using hframe i hi)

def coreHaloPacketCode : TblCode 16 := tblFor 4 15 coreHaloPacketRow

theorem coreHaloPacketCode_do {A W w s width band n : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (hw : st.val 1 = width) (hr : st.val 2 = n*band) (hz : st.val 12 = 0)
    (hcount : st.val 15 = (s+width-1)/width) (hwidth : 0 < width)
    (hwide : s+n*band < 2^W) (hcountWide : (s+width-1)/width < 2^W) :
    TblDo A W w coreHaloPacketCode st (fun st' =>
      st'.acc = ((coreHaloPacketValues s width band n).flatMap (fun x => tblPairs A w x 0)).reverse++st.acc)
      (17*((s+width-1)/width)+3) := by
  have h := descriptorEnumeration_do coreHaloPacketRow
    (fun k => tblPairs A w (coreHaloEndpoints s width k band n).1 0++
      tblPairs A w ((coreHaloEndpoints s width k band n).2-(coreHaloEndpoints s width k band n).1) 0)
    st hcount hcountWide (K := 14) (fun j hj st₁ hf hindex =>
      coreHaloPacketRow_do st₁ ((hf 0 (by simp)).trans hs) ((hf 1 (by simp)).trans hw) hindex
        ((hf 2 (by simp)).trans hr) ((hf 12 (by simp)).trans hz)
        (coreIndex_start_lt s width j hwidth (List.mem_range.mpr hj)).le hwide)
  simpa [coreHaloPacketCode,coreHaloPacketValues,coreIndices,List.flatMap_assoc,Nat.mul_comm] using h

def generatedCoreHaloPacketCode : TblCode 16 := coreDescriptorInit ;; coreHaloPacketCode

theorem generatedCoreHaloPacketCode_do {A W w s width band n : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (hw : st.val 1 = width) (hr : st.val 2 = n*band)
    (hwidth : 0 < width) (hwide : s+width+n*band < 2^W) :
    TblDo A W w generatedCoreHaloPacketCode st (fun st' =>
      st'.acc = ((coreHaloPacketValues s width band n).flatMap (fun x => tblPairs A w x 0)).reverse++st.acc)
      (17*((s+width-1)/width)+9) := by
  have hc : (s+width-1)/width < 2^W :=
    (Nat.div_le_self _ _).trans_lt ((Nat.sub_le _ _).trans_lt (by omega))
  have h := coreDescriptorInit_do (A := A) (W := W) (w := w) st hs hw hwidth (by omega)
  exact (h.seq (fun st₁ ⟨hs₁,hw₁,hz,hcount,hacc,hframe⟩ =>
    (coreHaloPacketCode_do st₁ hs₁ hw₁ ((hframe 2 (by simp)).trans hr) hz hcount hwidth
      (by omega) hc).mono (fun st₂ he => by rw [he,hacc]) le_rfl)).mono
        (fun _ he => he) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
