module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreGatherEmit
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreDescriptorHost

/-! # Executed generation of an ordered halo group's origins

The count comes from s and core width. The same predicate defines mathematical
group membership and selects emitted origins. No origin list is an input.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellMatrix

def coreGatherCode : TblCode 16 := tblFor 4 15 coreGatherRowCode

theorem coreGatherCode_do {A W w s width radius L : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (hw : st.val 1 = width) (hr : st.val 2 = radius)
    (hL : st.val 3 = L) (hz : st.val 12 = 0) (hcount : st.val 15 = (s+width-1)/width)
    (hwidth : 0 < width) (hwide : s+2*radius < 2^W) (hcountWide : (s+width-1)/width < 2^W) :
    TblDo A W w coreGatherCode st (fun st' =>
      st'.acc = ((coreGatherIndices s width radius L).flatMap (fun k =>
        tblPairs A w (coreStart width k-radius) 0)).reverse++st.acc)
      (18*((s+width-1)/width)+3) := by
  let pred := fun k => radius ≤ coreStart width k ∧
    coreStart width k+coreLength s width k+radius ≤ s ∧ coreLength s width k+2*radius = L
  let F := fun k => if pred k then tblPairs A w (coreStart width k-radius) 0 else []
  have h := descriptorEnumeration_do coreGatherRowCode F st hcount hcountWide (K := 15)
    (fun j hj st₁ hf hindex => coreGatherRowCode_do st₁
      ((hf 0 (by simp)).trans hs) ((hf 1 (by simp)).trans hw) hindex
      ((hf 2 (by simp)).trans hr) ((hf 3 (by simp)).trans hL) ((hf 12 (by simp)).trans hz)
      (coreIndex_start_lt s width j hwidth (List.mem_range.mpr hj)).le hwide)
  have hfilter (ks : List ℕ) : ks.flatMap F = (ks.filter (fun k => decide (pred k))).flatMap
      (fun k => tblPairs A w (coreStart width k-radius) 0) := by
    induction ks with
    | nil => rfl
    | cons k ks ih => by_cases hp : pred k <;> simp [F,hp,ih]
  simpa only [hfilter,pred,coreGatherCode,coreGatherIndices,coreIndices,Nat.mul_comm] using h

def generatedCoreGatherCode : TblCode 16 := coreDescriptorInit ;; coreGatherCode

theorem generatedCoreGatherCode_do {A W w s width radius L : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (hw : st.val 1 = width) (hr : st.val 2 = radius) (hL : st.val 3 = L)
    (hwidth : 0 < width) (hwide : s+width+2*radius < 2^W) :
    TblDo A W w generatedCoreGatherCode st (fun st' =>
      st'.acc = ((coreGatherIndices s width radius L).flatMap (fun k =>
        tblPairs A w (coreStart width k-radius) 0)).reverse++st.acc)
      (18*((s+width-1)/width)+9) := by
  have hc : (s+width-1)/width < 2^W :=
    (Nat.div_le_self _ _).trans_lt ((Nat.sub_le _ _).trans_lt (by omega))
  have h := coreDescriptorInit_do (A := A) (W := W) (w := w) st hs hw hwidth (by omega)
  exact (h.seq (fun st₁ ⟨hs₁,hw₁,hz,hcount,hacc,hframe⟩ =>
    (coreGatherCode_do st₁ hs₁ hw₁ ((hframe 2 (by simp)).trans hr)
      ((hframe 3 (by simp)).trans hL) hz hcount hwidth (by omega) hc).mono
      (fun st₂ he => by rw [he,hacc]) le_rfl)).mono (fun _ he => he) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
