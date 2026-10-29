module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreIntervalCode
public import IntegerMultBounds.NLogN.PhaseCellCoreDescriptors

/-! # Checked selection of interval halos

The two endpoint comparisons use the same fit predicate as the analytic halo.
A nonfitting halo becomes the original full line, never a new periodic matrix.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellMatrix

def coreHaloChoose : TblCode 16 :=
  .ite 9 2 (tblBlock 16 [.copy 12 9] (.copy 0 10))
    (.ite 0 8 (tblBlock 16 [.copy 12 9] (.copy 0 10))
      (tblBlock 16 [.sub 9 2 9] (.copy 8 10)))

theorem coreHaloChoose_do {A W w s width k band n : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (hr : st.val 2 = n*band) (hz : st.val 12 = 0)
    (ha : st.val 9 = coreStart width k)
    (hb : st.val 8 = coreStart width k+coreLength s width k+n*band)
    (hwide : coreStart width k < 2^W) :
    TblDo A W w coreHaloChoose st (fun st' => st' =
      ⟨Function.update (Function.update st.val 9 (coreHaloEndpoints s width k band n).1)
        10 (coreHaloEndpoints s width k band n).2,st.acc⟩) 4 := by
  by_cases hleft : coreStart width k < n*band
  · apply TblDo.iteT (by simpa [ha,hr] using hleft)
    have hnot : ¬ (n*band ≤ coreStart width k ∧
        coreStart width k+coreLength s width k+n*band ≤ s) := by omega
    have hblock : TblDo A W w (tblBlock 16 [.copy 12 9] (.copy 0 10)) st
        (fun st' => st' = ⟨Function.update (Function.update st.val 9 0) 10 s,st.acc⟩) 2 := by
      apply TblDo.block
      · simp [tblFitsList,TblIns.fits]
      · simp [tblExactList,TblIns.exact,hs,hz]
    exact hblock.mono (fun _ he => by simpa [coreHaloEndpoints,hnot] using he) (by decide)
  · apply TblDo.iteF (by simpa [ha,hr] using hleft)
    by_cases hright : s < coreStart width k+coreLength s width k+n*band
    · apply TblDo.iteT (by simpa [hs,hb] using hright)
      apply TblDo.block
      · simp [tblFitsList,TblIns.fits]
      · have hnot : ¬ (n*band ≤ coreStart width k ∧
            coreStart width k+coreLength s width k+n*band ≤ s) := by omega
        simp [tblExactList,TblIns.exact,hs,hz,coreHaloEndpoints,hnot]
    · apply TblDo.iteF (by simpa [hs,hb] using hright)
      apply TblDo.block
      · simp [tblFitsList,TblIns.fits,ha,hr,hwide]
        omega
      · have hfit : n*band ≤ coreStart width k ∧
            coreStart width k+coreLength s width k+n*band ≤ s := by omega
        simp [tblExactList,TblIns.exact,ha,hr,hb,coreHaloEndpoints,hfit]

/-- Pad the computed core, then select either its interval or the full line. -/
def coreHaloPadCode : TblCode 16 := .ins (.add 10 2 8) ;; coreHaloChoose

theorem coreHaloPadCode_do {A W w s width k band n : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (hr : st.val 2 = n*band) (hz : st.val 12 = 0)
    (ha : st.val 9 = coreStart width k)
    (hb : st.val 10 = coreStart width k+coreLength s width k)
    (hwide : coreStart width k+coreLength s width k+n*band < 2^W) :
    TblDo A W w coreHaloPadCode st (fun st' =>
      st'.val 9 = (coreHaloEndpoints s width k band n).1 ∧
      st'.val 10 = (coreHaloEndpoints s width k band n).2 ∧ st'.acc = st.acc ∧
      ∀ i, i ∉ [(8 : Fin 16),9,10] → st'.val i = st.val i) 5 := by
  let S₁ : TblSt 16 A := ⟨Function.update st.val 8
    (coreStart width k+coreLength s width k+n*band),st.acc⟩
  have h₁ : TblDo A W w (.ins (.add 10 2 8)) st (fun st' => st' = S₁) 1 := by
    apply TblDo.insX
    · simpa [TblIns.fits,hb,hr] using hwide
    · simp [TblIns.exact,S₁,hb,hr]
  have h₂ := coreHaloChoose_do (A := A) (W := W) (w := w) S₁
    (by simpa [S₁] using hs) (by simpa [S₁] using hr) (by simpa [S₁] using hz)
    (by simpa [S₁] using ha) (by simp [S₁]) (by omega : coreStart width k < 2^W)
  have hseq : TblDo A W w coreHaloPadCode st (fun st' => st' =
      ⟨Function.update (Function.update S₁.val 9 (coreHaloEndpoints s width k band n).1)
        10 (coreHaloEndpoints s width k band n).2,S₁.acc⟩) 5 := by
    unfold coreHaloPadCode
    exact h₁.seq (K₂ := 4) (fun st₁ he => by subst st₁; exact h₂)
  exact hseq.mono (fun st' he => by
    subst st'
    refine ⟨by simp,by simp,rfl,?_⟩
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
    simp [S₁,hi.1,hi.2.1,hi.2.2]) le_rfl

def coreHaloIntervalCode : TblCode 16 := coreIntervalCode ;; coreHaloPadCode

/-- Eleven table atoms compute the actual halo endpoint pair from core index
and ordinary geometry parameters, preserving all other input fields. -/
theorem coreHaloIntervalCode_do {A W w s width k band n : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (hw : st.val 1 = width) (hk : st.val 4 = k)
    (hr : st.val 2 = n*band) (hz : st.val 12 = 0)
    (hstart : coreStart width k ≤ s) (hwide : s+n*band < 2^W) :
    TblDo A W w coreHaloIntervalCode st (fun st' =>
      st'.val 9 = (coreHaloEndpoints s width k band n).1 ∧
      st'.val 10 = (coreHaloEndpoints s width k band n).2 ∧ st'.acc = st.acc ∧
      ∀ i, i ∉ [(8 : Fin 16),9,10,11] → st'.val i = st.val i) 11 := by
  have hlen : coreLength s width k ≤ s-coreStart width k := min_le_right _ _
  have h := coreIntervalCode_do (A := A) (W := W) (w := w) st hs hw hk hstart (by omega)
  exact h.seq (K₂ := 5) (fun st₁ ⟨ha,_,hb,hacc,hframe⟩ =>
    (coreHaloPadCode_do (A := A) (W := W) (w := w) st₁
      ((hframe 0 (by simp)).trans hs) ((hframe 2 (by simp)).trans hr)
      ((hframe 12 (by simp)).trans hz) ha hb (by omega)).mono
      (fun st₂ ⟨ha₂,hb₂,hacc₂,hframe₂⟩ => ⟨ha₂,hb₂,hacc₂.trans hacc,by
        intro i hi
        have hi' : i ∉ [(8 : Fin 16),9,10] := by
          simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi ⊢
          exact ⟨hi.1,hi.2.1,hi.2.2.1⟩
        exact (hframe₂ i hi').trans (hframe i hi)⟩) le_rfl)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
