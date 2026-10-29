module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalGroupCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreIntervalCode

/-! # Emission for fitting core halos

Reuse the existing length-selective emitter after padding the core length and
subtracting the guard from its origin. Setup keys are unaffected: this is only
an exposure schedule.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM

def coreGatherEmit : TblCode 16 :=
  tblBlock 16 [.add 11 2 11,.add 11 2 11] (.sub 9 2 9) ;; naturalOriginEmit

theorem coreGatherEmit_do {A W w origin len radius L : ℕ} (st : TblSt 16 A)
    (ho : st.val 9 = origin) (hl : st.val 11 = len) (hr : st.val 2 = radius)
    (hL : st.val 3 = L) (hz : st.val 12 = 0) (hleft : radius ≤ origin)
    (hoW : origin < 2^W) (hlW : len+2*radius < 2^W) :
    TblDo A W w coreGatherEmit st (fun st' =>
      st'.acc = (if len+2*radius = L then tblPairs A w (origin-radius) 0 else []).reverse++st.acc ∧
      ∀ i, i ∉ [(9 : Fin 16),11] → st'.val i = st.val i) 6 := by
  let S₁ : TblSt 16 A := ⟨Function.update (Function.update st.val 11 (len+2*radius))
    9 (origin-radius),st.acc⟩
  have h₁ : TblDo A W w (tblBlock 16 [.add 11 2 11,.add 11 2 11] (.sub 9 2 9)) st
      (fun st' => st' = S₁) 3 := by
    apply TblDo.block
    · simp [tblFitsList,TblIns.fits,TblIns.exact,ho,hl,hr,hleft,hoW]
      omega
    · simp [tblExactList,TblIns.exact,S₁,ho,hl,hr,Function.update_idem,Nat.two_mul,Nat.add_assoc]
  have h₂ := naturalOriginEmit_do (A := A) (W := W) (w := w) (len := len+2*radius) (origin := origin-radius) (L := L) S₁
    (by simpa [S₁] using hL) (by simp [S₁]) (by simp [S₁]) (by simpa [S₁] using hz)
  have h : TblDo A W w coreGatherEmit st (fun st' => st'.val = S₁.val ∧
      st'.acc = (if len+2*radius = L then tblPairs A w (origin-radius) 0 else []).reverse++st.acc) 6 := by
    unfold coreGatherEmit
    exact h₁.seq (K₂ := 3) (fun st₁ he => by subst st₁; exact h₂)
  exact h.mono (fun st' ⟨hv,ha⟩ => ⟨ha,by
    intro i hi
    rw [hv]
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
    simp [S₁,hi.1,hi.2]⟩) le_rfl

def coreGatherChoose : TblCode 16 :=
  .ite 9 2 (.ins (.copy 12 12))
    (.ite 0 8 (.ins (.copy 12 12)) coreGatherEmit)

theorem coreGatherChoose_do {A W w s origin len radius L : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (ho : st.val 9 = origin) (hl : st.val 11 = len)
    (hr : st.val 2 = radius) (hL : st.val 3 = L) (hz : st.val 12 = 0)
    (hb : st.val 8 = origin+len+radius)
    (hoW : origin < 2^W) (hlW : len+2*radius < 2^W) :
    TblDo A W w coreGatherChoose st (fun st' =>
      st'.acc = (if radius ≤ origin ∧ origin+len+radius ≤ s ∧ len+2*radius = L
        then tblPairs A w (origin-radius) 0 else []).reverse++st.acc ∧
      ∀ i, i ∉ [(9 : Fin 16),11] → st'.val i = st.val i) 8 := by
  have hskip : TblDo A W w (.ins (.copy 12 12)) st (fun st' => st' = st) 1 :=
    TblDo.ins (.copy 12 12) (by simp [TblIns.run])
  by_cases hleft : origin < radius
  · apply TblDo.iteT (by simpa [ho,hr] using hleft)
    exact hskip.mono (fun st' he => he ▸ by simp [show ¬radius ≤ origin by omega]) (by decide)
  · apply TblDo.iteF (by simpa [ho,hr] using hleft)
    by_cases hright : s < origin+len+radius
    · apply TblDo.iteT (by simpa [hs,hb] using hright)
      exact hskip.mono (fun st' he => he ▸ by simp [show ¬origin+len+radius ≤ s by omega]) (by decide)
    · apply TblDo.iteF (by simpa [hs,hb] using hright)
      exact (coreGatherEmit_do st ho hl hr hL hz (by omega) hoW hlW).mono
        (fun st' he => by simpa [show radius ≤ origin by omega,
          show origin+len+radius ≤ s by omega] using he) le_rfl

open IntegerMultBounds.NLogN.PhaseCellMatrix

def coreGatherRowCode : TblCode 16 :=
  coreIntervalCode ;; (.ins (.add 10 2 8) ;; coreGatherChoose)

theorem coreGatherRowCode_do {A W w s width k radius L : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (hw : st.val 1 = width) (hk : st.val 4 = k)
    (hr : st.val 2 = radius) (hL : st.val 3 = L) (hz : st.val 12 = 0)
    (hstart : coreStart width k ≤ s) (hwide : s+2*radius < 2^W) :
    TblDo A W w coreGatherRowCode st (fun st' =>
      st'.acc = (if radius ≤ coreStart width k ∧
        coreStart width k+coreLength s width k+radius ≤ s ∧ coreLength s width k+2*radius = L
        then tblPairs A w (coreStart width k-radius) 0 else []).reverse++st.acc ∧
      ∀ i, i ∉ [(8 : Fin 16),9,10,11] → st'.val i = st.val i) 15 := by
  have hlen : coreLength s width k ≤ s-coreStart width k := min_le_right _ _
  have hi := coreIntervalCode_do (A := A) (W := W) (w := w) st hs hw hk hstart (by omega)
  apply hi.seq (K₂ := 9)
  intro st₁ ⟨ha,hl,hb,hacc,hframe⟩
  let S₂ : TblSt 16 A := ⟨Function.update st₁.val 8
    (coreStart width k+coreLength s width k+radius),st₁.acc⟩
  have hadd : TblDo A W w (.ins (.add 10 2 8)) st₁ (fun st' => st' = S₂) 1 := by
    apply TblDo.insX
    · have hr₁ := (hframe 2 (by simp)).trans hr
      simp only [TblIns.fits,hb,hr₁]
      omega
    · simp [TblIns.exact,S₂,hb,(hframe 2 (by simp)).trans hr]
  apply hadd.seq (K₂ := 8)
  intro st₂ he
  subst st₂
  have hc := coreGatherChoose_do (A := A) (W := W) (w := w) S₂
    (by simpa [S₂] using (hframe 0 (by simp)).trans hs)
    (by simpa [S₂] using ha) (by simpa [S₂] using hl)
    (by simpa [S₂] using (hframe 2 (by simp)).trans hr)
    (by simpa [S₂] using (hframe 3 (by simp)).trans hL)
    (by simpa [S₂] using (hframe 12 (by simp)).trans hz)
    (by simp [S₂]) (by omega) (by omega)
  exact hc.mono (fun st₃ ⟨hout,hf⟩ => ⟨by simpa [S₂,hacc] using hout,by
    intro i hi
    have hrest : i ∉ [(9 : Fin 16),11] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi ⊢
      exact ⟨hi.2.1,hi.2.2.2⟩
    rw [hf i hrest]
    have h8 : i ≠ (8 : Fin 16) := by intro he; apply hi; simp [he]
    simpa [S₂,h8] using hframe i hi⟩) le_rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
