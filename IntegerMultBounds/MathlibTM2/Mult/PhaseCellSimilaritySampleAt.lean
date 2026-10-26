module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSimilarityArgumentAt
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightNumerators
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientExp

/-! Sample either retained coordinate while preserving the other sample and
both arithmetic-grid powers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Resampling IntegerMultBounds.Resampling.WeightNat
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

def similaritySampleAt (target : Bool) : TblCode 48 :=
  similarityArgumentAt target ;;
    (correctedExpCode.rename tblExpMap48 ;; .ins (.copy 23 (if target then 42 else 41)))

theorem similaritySampleAt_do {A V w P s t u j : ℕ} (target : Bool) (st : TblSt 48 A)
    (hpi : st.val 18 = piN P) (hP' : st.val 19 = P) (hneg : st.val 22 = 1)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hu : st.val 36 = u)
    (hj : st.val (if target then 38 else 37) = j)
    (hdouble : st.val 47 = 2*s) (hden : st.val 44 = similarityDenominator s t)
    (hP : 13 ≤ P) (hs0 : 0 < s) (hst : s < t)
    (hindex : 2*t*j+s < 2^V) (hsV : 2*s < 2^V)
    (hsq : s^2 < 2^V) (huV : u*s^2 < 2^V)
    (hV : 13*P+8 ≤ V)
    (haV : similarityNumerator s t u j * 2^(5*P+2) < 2^V) :
    TblDo A V w (similaritySampleAt target) st (fun st' =>
      st'.val (if target then 42 else 41) = similarityGridNumerator P s t u j ∧
      st'.acc = st.acc ∧
      st'.val 18 = st.val 18 ∧ st'.val 19 = st.val 19 ∧ st'.val 22 = st.val 22 ∧
      ∀ r : Fin 48, 34 ≤ r.val → r ≠ 45 → r ≠ 46 →
        r ≠ (if target then 42 else 41) → st'.val r = st.val r)
      (310*P+115) := by
  have hargs := similarityArgumentAt_do (w := w) target st hs ht hu hj hdouble hden hs0
    hindex hsV hsq huV
  have hcore : TblDo A V w (similaritySampleAt target) st (fun st' =>
      st'.val (if target then 42 else 41) = similarityGridNumerator P s t u j ∧
      st'.acc = st.acc ∧
      st'.val 18 = st.val 18 ∧ st'.val 19 = st.val 19 ∧ st'.val 22 = st.val 22 ∧
      ∀ r : Fin 48, 34 ≤ r.val → r ≠ 45 → r ≠ 46 →
        r ≠ (if target then 42 else 41) → st'.val r = st.val r)
      (8+((310*P+106)+1)) := by
    unfold similaritySampleAt
    refine hargs.seq (K₂ := (310*P+106)+1) (fun s₁ h₁ => ?_)
    have hpre (r : Fin 48) (hr : r ∉ [(20 : Fin 48),21,45,46]) := h₁.2.2.2 r hr
    have hexp := (correctedExpCode_do (A := A) (V := V) (w := w)
      (s₁.restrict tblExpMap48)
      (by simpa [TblSt.restrict,tblExpMap48,hpre 18 (by simp)] using hpi)
      (by simpa [TblSt.restrict,tblExpMap48,hpre 19 (by simp)] using hP')
      (by simpa [TblSt.restrict,tblExpMap48] using h₁.1)
      (by simpa [TblSt.restrict,tblExpMap48] using h₁.2.1)
      (by simpa [TblSt.restrict,tblExpMap48,hpre 22 (by simp)] using hneg)
      hP (similarityDenominator_pos hs0 hst) hV haV).rename
        (show Function.Injective tblExpMap48 by
          intro i j h
          exact Fin.ext (congrArg (fun x : Fin 48 => x.val) h))
    refine hexp.seq (K₂ := 1) (fun s₂ h₂ => ?_)
    have hoff (r : Fin 48) (hr : 34 ≤ r.val) : s₂.val r = s₁.val r :=
      h₂.2 r (tbl_castLE_ne (by decide) r hr)
    have hcopy : TblDo A V w (.ins (.copy 23 (if target then 42 else 41))) s₂
        (fun s₃ => s₃.val (if target then 42 else 41) = s₂.val 23 ∧
          s₃.acc = s₂.acc ∧ ∀ r, r ≠ (if target then 42 else 41) → s₃.val r = s₂.val r) 1 := by
      apply TblDo.insX (.copy 23 (if target then 42 else 41))
      · simp [TblIns.fits]
      · simp [TblIns.exact]
        intro r hr
        simp [hr]
    refine hcopy.mono (fun s₃ h₃ => ?_) le_rfl
    have hne (r : Fin 48) (hr : r.val < 34) : r ≠ (if target then 42 else 41) := by
      cases target <;> norm_num <;> intro h <;> subst r <;> norm_num at hr
    refine ⟨?_,h₃.2.1.trans (h₂.1.2.2.1.trans h₁.2.2.1),?_,?_,?_,?_⟩
    · simpa [similarityGridNumerator,TblSt.restrict,tblExpMap48] using h₃.1.trans h₂.1.1
    · exact (h₃.2.2 18 (hne 18 (by decide))).trans
        (h₂.1.2.2.2.1.trans (hpre 18 (by simp)))
    · exact (h₃.2.2 19 (hne 19 (by decide))).trans
        (h₂.1.2.2.2.2.1.trans (hpre 19 (by simp)))
    · exact (h₃.2.2 22 (hne 22 (by decide))).trans
        (h₂.1.2.2.2.2.2.2.trans (hpre 22 (by simp)))
    · intro r hr hr45 hr46 hrdst
      rw [h₃.2.2 r hrdst,hoff r hr,hpre r]
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨by intro h; subst r; norm_num at hr,
        by intro h; subst r; norm_num at hr,hr45,hr46⟩
  exact hcore.mono (fun _ h => h) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
