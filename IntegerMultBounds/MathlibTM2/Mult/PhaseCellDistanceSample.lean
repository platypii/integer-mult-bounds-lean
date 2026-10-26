module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDistanceArgument
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWithinCoefficientWord
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientExp

/-! Execute the distance sample, retaining both similarity numerators. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Resampling.WeightNat
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

def distanceSample : TblCode 48 := distanceArgument ;; correctedExpCode.rename tblExpMap48

theorem distanceSample_do {A V w P s t u j k : ℕ} (st : TblSt 48 A)
    (hpi : st.val 18 = piN P) (hP' : st.val 19 = P) (hneg : st.val 22 = 1)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hu : st.val 36 = u)
    (hj : st.val 37 = j) (hk : st.val 38 = k)
    (hP : 13 ≤ P) (hs0 : 0 < s) (hV : 13*P+8 ≤ V)
    (hjV : j < 2^V) (hkV : k < 2^V)
    (hdV : naturalDistance j k^2 < 2^V) (htV : t*naturalDistance j k^2 < 2^V)
    (huV : u*(t*naturalDistance j k^2) < 2^V)
    (haV : (u*t*naturalDistance j k^2)*2^(5*P+2) < 2^V) :
    TblDo A V w distanceSample st (fun st' =>
      st'.val 23 = distanceGridNumerator P s t u (naturalDistance j k) ∧
      st'.val 25 = 0 ∧ st'.acc = st.acc ∧
      st'.val 18 = st.val 18 ∧ st'.val 19 = st.val 19 ∧ st'.val 22 = st.val 22 ∧
      ∀ r : Fin 48, 34 ≤ r.val → r ≠ 45 → st'.val r = st.val r) (310*P+112) := by
  have hargs := distanceArgument_do (w := w) st hs ht hu hj hk hjV hkV hdV htV huV
  have hcore : TblDo A V w distanceSample st (fun st' =>
      st'.val 23 = distanceGridNumerator P s t u (naturalDistance j k) ∧
      st'.val 25 = 0 ∧ st'.acc = st.acc ∧
      st'.val 18 = st.val 18 ∧ st'.val 19 = st.val 19 ∧ st'.val 22 = st.val 22 ∧
      ∀ r : Fin 48, 34 ≤ r.val → r ≠ 45 → st'.val r = st.val r) (6+(310*P+106)) := by
    unfold distanceSample
    refine hargs.seq (fun s₁ h₁ => ?_)
    have hpre (r : Fin 48) (hr : r ∉ [(20 : Fin 48),21,45]) := h₁.2.2.2 r hr
    have hexp := (correctedExpCode_do (A := A) (V := V) (w := w)
      (s₁.restrict tblExpMap48)
      (by simpa [TblSt.restrict,tblExpMap48,hpre 18 (by simp)] using hpi)
      (by simpa [TblSt.restrict,tblExpMap48,hpre 19 (by simp)] using hP')
      (by simpa [TblSt.restrict,tblExpMap48] using h₁.1)
      (by simpa [TblSt.restrict,tblExpMap48] using h₁.2.1)
      (by simpa [TblSt.restrict,tblExpMap48,hpre 22 (by simp)] using hneg)
      hP hs0 hV haV).rename
      (show Function.Injective tblExpMap48 by
        intro i j h
        exact Fin.ext (congrArg (fun x : Fin 48 => x.val) h))
    refine hexp.mono (fun s₂ h₂ => ?_) le_rfl
    refine ⟨?_,?_,h₂.1.2.2.1.trans h₁.2.2.1,?_,?_,?_,?_⟩
    · simpa [distanceGridNumerator,TblSt.restrict,tblExpMap48] using h₂.1.1
    · simpa [TblSt.restrict,tblExpMap48] using h₂.1.2.1
    · exact h₂.1.2.2.2.1.trans (hpre 18 (by simp))
    · exact h₂.1.2.2.2.2.1.trans (hpre 19 (by simp))
    · exact h₂.1.2.2.2.2.2.2.trans (hpre 22 (by simp))
    · intro r hr hr45
      rw [h₂.2 r (tbl_castLE_ne (by decide) r hr),hpre r]
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨by intro h; subst r; norm_num at hr,
        by intro h; subst r; norm_num at hr,hr45⟩
  exact hcore.mono (fun _ h => h) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
