module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDirectCoefficient

/-! Generate pi and both scaling powers from numeric precision headers. Only
owned table workspace changes; geometry and coordinate inputs are retained. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.Resampling.WeightNat

def prepareDirectCoefficient : TblCode 48 :=
  tblPiSetup48 ;; (tblPow2 39 44 45 ;; (tblPow2 40 19 45 ;; tblBlock 48 [.zero 22] (.inc 22)))

theorem prepareDirectCoefficient_do {A V w P q : ℕ} (st : TblSt 48 A)
    (hP' : st.val 19 = P) (hq : st.val 44 = q) (hP : 13 ≤ P)
    (hV : 13*P+8 ≤ V) (hqV : q+P+2 ≤ V) :
    TblDo A V w prepareDirectCoefficient st (fun st' =>
      st'.val 18 = piN P ∧ st'.val 19 = P ∧ st'.val 22 = 1 ∧
      st'.val 39 = 2^q ∧ st'.val 40 = 2^P ∧ st'.acc = st.acc ∧
      ∀ r : Fin 48, 34 ≤ r.val → r ≠ 39 → r ≠ 40 → r ≠ 45 → st'.val r = st.val r)
      (154*P+4*q+413) := by
  have hpi := tbl_pi48_do (W := V) (w := w) st hP' (by omega) (by omega)
  have hcore : TblDo A V w prepareDirectCoefficient st (fun st' =>
      st'.val 18 = piN P ∧ st'.val 19 = P ∧ st'.val 22 = 1 ∧
      st'.val 39 = 2^q ∧ st'.val 40 = 2^P ∧ st'.acc = st.acc ∧
      ∀ r : Fin 48, 34 ≤ r.val → r ≠ 39 → r ≠ 40 → r ≠ 45 → st'.val r = st.val r)
      ((1+(150*P+400))+((4*q+5)+((4*P+5)+2))) := by
    unfold prepareDirectCoefficient
    refine hpi.seq (K₂ := (4*q+5)+((4*P+5)+2)) (fun s₁ h₁ => ?_)
    have hq₁ : s₁.val 44 = q := (h₁.2.2 44 (by decide)).trans hq
    have hp₁ : s₁.val 19 = P := (h₁.2.2 19 (by decide)).trans hP'
    have hpowq := tblPow2_do (A := A) (W := V) (w := w)
      (c := 39) (e := 44) (i := 45) (by decide) (by decide) (by decide) s₁ (by rw [hq₁]; omega)
    rw [hq₁] at hpowq
    refine hpowq.seq (K₂ := (4*P+5)+2) (fun s₂ h₂ => ?_)
    have hp₂ : s₂.val 19 = P := (h₂.2.2.1 19 (by decide) (by decide)).trans hp₁
    have hpowp := tblPow2_do (A := A) (W := V) (w := w)
      (c := 40) (e := 19) (i := 45) (by decide) (by decide) (by decide) s₂ (by rw [hp₂]; omega)
    rw [hp₂] at hpowp
    refine hpowp.seq (K₂ := 2) (fun s₃ h₃ => ?_)
    apply TblDo.block
    · simp [tblFitsList,TblIns.fits,TblIns.exact]
      omega
    · simp only [List.cons_append,List.nil_append,tblExactList,TblIns.exact]
      refine ⟨?_,?_,by simp,?_,?_,?_,?_⟩
      · simpa using (h₃.2.2.1 18 (by decide) (by decide)).trans
          ((h₂.2.2.1 18 (by decide) (by decide)).trans h₁.1)
      · simpa using (h₃.2.2.1 19 (by decide) (by decide)).trans hp₂
      · simpa using (h₃.2.2.1 39 (by decide) (by decide)).trans h₂.1
      · simpa using h₃.1
      · exact h₃.2.2.2.trans (h₂.2.2.2.trans h₁.2.1)
      · intro r hr hr39 hr40 hr45
        have hr22 : r ≠ 22 := by intro he; subst r; norm_num at hr
        simp only [Function.update_of_ne hr22]
        exact (h₃.2.2.1 r hr40 hr45).trans ((h₂.2.2.1 r hr39 hr45).trans (h₁.2.2 r (by omega)))
  exact hcore.mono (fun _ h => h) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
