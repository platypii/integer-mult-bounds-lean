module

public import IntegerMultBounds.MathlibTM2.Fast.TableNatSub
public import IntegerMultBounds.NLogN.PhaseCellRecoveryWindows

/-! Compute either pair of clipped recovery-window bounds once, in nine table atoms. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def recoveryWindowRadiusCode : TblCode 16 :=
  tblBlock 16 [.zero 6,.inc 6,.inc 6] (.div 2 6 7)

def recoveryWindowCode (ambient : Bool) : TblCode 16 :=
  recoveryWindowRadiusCode ;; (if ambient then tblNatMin 0 7 8 ;; tblNatSub 0 7 9
    else tblNatSub 13 7 8 ;; (.ins (.add 14 7 9) ;; tblNatMin 0 9 9))

def recoveryWindowState (ambient : Bool) (s B a b : ℕ) (st : TblSt 16 A) : TblSt 16 A :=
  ⟨Function.update (Function.update (Function.update (Function.update st.val 6 2) 7 (B/2)) 8
    (recoveryWindowLower ambient s B a)) 9 (recoveryWindowUpper ambient s B b),st.acc⟩

theorem recoveryWindowCode_do {A W w s B a b : ℕ} (ambient : Bool) (st : TblSt 16 A)
    (hs : st.val 0 = s) (hB : st.val 2 = B) (ha : st.val 13 = a) (hb : st.val 14 = b)
    (has : a ≤ s) (hbs : b ≤ s) (hwide : 2*s+2*B+8 < 2^W) :
    TblDo A W w (recoveryWindowCode ambient) st
      (fun st' => st' = recoveryWindowState ambient s B a b st) 9 := by
  let S₁ : TblSt 16 A := ⟨Function.update (Function.update st.val 6 2) 7 (B/2),st.acc⟩
  have htwo : 2 < 2^W := by omega
  have hW : W ≠ 0 := by intro he; rw [he] at htwo; norm_num at htwo
  have hr : TblDo A W w recoveryWindowRadiusCode st (fun st' => st' = S₁) 4 := by
    apply TblDo.block
    · simp [tblFitsList,TblIns.fits,TblIns.exact,hW]
      omega
    · simp [tblExactList,TblIns.exact,S₁,hB]
  apply hr.seq (K₂ := 5)
  intro st₁ he₁
  subst he₁
  cases ambient with
  | true =>
    have hm := tblNatMin_do (A := A) (W := W) (w := w) 0 7 8 S₁
    apply (hm.seq (K₂ := 2) (fun st₂ he₂ => by
      subst he₂
      exact (tblNatSub_do (A := A) (W := W) (w := w) 0 7 9 _ (by simp [S₁,hs]; omega)).mono
        (fun st₃ he₃ => by simpa [S₁,recoveryWindowState,recoveryWindowLower,recoveryWindowUpper,hs] using he₃)
        le_rfl)).mono (fun _ h => h) (by omega)
  | false =>
    have hsub := tblNatSub_do (A := A) (W := W) (w := w) 13 7 8 S₁ (by simp [S₁,ha]; omega)
    apply hsub.seq (K₂ := 3)
    intro st₂ he₂
    subst he₂
    let S₂ : TblSt 16 A := ⟨Function.update (Function.update S₁.val 8 (a-B/2)) 9 (b+B/2),st.acc⟩
    have hadd : TblDo A W w (.ins (.add 14 7 9))
        ⟨Function.update S₁.val 8 (S₁.val 13-S₁.val 7),S₁.acc⟩ (fun st' => st' = S₂) 1 := by
      apply TblDo.insX
      · simp [TblIns.fits,S₁,hb]
        have := Nat.div_le_self B 2
        omega
      · simp [TblIns.exact,S₂,S₁,ha,hb]
    apply hadd.seq (K₂ := 2)
    intro st₃ he₃
    subst he₃
    exact (tblNatMin_do (A := A) (W := W) (w := w) 0 9 9 S₂).mono (fun st₄ he₄ => by
      simpa [S₂,S₁,recoveryWindowState,recoveryWindowLower,recoveryWindowUpper,hs,Function.update_idem] using he₄) le_rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
