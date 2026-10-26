module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalIntervalCode
public import IntegerMultBounds.NLogN.PhaseCellHaloInterval

/-! Nine checked table atoms clip an ambient interval at the artificial halo
endpoints. All geometry/header sources and the accumulator are retained. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def haloNatMax {n : ℕ} (a b c : Fin n) : TblCode n :=
  .ite a b (.ins (.copy b c)) (.ins (.copy a c))

theorem haloNatMax_do {n A W w : ℕ} (a b c : Fin n) (st : TblSt n A) :
    TblDo A W w (haloNatMax a b c) st
      (fun st' => st' = ⟨Function.update st.val c (max (st.val a) (st.val b)),st.acc⟩) 2 := by
  by_cases hab : st.val a < st.val b
  · apply TblDo.iteT hab
    exact TblDo.insX (.copy b c) (by trivial) (by simp [TblIns.exact,max_eq_right hab.le])
  · apply TblDo.iteF hab
    exact TblDo.insX (.copy a c) (by trivial) (by simp [TblIns.exact,max_eq_left (Nat.le_of_not_gt hab)])

def haloClipCode : TblCode 16 :=
  .ins (.add 13 2 8) ;; (haloNatMax 9 8 9 ;;
    (tblNatSub 14 2 8 ;; (tblNatMin 10 8 10 ;; tblNatSub 10 9 11)))

theorem haloClipCode_do {A W w s t band a b phase : ℕ} (st : TblSt 16 A)
    (hband : st.val 2 = band) (ha : st.val 13 = a) (hb : st.val 14 = b)
    (hstart : st.val 9 = naturalStart s t band phase) (hstop : st.val 10 = naturalStop s t band phase)
    (haW : a+band < 2^W) (hbW : b < 2^W) (hsW : s < 2^W) :
    TblDo A W w haloClipCode st (fun st' =>
      st'.val 9 = haloStart s t band a phase ∧ st'.val 10 = haloStop s t band b phase ∧
      st'.val 11 = haloLength s t band a b phase ∧ st'.acc = st.acc ∧
      ∀ k, k ∉ [(8 : Fin 16),9,10,11] → st'.val k = st.val k) 9 := by
  let S₁ : TblSt 16 A := ⟨Function.update st.val 8 (a+band),st.acc⟩
  have h₁ : TblDo A W w (.ins (.add 13 2 8)) st (fun st' => st' = S₁) 1 := by
    apply TblDo.insX
    · simpa [TblIns.fits,ha,hband] using haW
    · simp [TblIns.exact,S₁,ha,hband]
  let S₂ : TblSt 16 A := ⟨Function.update S₁.val 9 (haloStart s t band a phase),st.acc⟩
  have h₂ : TblDo A W w (haloNatMax 9 8 9) S₁ (fun st' => st' = S₂) 2 := by
    simpa [S₂,S₁,hstart,haloStart] using haloNatMax_do (A := A) (W := W) (w := w) 9 8 9 S₁
  let S₃ : TblSt 16 A := ⟨Function.update S₂.val 8 (b-band),st.acc⟩
  have h₃ : TblDo A W w (tblNatSub 14 2 8) S₂ (fun st' => st' = S₃) 2 := by
    simpa [S₃,S₂,S₁,hb,hband,Function.update_idem] using
      tblNatSub_do (A := A) (W := W) (w := w) 14 2 8 S₂ (by simpa [S₂,S₁,hb] using hbW)
  let S₄ : TblSt 16 A := ⟨Function.update S₃.val 10 (haloStop s t band b phase),st.acc⟩
  have h₄ : TblDo A W w (tblNatMin 10 8 10) S₃ (fun st' => st' = S₄) 2 := by
    simpa [S₄,S₃,S₂,S₁,hstop,haloStop] using tblNatMin_do (A := A) (W := W) (w := w) 10 8 10 S₃
  let S₅ : TblSt 16 A := ⟨Function.update S₄.val 11 (haloLength s t band a b phase),st.acc⟩
  have h₅ : TblDo A W w (tblNatSub 10 9 11) S₄ (fun st' => st' = S₅) 2 := by
    simpa [S₅,S₄,S₃,S₂,haloLength] using tblNatSub_do (A := A) (W := W) (w := w) 10 9 11 S₄
      (by simpa [S₄] using (haloStop_le s t band b phase).trans_lt hsW)
  have hc := h₁.seq (fun st' he => he ▸ h₂.seq (fun st'' he' => he' ▸ h₃.seq
    (fun st₃ he₃ => he₃ ▸ h₄.seq (fun st₄ he₄ => he₄ ▸ h₅))))
  refine hc.mono (fun st' he => he ▸ ?_) (by decide)
  refine ⟨by simp [S₅,S₄,S₃,S₂],by simp [S₅,S₄],by simp [S₅],rfl,?_⟩
  intro k hk
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hk
  simp [S₅,S₄,S₃,S₂,S₁,hk.1,hk.2.1,hk.2.2.1,hk.2.2.2]

def haloIntervalCode : TblCode 16 := naturalIntervalCode ;; haloClipCode

theorem haloIntervalCode_do {A W w s t band a b phase : ℕ} (st : TblSt 16 A)
    (hs' : st.val 0 = s) (hband : st.val 2 = band) (hphase : st.val 4 = phase)
    (hden : st.val 6 = 2*(t-s)) (hone : st.val 7 = 1)
    (ha : st.val 13 = a) (hb : st.val 14 = b) (has : a ≤ s) (hbs : b ≤ s)
    (hs : 0 < s) (hst : s < t) (hphaseMax : phase ≤ t-s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^W) :
    TblDo A W w haloIntervalCode st (fun st' =>
      st'.val 9 = haloStart s t band a phase ∧ st'.val 10 = haloStop s t band b phase ∧
      st'.val 11 = haloLength s t band a b phase ∧ st'.acc = st.acc ∧
      ∀ k, k ∉ [(8 : Fin 16),9,10,11] → st'.val k = st.val k) 30 := by
  have haW : a+band < 2^W := by nlinarith only [hwide,has,hst]
  have hsW : s < 2^W := by nlinarith only [hwide,hst]
  have hi := naturalIntervalCode_do (A := A) (W := W) (w := w) st hs' hband hphase hden hone hs hst hphaseMax hwide
  exact hi.seq (K₂ := 9) (fun st₁ ⟨hstart,hstop,_,hacc,hframe⟩ =>
    (haloClipCode_do (A := A) (W := W) (w := w) st₁
      ((hframe 2 (by simp)).trans hband) ((hframe 13 (by simp)).trans ha)
      ((hframe 14 (by simp)).trans hb) hstart hstop haW (hbs.trans_lt hsW) hsW).mono
        (fun st₂ ⟨hstart₂,hstop₂,hlen₂,hacc₂,hframe₂⟩ =>
          ⟨hstart₂,hstop₂,hlen₂,hacc₂.trans hacc,fun k hk => (hframe₂ k hk).trans (hframe k hk)⟩) le_rfl)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
