module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalPhaseCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLengthEndpointCode
public import IntegerMultBounds.NLogN.PhaseCellHaloLengthKeys

/-! Compute the two additional halo length candidates using the original
ambient phase at each cut. Empty clipped intervals emit zero. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def haloEndpointLengthCode : TblCode 16 :=
  naturalPhaseCode ;; (haloIntervalCode ;; .ins (.emit 11 12))

theorem haloEndpointLengthCode_do {A W w s t band a b x : ℕ} (st : TblSt 16 A)
    (hs' : st.val 0 = s) (hband : st.val 2 = band) (hden : st.val 6 = 2*(t-s))
    (hone : st.val 7 = 1) (hx : st.val 8 = x) (hz : st.val 12 = 0)
    (ha : st.val 13 = a) (hb : st.val 14 = b) (has : a ≤ s) (hbs : b ≤ s)
    (hs : 0 < s) (hst : s < t) (hxs : x ≤ 2*s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^W) :
    TblDo A W w haloEndpointLengthCode st (fun st' =>
      st'.acc = (tblPairs A w (haloLength s t band a b (naturalPhase s t x)) 0).reverse ++ st.acc ∧
      ∀ k, k ∉ [(4 : Fin 16),8,9,10,11] → st'.val k = st.val k) 35 := by
  have hp := naturalPhaseCode_do (A := A) (W := W) (w := w) st hs' hden hx hs hst hxs hwide
  apply hp.seq (K₂ := 31)
  intro st₁ ⟨hphase,hacc,hframe⟩
  have hi := haloIntervalWideCode_do (A := A) (W := W) (w := w) st₁
    ((hframe 0 (by simp)).trans hs') ((hframe 2 (by simp)).trans hband) hphase
    ((hframe 6 (by simp)).trans hden) ((hframe 7 (by simp)).trans hone)
    ((hframe 13 (by simp)).trans ha) ((hframe 14 (by simp)).trans hb) has hbs hs hst
    (naturalPhase_le_double_gap hs hxs) hwide
  apply hi.seq (K₂ := 1)
  intro st₂ ⟨_,_,hlen,hacc₂,hframe₂⟩
  exact (emitCurrentLength_do (W := W) (e := w) st₂ hlen
    ((hframe₂ 12 (by simp)).trans ((hframe 12 (by simp)).trans hz))).mono
    (fun st₃ ⟨hv,hout⟩ => by
      constructor
      · rw [hout,hacc₂,hacc]
      · intro k hk
        have h₁ : k ∉ [(4 : Fin 16),9] := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at *
          tauto
        have h₂ : k ∉ [(8 : Fin 16),9,10,11] := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at *
          tauto
        rw [hv]
        exact (hframe₂ k h₂).trans (hframe k h₁)) le_rfl

def haloEndpointLengthsCode : TblCode 16 :=
  .ins (.add 13 2 8) ;; (haloEndpointLengthCode ;;
    (tblNatSub 14 2 8 ;; (tblNatSub 8 7 8 ;; haloEndpointLengthCode)))

theorem haloEndpointLengthsCode_do {A W w s t band a b : ℕ} (st : TblSt 16 A)
    (hs' : st.val 0 = s) (hband : st.val 2 = band) (hden : st.val 6 = 2*(t-s))
    (hone : st.val 7 = 1) (hz : st.val 12 = 0) (ha : st.val 13 = a) (hb : st.val 14 = b)
    (has : a ≤ s) (hbs : b ≤ s) (hbandS : band ≤ s) (hs : 0 < s) (hst : s < t)
    (hwide : 8*(t+1)^2+2*band+8 < 2^W) :
    TblDo A W w haloEndpointLengthsCode st (fun st' =>
      st'.acc = (tblPairs A w (haloLength s t band a b (naturalPhase s t (a+band))) 0 ++
        tblPairs A w (haloLength s t band a b (naturalPhase s t (b-band-1))) 0).reverse ++ st.acc ∧
      ∀ k, k ∉ [(4 : Fin 16),8,9,10,11] → st'.val k = st.val k) 75 := by
  have hsW : 2*s < 2^W := by nlinarith only [hwide,hst]
  let S₁ : TblSt 16 A := ⟨Function.update st.val 8 (a+band), st.acc⟩
  have h₁ : TblDo A W w (.ins (.add 13 2 8)) st (fun st' => st' = S₁) 1 := by
    apply TblDo.insX
    · simp [TblIns.fits,ha,hband]; omega
    · simp [TblIns.exact,S₁,ha,hband]
  apply h₁.seq (K₂ := 74)
  intro st₁ he₁
  subst he₁
  have hl := haloEndpointLengthCode_do (A := A) (W := W) (w := w) (x := a+band) S₁
    (by simp [S₁,hs']) (by simp [S₁,hband]) (by simp [S₁,hden]) (by simp [S₁,hone])
    (by simp [S₁]) (by simp [S₁,hz]) (by simp [S₁,ha]) (by simp [S₁,hb]) has hbs hs hst (by omega) hwide
  apply hl.seq (K₂ := 39)
  intro st₂ ⟨hacc₂,hf₂⟩
  have hsub := tblNatSub_do (A := A) (W := W) (w := w) 14 2 8 st₂ (by
    rw [hf₂ 14 (by simp)]; simp [S₁,hb]; omega)
  apply hsub.seq (K₂ := 37)
  intro st₃ he₃
  subst he₃
  have hsub₁ := tblNatSub_do (A := A) (W := W) (w := w) 8 7 8
    (⟨Function.update st₂.val 8 (st₂.val 14-st₂.val 2), st₂.acc⟩ : TblSt 16 A) (by
      simp; rw [hf₂ 14 (by simp)]; simp [S₁,hb]; omega)
  apply hsub₁.seq (K₂ := 35)
  intro st₄ he₄
  subst he₄
  let S₄ : TblSt 16 A := ⟨Function.update st₂.val 8 (b-band-1), st₂.acc⟩
  have hright := haloEndpointLengthCode_do (A := A) (W := W) (w := w) (x := b-band-1) S₄
    (by simp [S₄,hf₂ 0 (by simp),S₁,hs'])
    (by simp [S₄,hf₂ 2 (by simp),S₁,hband])
    (by simp [S₄,hf₂ 6 (by simp),S₁,hden])
    (by simp [S₄,hf₂ 7 (by simp),S₁,hone]) (by simp [S₄])
    (by simp [S₄,hf₂ 12 (by simp),S₁,hz])
    (by simp [S₄,hf₂ 13 (by simp),S₁,ha])
    (by simp [S₄,hf₂ 14 (by simp),S₁,hb]) has hbs hs hst (by omega) hwide
  have hstate : (⟨Function.update (Function.update st₂.val 8 (st₂.val 14-st₂.val 2)) 8
      ((Function.update st₂.val 8 (st₂.val 14-st₂.val 2)) 8 -
       (Function.update st₂.val 8 (st₂.val 14-st₂.val 2)) 7), st₂.acc⟩ : TblSt 16 A) = S₄ := by
    simp [S₄,Function.update_idem,hf₂ 14 (by simp),hf₂ 2 (by simp),hf₂ 7 (by simp),S₁,hb,hband,hone]
  rw [hstate]
  exact hright.mono (fun st₅ ⟨hout,hf₅⟩ => by
    constructor
    · rw [hout]
      simp [S₄,hacc₂,S₁,List.reverse_append,List.append_assoc]
    · intro k hk
      have h8 : k ≠ (8 : Fin 16) := by intro he; apply hk; simp [he]
      rw [hf₅ k hk]
      simp [S₄,h8,hf₂ k hk,S₁]) le_rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
