module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloClipCode
public import IntegerMultBounds.NLogN.PhaseCellCoreWindows

/-! # Executed core geometry

Six table atoms compute the owned core from s, width and its index. The layout
matches existing origin/length emitters, so the descriptor controller can reuse
their loops and framing proofs. All arithmetic is checked at the supplied width.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellMatrix

def coreIntervalCode : TblCode 16 :=
  .ins (.mul 4 1 9) ;; (tblNatSub 0 9 8 ;;
    (tblNatMin 1 8 11 ;; .ins (.add 9 11 10)))

theorem coreIntervalCode_do {A W w s width k : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (hwidth : st.val 1 = width) (hk : st.val 4 = k)
    (hstart : coreStart width k ≤ s) (hwide : s < 2^W) :
    TblDo A W w coreIntervalCode st (fun st' =>
      st'.val 9 = coreStart width k ∧ st'.val 11 = coreLength s width k ∧
      st'.val 10 = coreStart width k+coreLength s width k ∧ st'.acc = st.acc ∧
      ∀ i, i ∉ [(8 : Fin 16),9,10,11] → st'.val i = st.val i) 6 := by
  let S₁ : TblSt 16 A := ⟨Function.update st.val 9 (coreStart width k),st.acc⟩
  have h₁ : TblDo A W w (.ins (.mul 4 1 9)) st (fun st' => st' = S₁) 1 := by
    apply TblDo.insX
    · simpa [TblIns.fits,hk,hwidth,coreStart] using hstart.trans_lt hwide
    · simp [TblIns.exact,S₁,hk,hwidth,coreStart]
  let S₂ : TblSt 16 A := ⟨Function.update S₁.val 8 (s-coreStart width k),st.acc⟩
  have h₂ : TblDo A W w (tblNatSub 0 9 8) S₁ (fun st' => st' = S₂) 2 := by
    simpa [S₂,S₁,hs] using tblNatSub_do (A := A) (W := W) (w := w) 0 9 8 S₁
      (by simpa [S₁,hs] using hwide)
  let S₃ : TblSt 16 A := ⟨Function.update S₂.val 11 (coreLength s width k),st.acc⟩
  have h₃ : TblDo A W w (tblNatMin 1 8 11) S₂ (fun st' => st' = S₃) 2 := by
    simpa [S₃,S₂,S₁,hwidth,coreLength] using tblNatMin_do (A := A) (W := W) (w := w) 1 8 11 S₂
  have hstop : coreStart width k+coreLength s width k ≤ s := by
    have hlen : coreLength s width k ≤ s-coreStart width k := min_le_right _ _
    omega
  let S₄ : TblSt 16 A := ⟨Function.update S₃.val 10
    (coreStart width k+coreLength s width k),st.acc⟩
  have h₄ : TblDo A W w (.ins (.add 9 11 10)) S₃ (fun st' => st' = S₄) 1 := by
    apply TblDo.insX
    · simpa [TblIns.fits,S₃,S₂,S₁] using hstop.trans_lt hwide
    · simp [TblIns.exact,S₄,S₃,S₂,S₁]
  have h := h₁.seq (fun st₁ he₁ => he₁ ▸ h₂.seq
    (fun st₂ he₂ => he₂ ▸ h₃.seq (fun st₃ he₃ => he₃ ▸ h₄)))
  refine h.mono (fun st' he => he ▸ ?_) (by decide)
  refine ⟨by simp [S₄,S₃,S₂,S₁],by simp [S₄,S₃],by simp [S₄],rfl,?_⟩
  intro i hi
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
  simp [S₄,S₃,S₂,S₁,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
