module

public import IntegerMultBounds.MathlibTM2.Fast.TableNatSub
public import IntegerMultBounds.NLogN.PhaseCellNaturalInterval

/-! Compute one natural phase threshold in a bounded binary table. The
truncated subtraction handles phase zero without a special numerical oracle. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM

/-- Inputs: modulus on 0, doubled gap on 6, one on 7 and numerator on 8. -/
def naturalLowerCode (dst : Fin 16) : TblCode 16 :=
  tblBlock 16 [.add 8 6 dst] (.sub dst 7 dst) ;;
    (tblNatSub dst 0 dst ;; .ins (.div dst 6 dst))

theorem naturalLowerCode_do {A W w s d x : ℕ} (dst : Fin 16)
    (hreg : [(0 : Fin 16), 6, 7, 8, dst].Nodup) (st : TblSt 16 A)
    (hs : st.val 0 = s) (hd : st.val 6 = 2*d) (hone : st.val 7 = 1) (hx : st.val 8 = x)
    (hdpos : 0 < d) (hfit : x+2*d < 2^W) :
    TblDo A W w (naturalLowerCode dst) st
      (fun st' => st' = ⟨Function.update st.val dst ((x+2*d-1-s)/(2*d)), st.acc⟩) 5 := by
  have hr := hreg
  regs_ne hr
  let S₁ : TblSt 16 A := ⟨Function.update st.val dst (x+2*d-1), st.acc⟩
  have h₁ : TblDo A W w (tblBlock 16 [.add 8 6 dst] (.sub dst 7 dst)) st (fun st' => st' = S₁) 2 := by
    apply TblDo.block
    · simp [tblFitsList, TblIns.fits, TblIns.exact, hd, hone, hx, hfit,
        show (7 : Fin 16) ≠ dst from ‹(7 : Fin 16) ≠ dst›]
      omega
    · simp [tblExactList, TblIns.exact, S₁, hd, hone, hx, Function.update_idem,
        show (7 : Fin 16) ≠ dst from ‹(7 : Fin 16) ≠ dst›]
  have h₂ := tblNatSub_do (A := A) (W := W) (w := w) dst 0 dst S₁ (by simp [S₁]; omega)
  have hcore : TblDo A W w (naturalLowerCode dst) st
      (fun st' => st' = ⟨Function.update st.val dst ((x+2*d-1-s)/(2*d)), st.acc⟩) (2+(2+1)) := by
    unfold naturalLowerCode
    refine h₁.seq (fun st' he => he ▸ h₂.seq (fun st'' he' => ?_))
    subst he'
    apply TblDo.insX (.div dst 6 dst) (by trivial)
    simp [S₁, TblIns.exact, hs, hd, Function.update_idem,
      show (0 : Fin 16) ≠ dst from ‹(0 : Fin 16) ≠ dst›,
      show (6 : Fin 16) ≠ dst from ‹(6 : Fin 16) ≠ dst›]
  exact hcore

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
