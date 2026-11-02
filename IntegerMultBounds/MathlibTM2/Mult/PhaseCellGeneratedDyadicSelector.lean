module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicSelectorLoop

/-! Initialize and execute one row query from retained exponents, packet seed,
stage count and row index. All live selector controls are computed here. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM

def generatedDyadicSelectorCode : TblCode 16 :=
  .seq (tblBlock 16 [.copy 6 0,.copy 7 1,.copy 3 5,.copy 15 8,.copy 4 9,.zero 2,.zero 14] (.inc 14))
    dyadicSelectorLoopCode

def generatedDyadicSelectorWrites : List (Fin 16) := [0,1,2,5,8,9,10,11,12,13,14]

theorem generatedDyadicSelectorCode_do {A W w a b C i : ℕ} (st : TblSt 16 A)
    (ha : st.val 6 = a) (hb : st.val 7 = b) (hC : st.val 4 = C)
    (hn : st.val 3 = dyadicStageCount (a+b) a b) (hi : st.val 15 = i)
    (hbits : a+b < W) (hfit : C*2^(a+b) < 2^W) (hindex : i < dyadicStageCount (a+b) a b) :
    let row := selectDyadicStage (a+b) a b C (dyadicStageCount (a+b) a b) i
    TblDo A W w generatedDyadicSelectorCode st (fun F =>
      F.val 11 = row.outerCount ∧ F.val 9 = row.blockWidth ∧ F.val 10 = row.fieldBits ∧ F.val 5 = 0 ∧
      F.val 2 = 0 ∧ F.val 14 = 1 ∧ F.acc = st.acc ∧
      ∀ j, j ∉ generatedDyadicSelectorWrites → F.val j = st.val j)
      ((a+b)*(4*(a+b)+19)+10) := by
  let M : TblSt 16 A := ⟨Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update st.val 0 a) 1 b) 5 (dyadicStageCount (a+b) a b))
      8 i) 9 C) 2 0) 14 1,st.acc⟩
  have hinit : TblDo A W w
      (tblBlock 16 [.copy 6 0,.copy 7 1,.copy 3 5,.copy 15 8,.copy 4 9,.zero 2,.zero 14] (.inc 14)) st
      (fun F => F = M) 8 := by
    apply TblDo.block
    · simp [tblFitsList,TblIns.fits,TblIns.exact]
      omega
    · simp [tblExactList,TblIns.exact,M,ha,hb,hC,hn,hi]
  unfold generatedDyadicSelectorCode
  apply (hinit.seq (K₂ := (a+b)*(4*(a+b)+19)+2) ?_).mono (fun _ h => h) (by omega)
  intro st₁ he
  subst st₁
  have hloop := dyadicSelectorLoopCode_do (W := W) (w := w) (a+b) hbits (a+b) a b C i
    (by omega) (by omega) M
    (by simp [M]) (by simp [M]) (by simp [M]) (by simp [M]) (by simp [M])
    (by simp [M]) (by simp [M]) hfit hindex
  exact hloop.mono (fun F hF => by
    rcases hF with ⟨h11,h9,h10,h5,hacc,hframe⟩
    refine ⟨h11,h9,h10,h5,?_,?_,hacc,?_⟩
    · simpa only [M,Function.update_of_ne (by decide : (2 : Fin 16) ≠ 14),Function.update_self] using hframe 2 (by decide)
    · simpa only [M,Function.update_self] using hframe 14 (by decide)
    · intro j hj
      have hsub : dyadicSelectorWrites ⊆ generatedDyadicSelectorWrites := by decide
      rw [hframe j (fun h => hj (hsub h))]
      simp only [generatedDyadicSelectorWrites,List.mem_cons,List.not_mem_nil,or_false,not_or] at hj
      simp [M,hj]) le_rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
