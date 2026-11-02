module

public import IntegerMultBounds.MathlibTM2.Fast.TableProg

/-! The selected leaf of the Euclidean selector constructs its prefix master
and signals completion. Both orientation branches use this same fixed macro. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM

def dyadicSelectorFinishCode (source x y : Fin 16) : TblCode 16 :=
  .seq (tblBlock 16 [.copy source 10] (.sub x y 12))
    (.seq (tblPow2 11 12 13) (.ins (.zero 5)))

theorem dyadicSelectorFinishCode_do {A W w m n k : ℕ} (source x y : Fin 16)
    (hfrom : x ≠ 10) (hsub : y ≠ 10) (st : TblSt 16 A)
    (hm : st.val x = m) (hn : st.val y = n) (hk : st.val source = k)
    (hnm : n ≤ m) (hmW : m < 2^W) (hdiff : m-n < W) :
    TblDo A W w (dyadicSelectorFinishCode source x y) st (fun st' =>
      st'.val 11 = 2^(m-n) ∧ st'.val 10 = k ∧ st'.val 12 = m-n ∧ st'.val 13 = m-n ∧
      st'.val 5 = 0 ∧ st'.acc = st.acc ∧
      ∀ j, j ∉ [(5 : Fin 16),10,11,12,13] → st'.val j = st.val j) (4*(m-n)+8) := by
  let M : TblSt 16 A := ⟨Function.update (Function.update st.val 10 k) 12 (m-n),st.acc⟩
  have hprep : TblDo A W w (tblBlock 16 [.copy source 10] (.sub x y 12)) st
      (fun st' => st' = M) 2 := by
    apply TblDo.block
    · simp only [List.cons_append,List.nil_append,tblFitsList,TblIns.fits,TblIns.exact,Function.update_of_ne hfrom,
        Function.update_of_ne hsub,hm,hn]
      exact ⟨trivial,⟨⟨hnm,hmW⟩,trivial⟩⟩
    · simp only [List.cons_append,List.nil_append,tblExactList,TblIns.exact,M,Function.update_of_ne hfrom,Function.update_of_ne hsub,hm,hn,hk]
  unfold dyadicSelectorFinishCode
  apply (hprep.seq (K₂ := 4*(m-n)+6) ?_).mono (fun _ h => h) (by omega)
  intro st₁ he
  subst st₁
  have hp := tblPow2_do (W := W) (w := w) (c := (11 : Fin 16)) (e := 12) (i := 13)
    (by decide) (by decide) (by decide) M (by simpa only [M,Function.update_self] using hdiff)
  apply (hp.seq (K₂ := 1) ?_).mono (fun _ h => h) (by change 4*(m-n)+5+1 ≤ 4*(m-n)+6; omega)
  intro s ⟨hp,hi,hframe,hacc⟩
  apply TblDo.insX (.zero 5) (by trivial)
  refine ⟨?_,?_,?_,?_,?_,hacc,?_⟩
  · simpa only [TblIns.exact,Function.update_of_ne (by decide : (11 : Fin 16) ≠ 5),M,Function.update_self] using hp
  · have hh := hframe 10 (by decide) (by decide)
    simpa only [TblIns.exact,Function.update_of_ne (by decide : (10 : Fin 16) ≠ 5),M,
      Function.update_of_ne (by decide : (10 : Fin 16) ≠ 12),Function.update_self] using hh.trans (by rfl)
  · simpa only [TblIns.exact,Function.update_of_ne (by decide : (12 : Fin 16) ≠ 5),M,Function.update_self]
      using hframe 12 (by decide) (by decide)
  · simpa only [TblIns.exact,Function.update_of_ne (by decide : (13 : Fin 16) ≠ 5),M,Function.update_self] using hi
  · simp only [TblIns.exact,Function.update_self]
  · intro j hj
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hj
    simpa only [TblIns.exact,Function.update_of_ne hj.1,M,
      Function.update_of_ne hj.2.2.2.1,Function.update_of_ne hj.2.1] using
      hframe j hj.2.2.1 hj.2.2.2.2

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
