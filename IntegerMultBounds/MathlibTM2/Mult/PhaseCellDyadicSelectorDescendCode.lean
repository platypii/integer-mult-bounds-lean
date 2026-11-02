module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableScalePow2

/-! The left descent of the arithmetic row selector, using one reusable
packet-width scaler. No row is emitted on a descent. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM

def dyadicSelectorLeftCode : TblCode 16 :=
  .seq (.ins (.copy 1 10)) (.seq (tblScalePow2 9 10 11 13)
    (tblBlock 16 [.sub 0 1 0,.sub 8 14 8] (.sub 5 14 5)))

theorem dyadicSelectorLeftCode_do {A W w a b n i C : ℕ} (st : TblSt 16 A)
    (ha : st.val 0 = a) (hb : st.val 1 = b) (hn : st.val 5 = n)
    (hi : st.val 8 = i) (hC : st.val 9 = C) (hone : st.val 14 = 1)
    (hba : b ≤ a) (hi0 : 0 < i) (hin : i < n) (haW : a < 2^W)
    (hnW : n < 2^W) (hbW : b < W) (hCW : C*2^b < 2^W) :
    TblDo A W w dyadicSelectorLeftCode st (fun st' =>
      st'.val 0 = a-b ∧ st'.val 5 = n-1 ∧ st'.val 8 = i-1 ∧ st'.val 9 = C*2^b ∧
      st'.acc = st.acc ∧
      ∀ j, j ∉ [(0 : Fin 16),5,8,9,10,11,13] → st'.val j = st.val j) (4*b+10) := by
  let M : TblSt 16 A := ⟨Function.update st.val 10 b,st.acc⟩
  have hcopy : TblDo A W w (.ins (.copy 1 10)) st (fun st' => st' = M) 1 :=
    TblDo.insX _ (by trivial) (by simp [TblIns.exact,M,hb])
  unfold dyadicSelectorLeftCode
  apply (hcopy.seq (K₂ := 4*b+9) ?_).mono (fun _ h => h) (by omega)
  intro st₁ he
  subst st₁
  have hscale := tblScalePow2_do (W := W) (w := w) (9 : Fin 16) 10 11 13
    (by decide) (by decide) (by decide) (by decide) (by decide) M
    (by simpa only [M,Function.update_of_ne (by decide : (9 : Fin 16) ≠ 10)] using hC)
    (by simp [M]) hbW hCW
  apply hscale.seq (K₂ := 3)
  intro s ⟨hpacket,hpow,hindex,hacc,hframe⟩
  have haS : s.val 0 = a := by simpa [M,ha] using hframe 0 (by decide) (by decide) (by decide)
  have hbS : s.val 1 = b := by simpa [M,hb] using hframe 1 (by decide) (by decide) (by decide)
  have hnS : s.val 5 = n := by simpa [M,hn] using hframe 5 (by decide) (by decide) (by decide)
  have hiS : s.val 8 = i := by simpa [M,hi] using hframe 8 (by decide) (by decide) (by decide)
  have honeS : s.val 14 = 1 := by simpa [M,hone] using hframe 14 (by decide) (by decide) (by decide)
  apply TblDo.block
  · simp [tblFitsList,TblIns.fits,TblIns.exact,haS,hbS,hnS,hiS,honeS]
    omega
  · refine ⟨?_,?_,?_,?_,hacc,?_⟩
    · simp [tblExactList,TblIns.exact,haS,hbS]
    · simp [tblExactList,TblIns.exact,hnS,honeS]
    · simp [tblExactList,TblIns.exact,hiS,honeS]
    · simpa [tblExactList,TblIns.exact] using hpacket
    · intro j hj
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hj
      have hh := hframe j hj.2.2.2.1 hj.2.2.2.2.2.1 hj.2.2.2.2.2.2
      simpa only [List.cons_append,List.nil_append,tblExactList,TblIns.exact,
        Function.update_of_ne hj.1,Function.update_of_ne hj.2.1,Function.update_of_ne hj.2.2.1,
        M,Function.update_of_ne hj.2.2.2.2.1] using hh

def dyadicSelectorRightCode : TblCode 16 :=
  .seq (.ins (.copy 0 10)) (.seq (tblScalePow2 9 10 11 13)
    (tblBlock 16 [.sub 1 0 0,.copy 10 1,.sub 5 14 12,.sub 12 14 12,.sub 12 8 8] (.sub 5 14 5)))

theorem dyadicSelectorRightCode_do {A W w a b n i C : ℕ} (st : TblSt 16 A)
    (ha : st.val 0 = a) (hb : st.val 1 = b) (hn : st.val 5 = n)
    (hi : st.val 8 = i) (hC : st.val 9 = C) (hone : st.val 14 = 1)
    (hab : a ≤ b) (hin : i+1 < n) (hbW : b < 2^W)
    (hnW : n < 2^W) (haW : a < W) (hCW : C*2^a < 2^W) :
    TblDo A W w dyadicSelectorRightCode st (fun st' =>
      st'.val 0 = b-a ∧ st'.val 1 = a ∧ st'.val 5 = n-1 ∧ st'.val 8 = n-2-i ∧
      st'.val 9 = C*2^a ∧ st'.acc = st.acc ∧
      ∀ j, j ∉ [(0 : Fin 16),1,5,8,9,10,11,12,13] → st'.val j = st.val j) (4*a+13) := by
  let M : TblSt 16 A := ⟨Function.update st.val 10 a,st.acc⟩
  have hcopy : TblDo A W w (.ins (.copy 0 10)) st (fun st' => st' = M) 1 :=
    TblDo.insX _ (by trivial) (by simp [TblIns.exact,M,ha])
  unfold dyadicSelectorRightCode
  apply (hcopy.seq (K₂ := 4*a+12) ?_).mono (fun _ h => h) (by omega)
  intro st₁ he
  subst st₁
  have hscale := tblScalePow2_do (W := W) (w := w) (9 : Fin 16) 10 11 13
    (by decide) (by decide) (by decide) (by decide) (by decide) M
    (by simpa only [M,Function.update_of_ne (by decide : (9 : Fin 16) ≠ 10)] using hC)
    (by simp [M]) haW hCW
  apply hscale.seq (K₂ := 6)
  intro s ⟨hpacket,hpow,hindex,hacc,hframe⟩
  have haS : s.val 0 = a := by simpa [M,ha] using hframe 0 (by decide) (by decide) (by decide)
  have hbS : s.val 1 = b := by simpa [M,hb] using hframe 1 (by decide) (by decide) (by decide)
  have hnS : s.val 5 = n := by simpa [M,hn] using hframe 5 (by decide) (by decide) (by decide)
  have hiS : s.val 8 = i := by simpa [M,hi] using hframe 8 (by decide) (by decide) (by decide)
  have honeS : s.val 14 = 1 := by simpa [M,hone] using hframe 14 (by decide) (by decide) (by decide)
  have hbits : s.val 10 = a := by simpa [M] using hframe 10 (by decide) (by decide) (by decide)
  apply TblDo.block
  · simp [tblFitsList,TblIns.fits,TblIns.exact,haS,hbS,hnS,hiS,honeS,hbits]
    omega
  · refine ⟨?_,?_,?_,?_,?_,hacc,?_⟩
    · simp [tblExactList,TblIns.exact,haS,hbS]
    · simp [tblExactList,TblIns.exact,hbits]
    · simp [tblExactList,TblIns.exact,hnS,honeS]
    · simp [tblExactList,TblIns.exact,hnS,honeS,hiS,Nat.sub_sub]
    · simpa [tblExactList,TblIns.exact] using hpacket
    · intro j hj
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hj
      have hh := hframe j hj.2.2.2.2.1 hj.2.2.2.2.2.2.1 hj.2.2.2.2.2.2.2.2
      simpa only [List.cons_append,List.nil_append,tblExactList,TblIns.exact,
        Function.update_of_ne hj.1,Function.update_of_ne hj.2.1,Function.update_of_ne hj.2.2.1,
        Function.update_of_ne hj.2.2.2.1,Function.update_of_ne hj.2.2.2.2.2.2.2.1,
        M,Function.update_of_ne hj.2.2.2.2.2.1] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
