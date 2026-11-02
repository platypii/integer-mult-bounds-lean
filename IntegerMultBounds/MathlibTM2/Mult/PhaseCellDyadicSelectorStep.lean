module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicSelectorDescendCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicSelectorFinishCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicScheduleSelector

/-! Fixed selector dispatch, with one common transition contract for both
Euclidean orientations. The accumulator and retained inputs are preserved. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM

inductive DyadicSelectorResult where
  | found (row : DyadicStageRow)
  | next (a b packet count index : ℕ)

def dyadicSelectorTransition (a b C n i : ℕ) : DyadicSelectorResult :=
  if a < b then
    if i+1 < n then .next (b-a) a (C*2^a) (n-1) (n-2-i)
    else .found ⟨2^(b-a),C,a⟩
  else if 0 < i then .next (a-b) b (C*2^b) (n-1) (i-1)
  else .found ⟨2^(a-b),C,b⟩

def DyadicSelectorResult.Holds {A : ℕ} : DyadicSelectorResult → TblSt 16 A → Prop
  | .found row,st => st.val 5 = 0 ∧ st.val 11 = row.outerCount ∧ st.val 9 = row.blockWidth ∧ st.val 10 = row.fieldBits
  | .next a b C n i,st => st.val 0 = a ∧ st.val 1 = b ∧ st.val 9 = C ∧ st.val 5 = n ∧ st.val 8 = i

def dyadicSelectorWrites : List (Fin 16) := [0,1,5,8,9,10,11,12,13]

def dyadicSelectorStepCode : TblCode 16 :=
  .ite 0 1
    (.seq (tblBlock 16 [.copy 8 12] (.inc 12))
      (.ite 12 5 dyadicSelectorRightCode (dyadicSelectorFinishCode 0 1 0)))
    (.ite 2 8 dyadicSelectorLeftCode (dyadicSelectorFinishCode 1 0 1))

theorem dyadicSelectorStepCode_do {A W w a b C n i : ℕ} (st : TblSt 16 A)
    (ha : st.val 0 = a) (hb : st.val 1 = b) (hz : st.val 2 = 0)
    (hn : st.val 5 = n) (hi : st.val 8 = i) (hC : st.val 9 = C) (hone : st.val 14 = 1)
    (hin : i < n) (hnBound : n ≤ a+b) (hbits : a+b < W) (hfit : C*2^(a+b) < 2^W) :
    TblDo A W w dyadicSelectorStepCode st (fun st' =>
      (dyadicSelectorTransition a b C n i).Holds st' ∧ st'.acc = st.acc ∧
      ∀ j, j ∉ dyadicSelectorWrites → st'.val j = st.val j) (4*(a+b)+17) := by
  have haW : a < 2^W := lt_trans (by omega : a < W) Nat.lt_two_pow_self
  have hbW : b < 2^W := lt_trans (by omega : b < W) Nat.lt_two_pow_self
  have hnW : n < 2^W := lt_trans (by omega : n < W) Nat.lt_two_pow_self
  have hCa : C*2^a < 2^W := (Nat.mul_le_mul_left C
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : a ≤ a+b))).trans_lt hfit
  have hCb : C*2^b < 2^W := (Nat.mul_le_mul_left C
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : b ≤ a+b))).trans_lt hfit
  unfold dyadicSelectorStepCode
  by_cases hab : a < b
  · let M : TblSt 16 A := ⟨Function.update st.val 12 (i+1),st.acc⟩
    have hprep : TblDo A W w (tblBlock 16 [.copy 8 12] (.inc 12)) st (fun s => s = M) 2 := by
      apply TblDo.block
      · simp [tblFitsList,TblIns.fits,TblIns.exact,hi]; omega
      · simp [tblExactList,TblIns.exact,M,hi]
    apply (TblDo.iteT (by simpa [ha,hb] using hab)
      (hprep.seq (K₂ := 4*(a+b)+14) ?_)).mono (fun _ h => h) (by omega)
    intro s hs
    subst s
    have hm (j : Fin 16) (hj : j ≠ 12) : M.val j = st.val j := Function.update_of_ne hj _ _
    have hj12 (j : Fin 16) (hj : j ∉ dyadicSelectorWrites) : j ≠ 12 := by
      intro he; apply hj; simp [dyadicSelectorWrites,he]
    by_cases hlast : i+1 < n
    · have hd := dyadicSelectorRightCode_do (W := W) (w := w) M
        ((hm 0 (by decide)).trans ha) ((hm 1 (by decide)).trans hb) ((hm 5 (by decide)).trans hn)
        ((hm 8 (by decide)).trans hi) ((hm 9 (by decide)).trans hC) ((hm 14 (by decide)).trans hone)
        hab.le hlast hbW hnW (by omega) hCa
      apply (TblDo.iteT (by simpa [M,hn] using hlast) hd).mono
      · intro F ⟨h0,h1,h5,h8,h9,hacc,hframe⟩
        refine ⟨?_,hacc,?_⟩
        · simpa [dyadicSelectorTransition,DyadicSelectorResult.Holds,hab,hlast] using ⟨h0,h1,h9,h5,h8⟩
        · intro j hj
          exact (hframe j hj).trans (hm j (hj12 j hj))
      · omega
    · have hd := dyadicSelectorFinishCode_do (W := W) (w := w) 0 1 0 (by decide) (by decide) M
        ((hm 1 (by decide)).trans hb) ((hm 0 (by decide)).trans ha) ((hm 0 (by decide)).trans ha)
        hab.le hbW (by omega)
      apply (TblDo.iteF (by simpa [M,hn] using hlast) hd).mono
      · intro F ⟨h11,h10,h12,h13,h5,hacc,hframe⟩
        have h9 := (hframe 9 (by decide)).trans ((hm 9 (by decide)).trans hC)
        refine ⟨?_,hacc,?_⟩
        · simpa [dyadicSelectorTransition,DyadicSelectorResult.Holds,hab,hlast] using ⟨h5,h11,h9,h10⟩
        · intro j hj
          have hsub : [(5 : Fin 16),10,11,12,13] ⊆ dyadicSelectorWrites := by decide
          exact (hframe j (fun h => hj (hsub h))).trans (hm j (hj12 j hj))
      · omega
  · have hba : b ≤ a := by omega
    by_cases hi0 : 0 < i
    · have hd := dyadicSelectorLeftCode_do (W := W) (w := w) st ha hb hn hi hC hone
        hba hi0 hin haW hnW (by omega) hCb
      apply (TblDo.iteF (by simpa [ha,hb] using hab) (TblDo.iteT (by simpa [hz,hi] using hi0) hd)).mono
      · intro F ⟨h0,h5,h8,h9,hacc,hframe⟩
        have h1 := (hframe 1 (by decide)).trans hb
        refine ⟨?_,hacc,?_⟩
        · simpa [dyadicSelectorTransition,DyadicSelectorResult.Holds,hab,hi0] using ⟨h0,h1,h9,h5,h8⟩
        · intro j hj
          have hsub : [(0 : Fin 16),5,8,9,10,11,13] ⊆ dyadicSelectorWrites := by decide
          exact hframe j (fun h => hj (hsub h))
      · omega
    · have hd := dyadicSelectorFinishCode_do (W := W) (w := w) 1 0 1 (by decide) (by decide) st
        ha hb hb hba haW (by omega)
      apply (TblDo.iteF (by simpa [ha,hb] using hab) (TblDo.iteF (by simpa [hz,hi] using hi0) hd)).mono
      · intro F ⟨h11,h10,h12,h13,h5,hacc,hframe⟩
        have h9 := (hframe 9 (by decide)).trans hC
        refine ⟨?_,hacc,?_⟩
        · simpa [dyadicSelectorTransition,DyadicSelectorResult.Holds,hab,hi0] using ⟨h5,h11,h9,h10⟩
        · intro j hj
          have hsub : [(5 : Fin 16),10,11,12,13] ⊆ dyadicSelectorWrites := by decide
          exact hframe j (fun h => hj (hsub h))
      · omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
