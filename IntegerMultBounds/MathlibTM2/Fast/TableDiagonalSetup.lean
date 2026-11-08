module

public import IntegerMultBounds.MathlibTM2.Fast.TableDiagonalInterval

/-! One-time ordinary scalar setup for a local D' coefficient page. The pi
approximation, squared parameter and dyadic divisor are all computed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.MathlibTM2.Fast.TableNum IntegerMultBounds.Resampling
  IntegerMultBounds.Resampling.WeightNat IntegerMultBounds.MathlibTM2.Layer

open scoped Nat

def tblDiagonalSetup : TblCode 48 :=
  tblPiSetup48 ;;
    tblBlock 48 [.zero 38,.mul 36 36 41,.add 41 41 43,.mul 34 34 21] (.zero 22) ;;
    tblPow2 44 43 45

theorem tblDiagonalSetup_do {A W w s t α p : ℕ} (st : TblSt 48 A)
    (hS : st.val 34 = s) (hT : st.val 35 = t) (hαval : st.val 36 = α) (hpval : st.val 19 = p)
    (hs : 0 < s) (hp : 13 ≤ p) (hα : 2 ≤ α) (hαp : α^2 ≤ p)
    (hW : α^2*(s+t)^2*2^(13*p+8) < 2^W) :
    TblDo A W w tblDiagonalSetup st (fun F => DiagonalReady s t α p F ∧
      F.val 37 = st.val 37 ∧ F.val 47 = st.val 47 ∧ F.acc = st.acc) (160*p+450) := by
  obtain ⟨hW1,hW2,hW3,hW4⟩ := tbl_W_facts hα (by omega : 1 ≤ s+t) hW
  have hNN : s*s ≤ (s+t)*(s+t) := Nat.mul_le_mul (by omega) (by omega)
  have hst : s+t ≤ (s+t)*(s+t) := Nat.le_mul_self _
  have hαα : α*α ≤ α*α*((s+t)*(s+t)) := Nat.le_mul_of_pos_right _ (by positivity)
  have hαα' : α*α ≤ p := by rw [←sq]; exact hαp
  have hαW : α*α+α*α < W := by omega
  have h2αα : α*α+α*α < 2^W := lt_trans hαW Nat.lt_two_pow_self
  refine ((tbl_pi48_do (W := W) (w := w) st hpval (by omega) (by omega)).seq
    (K₂ := 5+(4*(α*α+α*α)+5)) (fun H ⟨hpi,hacc,hframe⟩ => ?_)).mono (fun _ h => h) (by omega)
  refine (TblDo.block _ _ ?_ rfl).seq (fun K hK => ?_)
  · simp [tblFitsList,TblIns.fits,TblIns.exact,hframe (36 : Fin 48) (by decide),hαval,
      hframe (34 : Fin 48) (by decide),hS]
    omega
  subst hK
  let K := tblExactList A w ([.zero 38,.mul 36 36 41,.add 41 41 43,.mul 34 34 21]++[.zero 22]) H
  have hv : K.val 18 = piN p ∧ K.val 19 = p ∧ K.val 21 = s*s ∧ K.val 22 = 0 ∧
      K.val 34 = s ∧ K.val 35 = t ∧ K.val 41 = α*α ∧ K.val 43 = α*α+α*α ∧
      K.val 38 = 0 ∧ K.acc = st.acc ∧ K.val 37 = st.val 37 ∧ K.val 47 = st.val 47 := by
    simp [K,tblExactList,TblIns.exact,hpi,hframe (19 : Fin 48) (by decide),
      hframe (34 : Fin 48) (by decide),hframe (35 : Fin 48) (by decide),hframe (36 : Fin 48) (by decide),
      hframe (37 : Fin 48) (by decide),hframe (47 : Fin 48) (by decide),hpval,hS,hT,hαval,hacc]
  obtain ⟨h18,h19,h21,h22,h34,h35,h41,h43,h38,haccK,h37,h47⟩ := hv
  have hpow := tblPow2_do (A := A) (W := W) (w := w) (c := 44) (e := 43) (i := 45)
    (by decide) (by decide) (by decide) K (by rw [h43]; exact hαW)
  rw [h43] at hpow
  refine hpow.mono (fun F ⟨h44,_,hkeep,haccF⟩ => ?_) le_rfl
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,h44,?_⟩,?_,?_,haccF.trans haccK⟩
  · exact (hkeep 18 (by decide) (by decide)).trans h18
  · exact (hkeep 19 (by decide) (by decide)).trans h19
  · exact (hkeep 21 (by decide) (by decide)).trans h21
  · exact (hkeep 22 (by decide) (by decide)).trans h22
  · exact (hkeep 34 (by decide) (by decide)).trans h34
  · exact (hkeep 35 (by decide) (by decide)).trans h35
  · exact (hkeep 41 (by decide) (by decide)).trans h41
  · exact (hkeep 38 (by decide) (by decide)).trans h38
  · exact (hkeep 37 (by decide) (by decide)).trans h37
  · exact (hkeep 47 (by decide) (by decide)).trans h47

def tblOwnedDiagonal : TblCode 48 := .seq tblDiagonalSetup tblDiagonalInterval

theorem tblOwnedDiagonal_do {A W w s t α p c n : ℕ} (st : TblSt 48 A)
    (hS : st.val 34 = s) (hT : st.val 35 = t) (hαval : st.val 36 = α) (hpval : st.val 19 = p)
    (hc : st.val 37 = c) (hend : st.val 47 = c+n)
    (hs : 0 < s) (hfit : c+n ≤ s) (hp : 13 ≤ p) (hα : 2 ≤ α) (hαp : α^2 ≤ p)
    (hW : α^2*(s+t)^2*2^(13*p+8) < 2^W) :
    TblDo A W w tblOwnedDiagonal st
      (fun F => F.acc = (diagonalInterval A w s t α p c n).reverse++st.acc)
      ((160*p+450)+(n*(310*p+123)+2)) := by
  refine (tblDiagonalSetup_do st hS hT hαval hpval hs hp hα hαp hW).seq (fun H ⟨hr,h37,h47,hacc⟩ => ?_)
  exact (tblDiagonalInterval_do H hr (h37.trans hc) (h47.trans hend) hs hfit hp hα hαp hW).mono
    (fun _ hh => by simpa only [hacc] using hh.1) le_rfl

end IntegerMultBounds.MathlibTM2.Fast.TableVM
