module

public import IntegerMultBounds.MathlibTM2.Fast.TableWeight
public import IntegerMultBounds.MathlibTM2.Fast.TableForFrom

/-! Generate only the owned interval of the existing normalized diagonal table.
The original global row index feeds tblDiagBody, so phase offsets are retained. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.MathlibTM2.Fast.TableNum IntegerMultBounds.Resampling
  IntegerMultBounds.Resampling.WeightTable IntegerMultBounds.Resampling.WeightNat
  IntegerMultBounds.MathlibTM2.Layer

structure DiagonalReady (s t α p : ℕ) {A : ℕ} (st : TblSt 48 A) : Prop where
  piValue : st.val 18 = piN p
  precision : st.val 19 = p
  denominator : st.val 21 = s*s
  sign : st.val 22 = 0
  sourceSize : st.val 34 = s
  targetSize : st.val 35 = t
  alphaSquare : st.val 41 = α*α
  scale : st.val 44 = 2^(α*α+α*α)
  zero : st.val 38 = 0

def diagonalInterval (A w s t α p c n : ℕ) : List (Fin (A+4)) :=
  (List.range n).flatMap fun j => coeffSyms A w (red w ⟨tableD s t α p ((c+j : ℕ) : ZMod s),0⟩)

def tblDiagonalInterval : TblCode 48 := tblForFrom 37 47 tblDiagBody

theorem tblDiagonalInterval_do {A W w s t α p c n : ℕ} (st : TblSt 48 A)
    (hready : DiagonalReady s t α p st) (hc : st.val 37 = c) (hend : st.val 47 = c+n)
    (hs : 0 < s) (hfit : c+n ≤ s) (hp : 13 ≤ p) (hα : 2 ≤ α) (hαp : α^2 ≤ p)
    (hW : α^2*(s+t)^2*2^(13*p+8) < 2^W) :
    TblDo A W w tblDiagonalInterval st
      (fun F => F.acc = (diagonalInterval A w s t α p c n).reverse++st.acc ∧
        DiagonalReady s t α p F) (n*(310*p+123)+2) := by
  have hbound := (tbl_W_facts hα (by omega : 1 ≤ s+t) hW).2.2.1
  have hNW : c+n < 2^W := calc
    c+n ≤ s := hfit
    _ ≤ s+t := Nat.le_add_right _ _
    _ ≤ (s+t)*(s+t) := Nat.le_mul_self _
    _ < 2^W := hbound
  let word := fun j => coeffSyms A w (red w ⟨tableD s t α p ((c+j : ℕ) : ZMod s),0⟩)
  let Inv := fun j (R : TblSt 48 A) =>
    R.acc = ((List.range j).flatMap word).reverse++st.acc ∧ DiagonalReady s t α p R
  apply TblDo.forFrom c n (310*p+120) hc hend hNW (by decide) Inv
  · exact ⟨by simp,hready⟩
  · intro j hj R ⟨hacc,hr⟩ hi hstop
    refine (tblDiagBody_do R hr.piValue hr.precision hr.denominator hr.sign hr.sourceSize hr.targetSize
      hr.alphaSquare hr.scale hr.zero hi (by omega) hp hα hαp hW).keep.mono (fun R' ⟨hacc',hframe⟩ => ?_) le_rfl
    refine ⟨(hframe 37 (by decide)).trans hi,(hframe 47 (by decide)).trans hstop,?_,?_⟩
    · simp only [hacc',hacc,tbl_range_flatMap_succ,List.append_assoc]
      rfl
    · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · simpa only [Function.update_of_ne (show (18 : Fin 48) ≠ 37 by decide),hframe 18 (by decide)] using hr.piValue
      · simpa only [Function.update_of_ne (show (19 : Fin 48) ≠ 37 by decide),hframe 19 (by decide)] using hr.precision
      · simpa only [Function.update_of_ne (show (21 : Fin 48) ≠ 37 by decide),hframe 21 (by decide)] using hr.denominator
      · simpa only [Function.update_of_ne (show (22 : Fin 48) ≠ 37 by decide),hframe 22 (by decide)] using hr.sign
      · simpa only [Function.update_of_ne (show (34 : Fin 48) ≠ 37 by decide),hframe 34 (by decide)] using hr.sourceSize
      · simpa only [Function.update_of_ne (show (35 : Fin 48) ≠ 37 by decide),hframe 35 (by decide)] using hr.targetSize
      · simpa only [Function.update_of_ne (show (41 : Fin 48) ≠ 37 by decide),hframe 41 (by decide)] using hr.alphaSquare
      · simpa only [Function.update_of_ne (show (44 : Fin 48) ≠ 37 by decide),hframe 44 (by decide)] using hr.scale
      · simpa only [Function.update_of_ne (show (38 : Fin 48) ≠ 37 by decide),hframe 38 (by decide)] using hr.zero
  · intro F hI _ _
    exact hI

end IntegerMultBounds.MathlibTM2.Fast.TableVM
