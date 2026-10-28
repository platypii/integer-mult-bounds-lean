module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedAddressCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorPage

/-! Counted factor-page assembly is priced from generic word and row bounds. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem factorRowLoopCost_poly {q W N start L m R : ℕ}
    (hR : 1 ≤ R) (hq : q ≤ R) (hW : W ≤ R) (hN : N ≤ R)
    (hw : 2*q+8 ≤ R) (hstart : start+L ≤ R) (hm : m ≤ R) :
    factorRowLoopCost q W N start L m ≤ L*(2000000*R^3+4)+2*L+4 := by
  have hs : (Finset.range L).sum (fun i => 1+factorWordCost q (start+L-(i+1)) m W N+3) ≤
      L*(2000000*R^3+4) := by
    calc
      _ ≤ (Finset.range L).sum (fun _ => 2000000*R^3+4) := by
        apply Finset.sum_le_sum
        intro i hi
        have hn : start+L-(i+1) ≤ R := (Nat.sub_le _ _).trans hstart
        have hc := factorWordCost_poly hR hq hn hm hW hN hw
        omega
      _ = _ := by simp
  dsimp only [factorRowLoopCost]
  omega

theorem factorRowCost_poly {q W N start m R : ℕ}
    (hR : 1 ≤ R) (hq : q ≤ R) (hW : W ≤ R) (hN : N ≤ R)
    (hw : 2*q+8 ≤ R) (hstart : start+(2*W+1) ≤ R) (hm : m ≤ R) :
    factorRowCost q W N start m ≤ 3000000*R^4 := by
  have hc := factorRowLoopCost_poly hR hq hW hN hw hstart hm
  have hL : 2*W+1 ≤ R := by omega
  have hprod := Nat.mul_le_mul_right (2000000*R^3+4) hL
  have hp4 : R ≤ R^4 := by simpa using Nat.pow_le_pow_right hR (show 1 ≤ 4 by decide)
  dsimp only [factorRowCost]
  nlinarith only [hc,hprod,hL,hW,hR,hp4]

theorem factorSlidingStepCost_poly {q W N n R : ℕ}
    (hR : 1 ≤ R) (hq : q ≤ R) (hW : W ≤ R) (hN : N ≤ R)
    (hw : 2*q+8 ≤ R) (hn : n+2*W+1 ≤ R) :
    factorSlidingStepCost q W N n ≤ 4000000*R^4 := by
  have hc := factorRowCost_poly hR hq hW hN hw (by omega : n+(2*W+1) ≤ R) (by omega : W+n ≤ R)
  have hp4 : R ≤ R^4 := by simpa using Nat.pow_le_pow_right hR (show 1 ≤ 4 by decide)
  dsimp only [factorSlidingStepCost]
  nlinarith only [hc,hn,hW,hR,hp4]

theorem factorInputsCost_poly {q W N R : ℕ}
    (hR : 1 ≤ R) (hq : q ≤ R) (hW : W ≤ R) (hN : N ≤ R)
    (hw : 2*q+8 ≤ R) (henv : N+2*W+2 ≤ R) :
    factorInputsCost q W N ≤ 5000000*R^5 := by
  have hs : (Finset.range N).sum (fun i => factorSlidingStepCost q W N (1+N-(i+1))+3) ≤
      N*(4000000*R^4+3) := by
    calc
      _ ≤ (Finset.range N).sum (fun _ => 4000000*R^4+3) := by
        apply Finset.sum_le_sum
        intro i hi
        have hn : 1+N-(i+1)+2*W+1 ≤ R := by omega
        exact Nat.add_le_add_right (factorSlidingStepCost_poly hR hq hW hN hw hn) 3
      _ = _ := by simp
  have hprod := Nat.mul_le_mul_right (4000000*R^4+3) hN
  have hp5 : R ≤ R^5 := by simpa using Nat.pow_le_pow_right hR (show 1 ≤ 5 by decide)
  dsimp only [factorInputsCost,factorInputLoopCost]
  nlinarith only [hs,hprod,hN,hR,hp5]

theorem factorWindowCost_poly {q W N R : ℕ}
    (hR : 1 ≤ R) (hq : q ≤ R) (hW : W ≤ R) (hN : N ≤ R)
    (hw : 2*q+8 ≤ R) (henv : N+2*W+2 ≤ R) :
    factorWindowCost q W N ≤ 4000000*R^5 := by
  have hs : (Finset.range (W+1)).sum (fun i => 1+factorRowCost q W N 0 (0+(W+1)-(i+1))+3) ≤
      (W+1)*(3000000*R^4+4) := by
    calc
      _ ≤ (Finset.range (W+1)).sum (fun _ => 3000000*R^4+4) := by
        apply Finset.sum_le_sum
        intro i hi
        have hc := factorRowCost_poly hR hq hW hN hw (by omega : 0+(2*W+1) ≤ R)
          (by omega : 0+(W+1)-(i+1) ≤ R)
        omega
      _ = _ := by simp
  have hL : W+1 ≤ R := by omega
  have hprod := Nat.mul_le_mul_right (3000000*R^4+4) hL
  have hp5 : R ≤ R^5 := by simpa using Nat.pow_le_pow_right hR (show 1 ≤ 5 by decide)
  dsimp only [factorWindowCost,factorWindowLoopCost]
  nlinarith only [hs,hprod,hL,hW,hR,hp5]

theorem factorPageCost_poly {q W N R : ℕ}
    (hR : 1 ≤ R) (hq : q ≤ R) (hW : W ≤ R) (hN : N ≤ R)
    (hw : 2*q+8 ≤ R) (henv : N+2*W+2 ≤ R) :
    factorPageCost q W N ≤ 10000000*R^5 := by
  have hi := factorInputsCost_poly hR hq hW hN hw henv
  have hw' := factorWindowCost_poly hR hq hW hN hw henv
  dsimp only [factorPageCost]
  omega

end IntegerMultBounds.MathlibTM2.Cost
