module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorWord

/-! Structural packed-size and counted-address bounds for generated factor pages. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem packedBandWordCount_le_rows (N W L start : ℕ) :
    packedBandWordCount N W L start ≤ L*N := by
  induction L generalizing start with
  | zero => simp [packedBandWordCount]
  | succ L ih =>
    have hc : min N (start+W+1)-(start-W) ≤ N := (Nat.sub_le _ _).trans (Nat.min_le_left _ _)
    simpa only [packedBandWordCount,Nat.succ_mul] using Nat.add_le_add (ih (start+1)) hc

theorem packedSizeStepCost_le (n W N : ℕ) :
    packedSizeStepCost n W N ≤ 1000*(n+W+N+1) := by
  have hsub : n-W ≤ n := Nat.sub_le _ _
  have hc : min N (n+W+1)-(n-W) ≤ N := (Nat.sub_le _ _).trans (Nat.min_le_left _ _)
  have hclip : N-(n+W+1) ≤ N := Nat.sub_le _ _
  simp only [packedSizeStepCost,clippedBandControlsCost,bandIntervalEndpointsCost,clipUnaryCost,
    List.sum_cons,List.sum_nil]
  omega

theorem packedSizeSumCost_poly (N W start L : ℕ) :
    packedSizeSumCost N W start L ≤ 10000*(N+W+start+L+1)^2 := by
  let H := N+W+start+L+1
  have hH : 1 ≤ H := by dsimp only [H]; omega
  have hs : (Finset.range L).sum (fun i => packedSizeStepCost (start+i) W N+3) ≤ L*(1000*H+3) := by
    calc
      _ ≤ (Finset.range L).sum (fun _ => 1000*H+3) := by
        apply Finset.sum_le_sum
        intro i hi
        have hc := packedSizeStepCost_le (start+i) W N
        have hi' := Finset.mem_range.mp hi
        dsimp only [H]
        omega
      _ = _ := by simp
  have hL : L ≤ H := by dsimp only [H]; omega
  have hstart : start ≤ H := by dsimp only [H]; omega
  have hprod := Nat.mul_le_mul_right (1000*H+3) hL
  have hpow : H ≤ H^2 := by nlinarith only [hH]
  dsimp only [packedSizeSumCost,packedSizeLoopCost]
  change _ ≤ 10000*H^2
  nlinarith only [hs,hprod,hpow,hL,hstart,hH]

theorem rankedBoundaryEntryCost_poly {q n m W N R : ℕ}
    (hR : 1 ≤ R) (hq : q ≤ R) (hn : n ≤ R) (hm : m ≤ R) (hW : W ≤ R) (hN : N ≤ R)
    (hw : 2*q+8 ≤ R) : rankedBoundaryEntryCost q n m W N ≤ 1000000*R^3 := by
  have hcount := packedBandWordCount_le_rows N W (N-(n+1)) (n+1)
  have hrest : N-(n+1) ≤ R := (Nat.sub_le _ _).trans hN
  have hwithin : min N (n+W+1)-1-m ≤ R := (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans ((Nat.min_le_left _ _).trans hN))
  have hprod := Nat.mul_le_mul hrest hN
  have haddress : packedEntryOffset N W n m ≤ R^2+R := by
    unfold packedEntryOffset
    nlinarith only [hcount,hwithin,hprod]
  have hsum := packedSizeSumCost_poly N W (n+1) (N-(n+1))
  have hsum' : packedSizeSumCost N W (n+1) (N-(n+1)) ≤ 360000*R^2 := by
    have hH : N+W+(n+1)+(N-(n+1))+1 ≤ 6*R := by omega
    have hsquare := Nat.pow_le_pow_left hH 2
    nlinarith only [hsum,hsquare]
  have hsub : n-W ≤ R := (Nat.sub_le _ _).trans hn
  have hclip : N-(n+W+1) ≤ R := (Nat.sub_le _ _).trans hN
  have hp2 : R ≤ R^2 := by nlinarith only [hR]
  have hp3 : R^2 ≤ R^3 := by nlinarith only [Nat.mul_le_mul_left (R^2) hR]
  have hcopy : copyPackedWordCost q (packedEntryOffset N W n m) ≤
      (8*R+9)+((R^2+R)*(12*R+9)+10*R+22+(2*R+2)) := by
    unfold copyPackedWordCost
    gcongr
  simp only [rankedBoundaryEntryCost,generatePackedAddressCost,packedSuffixAddressCost,
    packedSuffixControlsCost,packedWithinAddressCost,bandIntervalEndpointsCost,clipUnaryCost,
    List.sum_cons,List.sum_nil]
  nlinarith only [hsum',hcopy,haddress,hsub,hclip,hwithin,hn,hm,hW,hN,hR,hp2,hp3]

theorem factorWordCost_poly {q n m W N R : ℕ}
    (hR : 1 ≤ R) (hq : q ≤ R) (hn : n ≤ R) (hm : m ≤ R) (hW : W ≤ R) (hN : N ≤ R)
    (hw : 2*q+8 ≤ R) : factorWordCost q n m W N ≤ 2000000*R^3 := by
  have hentry := rankedBoundaryEntryCost_poly hR hq hn hm hW hN hw
  have hsub : N-n ≤ R := (Nat.sub_le _ _).trans hN
  have hsub' : N-m ≤ R := (Nat.sub_le _ _).trans hN
  have hsub₁ : m+W+1-n ≤ m+W+1 := Nat.sub_le _ _
  have hsub₂ : n+W+1-m ≤ n+W+1 := Nat.sub_le _ _
  have hp2 : R ≤ R^2 := by nlinarith only [hR]
  have hp3 : R^2 ≤ R^3 := by nlinarith only [Nat.mul_le_mul_left (R^2) hR]
  simp only [factorWordCost,factorChoiceCost,factorEntryCost,feedFactorWordCost,factorZeroEntryCost,
    unaryIfLtCost,unaryIfLeSumCost]
  nlinarith only [hentry,hsub,hsub',hsub₁,hsub₂,hR,hq,hn,hm,hW,hN,hw,hp2,hp3]

end IntegerMultBounds.MathlibTM2.Cost
