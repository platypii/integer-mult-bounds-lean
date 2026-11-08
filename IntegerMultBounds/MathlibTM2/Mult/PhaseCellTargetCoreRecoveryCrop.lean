module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedRecoveryCrop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTargetCorePacked

/-! Instantiate the executed recovery crop on manuscript J_k endpoints. The
principal result stays in original ambient coordinates; only owned rows leave. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 19 Q A U}

theorem targetCoreRecoveryCrop_exec (q t L k radius : ℕ)
    (ha : radius ≤ cut s t L k) (hb : cut s t L (k+1)+radius ≤ s)
    (Zs : List (ZMod s → ℂ)) (Ds : List (ZMod s → GaussianInt)) (ε : ℝ)
    (tail : List (Fin (A+4))) (v : HS 19 Q A U) (S : Stacks 19 A)
    (hq : (S.R 0).length = q) (hstart : (S.R 1).length = cut s t L k-radius)
    (hstop : (S.R 2).length = cut s t L (k+1)+radius)
    (hoffset : (S.R 3).length = radius) (hrows : (S.R 4).length = rows s t L k)
    (hN : (S.R 5).length = Ds.length)
    (hblank : ∀ i ∈ ([(6 : Fin 19),7,8,9,10,13,14,15,16,17,18]), S.R i = [])
    (hsrc : S.R 11 = (Ds.map (fun D => cstream A (2*q+8)
      (packedInterval (cut s t L k-radius) (rows s t L k+2*radius) D))).flatten++tail)
    (hgood : List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn
      (haloVertices s (cut s t L k-radius) (cut s t L (k+1)+radius))
      (packedIntervalRead q (2*q+8) (cut s t L k-radius)
        (cstream A (2*q+8) (packedInterval (cut s t L k-radius) (rows s t L k+2*radius) D)++tail)) z ε) Zs Ds) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ generatedRecoveryCropCost q (cut s t L k-radius) (cut s t L (k+1)+radius)
        radius (rows s t L k) Ds.length ∧
      Exec body generatedRecoveryCrop (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 11 tail) 12
          ((Ds.reverse.map (fun D => cstream A (2*q+8)
            (packedInterval (cut s t L k) (rows s t L k) D))).flatten++S.R 12))}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (haloVertices s (cut s t L k) (cut s t L (k+1)))
        (packedIntervalRead q (2*q+8) (cut s t L k)
          (cstream A (2*q+8) (packedInterval (cut s t L k) (rows s t L k) D)++S.R 12)) z ε) Zs.reverse Ds.reverse ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          8*generatedRecoveryCropCost q (cut s t L k-radius) (cut s t L (k+1)+radius)
            radius (rows s t L k) Ds.length) depth generatedRecoveryCrop (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 11 tail) 12
          ((Ds.reverse.map (fun D => cstream A (2*q+8)
            (packedInterval (cut s t L k) (rows s t L k) D))).flatten++S.R 12))})) := by
  have hm := cut_mono s t L (show k ≤ k+1 by omega)
  have hspan : cut s t L (k+1)+radius-(cut s t L k-radius) = rows s t L k+2*radius := by
    dsimp only [rows]; omega
  have hbase : cut s t L k-radius+radius = cut s t L k := Nat.sub_add_cancel ha
  have hend : cut s t L k+rows s t L k = cut s t L (k+1) := by dsimp only [rows]; omega
  have hab : cut s t L k-radius ≤ cut s t L (k+1)+radius := by omega
  have heq : cut s t L k-radius+(cut s t L (k+1)+radius-(cut s t L k-radius)) =
      cut s t L (k+1)+radius := Nat.add_sub_of_le hab
  have hsum : cut s t L k-radius+(rows s t L k+2*radius) = cut s t L (k+1)+radius := by omega
  obtain ⟨v',n,hu,hn,he,haccuracy⟩ := generatedRecoveryCrop_exec (body := body) q
    (cut s t L k-radius) (cut s t L (k+1)+radius) radius (rows s t L k)
    (by omega) (by rw [hspan]; omega) Zs Ds ε tail v S hq hstart hstop hoffset hrows hN hblank
    (by simpa only [hspan] using hsrc) (by simpa only [hspan,hsum] using hgood)
  rw [hbase] at he haccuracy
  rw [hend] at haccuracy
  exact ⟨v',n,hu,hn,he,haccuracy,fun depth => generatedRecoveryCrop_within_stock he hn depth⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
