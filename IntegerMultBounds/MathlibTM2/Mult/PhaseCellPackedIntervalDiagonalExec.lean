module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedIntervalDiagonal
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCompleteDiagonalBatch

/-! Execute the existing complete D' batch directly from an actual normalized
interval packet, deriving the integer fit facts instead of supplying fields. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {s t Q A : ℕ} [NeZero s] [NeZero t] {P U : Type} {body : P → Pr P tapes Q A U}
noncomputable section

theorem completeDiagonalBatch_packet_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (u alpha B p w a radius n : ℕ) (hs : 0 < s) (hst : s ≤ t) (hfit : a+radius+n ≤ s)
    (hp : 13 ≤ p) (halpha : 2 ≤ alpha) (hsquare : u = alpha^2) (hbudget : alpha^2 ≤ p)
    (hw : p+2 ≤ w) (hroom : 4*w+2 < 2^B)
    (targets : List (ZMod s → ℂ)) (error : ℝ) (word : List (Fin (A+4)))
    (hpacketOut : PackedIntervalOutput p w (a+radius) n targets error word)
    (hwordWidth : p+3 ≤ w) (herror : error ≤ 1/2)
    (hmag : ∀ z ∈ targets, ∀ i ∈ haloVertices s (a+radius) (a+radius+n), ‖z i‖ ≤ (3/2 : ℝ))
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      diagonalMul diagonalMul_injective diagonal_tapes hQ (rsbCr diagonalRole .src .df .dst)) ≤ C)
    (v : HS tapes Q A U) (S : Stacks tapes A) (tail : List (Fin (A+4)))
    (hS : (S.R (recovery (.parameter 4))).length = s)
    (hT : (S.R (recovery (.parameter 5))).length = t)
    (hu : (S.R (recovery (.parameter 1))).length = u)
    (hprec : (S.R (recovery (.parameter 0))).length = p)
    (hprecision : (S.R (recovery (.control .precision))).length = p)
    (hpacket : (S.R (recovery (.control .packet))).length = w)
    (hB : (S.R diagonalWidthSource).length = B)
    (ha : (S.R diagonalHaloStart).length = a)
    (hradius : (S.R diagonalCropOffset).length = radius)
    (hn : (S.R diagonalCropRows).length = n)
    (hN : (S.R (recovery (.control .replicas))).length = targets.length)
    (hqueue : S.R diagonalQueue = word++tail) (hfresh : DiagonalFresh S) :
    ∃ (Ds : List (ZMod s → GaussianInt)) (v' : HS tapes Q A U) (steps : ℕ),
      Ds.length = targets.length ∧ v'.user = v.user ∧
      steps ≤ completeDiagonalBatchCost S B p w u t a radius n targets.length ∧
      (∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (mk v S)+depth+
        (16*diagonalPreparationCost S B p w u t a radius n+
          (2*bulkSelectionCountsCost targets.length n w+(2*(6*(n*w)+6)+realWeightWorkspace C w n))))
        depth (completeDiagonalBatch hQ) (mk v S) steps
        (mk v' {S with R := (Function.update (Function.update S.R diagonalQueue tail)
          (diagonalRole .dst) ((Ds.reverse.flatMap (fun D => cstream A w
            (packedInterval (a+radius) n (diagonalProduct s t alpha p D))))++S.R (diagonalRole .dst)))})) ∧
      PackedIntervalOutput p w (a+radius) n
        (targets.reverse.map (fun z i => (dPrime s t (alpha : ℝ) i : ℂ)*z i))
        (6/(2 : ℝ)^p+error)
        (Ds.reverse.flatMap (fun D => cstream A w
          (packedInterval (a+radius) n (diagonalProduct s t alpha p D)))) := by
  obtain ⟨Ds,hlen,hword,hfits,haccuracy⟩ := hpacketOut.diagonal_fields (t := t)
    (by omega) hp hwordWidth (by omega : 1 ≤ alpha) hbudget hfit herror hmag
  obtain ⟨v',steps,hu',htime,hwithin⟩ := completeDiagonalBatch_exec (body := body)
    hQ hA u alpha B p w a radius n hs hst hfit hp halpha hsquare hbudget hw hroom Ds hfits C hpush
    v S tail hS hT hu hprec hprecision hpacket hB ha hradius hn
    (hN.trans hlen.symm)
    (by rw [hqueue,hword]; simp only [List.flatMap_def]) hfresh
  refine ⟨Ds,v',steps,hlen,hu',?_,?_,?_⟩
  · simpa only [hlen] using htime
  · simpa only [hlen] using hwithin
  · simpa only [List.flatMap_def] using haccuracy

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
