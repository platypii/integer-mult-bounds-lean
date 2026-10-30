module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedHaloScatter
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComplexHaloScatter

/-! Complex accuracy at the protected length-class publication boundary.
Counter setup, the sweep and release execute in the existing fixed program. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {U P : Type} {body : P → Pr P 144 Q A U}

theorem protectedHaloScatter_complex_exec {s t : ℕ} [NeZero s] (hst : s < t) (band a b L q w : ℕ) (hwpos : 1 ≤ w)
    (hgroup : 0 < (haloLengthGroup s t band a b L).length)
    (E ys sourceTail outputTail : List (Fin (A+4)))
    (hE : E.length = s*w) (hys : ys.length = (haloLengthGroup s t band a b L).length*(L*w))
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hL : (S.R 128).length = L) (hw : (S.R 130).length = w)
    (hc : S.R 140 = gatherControls A (haloScatterGaps s t band a b L w))
    (hdst : S.R 132 = E++outputTail) (hsrc : S.R 93 = ys++sourceTail)
    (hz : ∀ k ∈ [(88 : Fin 144),89,90,92,94,131,134,135], S.R k = [])
    (x : ZMod s → ℂ) (error : ℝ)
    (hlocal : ∀ n : Fin (haloLengthGroup s t band a b L).length, ∀ i : Fin L,
      ‖value q (decodeWord (((ys++sourceTail).drop ((n.val*L+i.val)*w)).take w)) -
        x (haloGroupOrigin s t band a b L n+(i.val : ZMod s))‖ ≤ error) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 54*s*w+15 ∧
      Exec body protectedScatter (mk v S) n
        (mk v' { S with R := (Function.update (Function.update (Function.update S.R 93 sourceTail)
          132 (scatterRows (L*w) E (ys++sourceTail) (haloScatterGaps s t band a b L w)++outputTail)) 140 []) }) ∧
      ∀ k : Fin (haloLengthGroup s t band a b L).length,
        PhaseCellInterface.ErrorOn (publishedCellCore (haloGroupOrigin s t band a b L k) L)
          (pairedCellRead q w (scatterRows (L*w) E (ys++sourceTail)
            (haloScatterGaps s t band a b L w)++outputTail)) x error := by
  obtain ⟨v',n,hu,hn,he⟩ := protectedHaloScatter_exec (body := body) hst band a b L w hwpos hgroup
    E ys sourceTail outputTail hE hys v S hL hw hc hdst hsrc hz
  refine ⟨v',n,hu,hn,he,?_⟩
  have hf := haloScatterGaps_fits s t band a b L w E (by omega)
  have hgood := haloScatterRows_complex_errorOn t band a b L q w (E++outputTail) (ys++sourceTail)
    (by simp only [List.length_append]; omega)
    (by simp only [List.length_append,hys]; omega) x error hlocal
  simpa only [scatterRows_append (L*w) (haloScatterGaps s t band a b L w) E
    (ys++sourceTail) outputTail hf] using hgood

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
