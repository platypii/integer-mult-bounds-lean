module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightStreamStock
public import IntegerMultBounds.MathlibTM2.Host.AutoStock

/-! Coupling row products share the weighting-stream reserve; accumulation is native linear traffic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem subtractRow_native {T Q A : ℕ} {P U : Type} (acc terms saved width tmp : Fin T) :
    mnNativePushBound 2 (subtractRow (P := P) (Q := Q) (A := A) (U := U) acc terms saved width tmp) := by
  have hs : mnNativePushBound 2 (subtractRowStep (P := P) (Q := Q) (A := A) (U := U) acc terms saved width tmp) := by
    refine ⟨⟨by simp [mnNativePushBound,mnActPush],
      autoWord_native _ _ _ _ _ _ _ (by decide) (by decide)⟩,?_⟩
    simp [moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  simpa [subtractRow,peekR,mnNativePushBound,mnActPush] using hs

namespace ScalarPlacement
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

theorem fixedPointRowPrepared_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q w : ℕ} (hw : 1 ≤ w) (hqw : q ≤ w) (xs as : List GaussianInt) (hlen : xs.length = as.length)
    (hxs : ∀ x ∈ xs, Fits w x) (has : ∀ a ∈ as, Fits w a ∧ a.im = 0)
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ C)
    (v : HS 117 Q A U) (S : Stacks 117 A) (rhs : GaussianInt) (hc : CClean mul S)
    (hready : Ready (fun r => S.R (cr r)) w q)
    (hwork : ∀ r ∈ [CR.xsv, .ysv, .acc, .out], S.R (cr r) = []) (hwR : (S.R 94).length = w)
    (hx : S.R (cr .xs) = cstream A w xs) (hy : S.R (cr .ys) = cstream A w as)
    (hrhs : S.R 96 = csyms A w rhs) (hsaved : S.R 97 = []) (htmp : S.R 98 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ xs.length * (rmulCost w + 13 * w + 12) + 10 ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (realWeightWorkspace C w xs.length+2*(xs.length*(7*w+10)+2))) depth
        (integerRowPrepared hQ) (mk v S) m
        (mk v' { S with R := (Function.update S.R 96
          (csyms A w (rhs - (List.zipWith (fun x a => tdivN q (x*a)) xs as).sum))) }) := by
  let products := List.zipWith (fun x a => tdivN q (x*a)) xs as
  have hplen : products.length = xs.length := by simp [products, hlen]
  have hout : S.R (cr .out) = [] := hwork _ (by simp)
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := realWeightStream_exec_of_fits_within (body := body)
    cr_injective cr_mul mul_injective (by decide) hQ hA hw hqw
    xs as hlen hxs has v S hc hready hx hy (hwork _ (by simp)) (hwork _ (by simp)) (hwork _ (by simp))
  let S₁ : Stacks 117 A := { S with R := (Function.update S.R (cr .out)
    (cstream A w products ++ S.R (cr .out))) }
  obtain ⟨v₂, hu₂, he₂⟩ := subtractRow_exec (body := body) (w := w)
    (show [(96 : Fin 117), cr .out, 97, 94, 98].Nodup by decide) hA (by omega) products v₁ S₁ rhs
    (by simpa [S₁, cr, OutputPlacement.code] using hrhs)
    (by simp [S₁, hout])
    (by simpa [S₁, cr, OutputPlacement.code] using hsaved)
    (by simpa [S₁, cr, OutputPlacement.code] using hwR)
    (by simpa [S₁, cr, OutputPlacement.code] using htmp)
  refine ⟨v₂, m₁ + (products.length * (7 * w + 10) + 2), hu₂.trans hu₁, ?_,
    ?_⟩
  · rw [hplen]
    nlinarith only [hm₁]
  · intro depth
    have ht₁ := he₁ C hpush depth
    have ht₂ := mn_native_exec_within he₂ 2 (subtractRow_native ..) depth _ (Nat.le_refl _)
    have ht := mn_seq_within_add ht₁ ht₂
    refine (ht.mono (by intro d z hz; rw [hplen] at hz; omega)).cast rfl ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases ha : k = 96
    · subst k; simp [products]
    by_cases ho : k = cr .out
    · subst k
      simpa [S₁, cr, OutputPlacement.code] using hout.symm
    simp [S₁, ha, ho]

end ScalarPlacement
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
