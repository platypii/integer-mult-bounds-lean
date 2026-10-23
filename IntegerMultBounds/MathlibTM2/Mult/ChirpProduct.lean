module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpSetup
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvUnary

/-! # Execute one chirp correlation block from raw operands

The raw reversed input and shifted kernel are packed and multiplied by S1. Generate the
extraction counter from unary dimensions, return correlations in output order, then clear
the temporary full product. Only the destination changes; there is no execution oracle.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.Spec.SignedRingProduct

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}
  {rg : RpReg → Fin T} {ι : Fin 91 → Fin T}

/-- A complete block call, including all generated parameters and temporary-product cleanup. -/
noncomputable def chirpProduct (rg : RpReg → Fin T) (ι : Fin 91 → Fin T)
    (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q)
    (pR lR wR srcX padX srcY padY mR triples skip savedSkip recordSaved dst saved buf tmp : Fin T) :
    Pr P T Q A U :=
  .seq (fromUnary rg ι h hT hQ pR lR wR srcX padX srcY padY)
    (.seq (correlationFromUnary mR wR triples skip savedSkip recordSaved (rg .out) dst saved buf tmp)
      (uclear (rg .out)))

/-- Exact block cost before replacing S1 by its public linear bound. -/
def chirpProductCost (p l w m : ℕ) : ℕ :=
  unaryCost p l w (3 * m + 1) (4 * m) + 52 * m * w + 56 * m + 2 * (2 ^ l * w) + 26

theorem chirpProduct_exec (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {p l w m : ℕ} (hp : 1 ≤ p) (hw : p + 2 ≤ w) (hm : 1 ≤ m) (hl : 7 * m ≤ 2 ^ l)
    (x y : List GaussianInt) (hlenX : x.length = 3 * m + 1) (hlenY : y.length = 4 * m)
    (hX : ∀ z ∈ x, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (hY : ∀ z ∈ y, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (pR lR wR srcX padX srcY padY mR triples skip savedSkip recordSaved dst saved buf tmp : Fin T)
    (hin : [pR, lR, wR, rg .d0, rg .ta, rg .tb, rg .acc, rg .sv, rg .tmp].Nodup)
    (hreg : [srcX, padX, srcY, padY, rg .xs, rg .ys, rg .ta, rg .tb, rg .d0].Nodup)
    (haux : [pR, lR, wR, srcX, srcY, padX, padY].Nodup)
    (hoff : ∀ r, padX ≠ rg r ∧ padY ≠ rg r)
    (hpriv : ∀ j, padX ≠ ι j ∧ padY ≠ ι j)
    (hextract : [mR, wR, triples, skip, savedSkip, recordSaved, rg .out, dst, saved, buf, tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (hc : RpClean ι S)
    (hsrcX : S.R srcX = cstream A w x) (hsrcY : S.R srcY = cstream A w y)
    (hpadX : S.R padX = []) (hpadY : S.R padY = [])
    (hwn : (S.R (rg .wn)).length = w)
    (hempty : ∀ r ∈ [RpReg.xs, .ys, .sv, .ta, .tb, .acc, .tmp, .d0, .d1, .d2, .d3], S.R (rg r) = [])
    (hpR : (S.R pR).length = p) (hlR : (S.R lR).length = l) (hwR : (S.R wR).length = w)
    (hmR : (S.R mR).length = m) (hout : S.R (rg .out) = [])
    (htriples : S.R triples = []) (hskip : S.R skip = [])
    (hsavedSkip : S.R savedSkip = []) (hrecordSaved : S.R recordSaved = [])
    (hsaved : S.R saved = []) (hbuf : S.R buf = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ chirpProductCost p l w m ∧
      Exec body (chirpProduct rg ι h hT hQ pR lR wR srcX padX srcY padY
        mR triples skip savedSkip recordSaved dst saved buf tmp) (mk v S) n
        (mk v' { S with R := (Function.update S.R dst
          (cstream A w (correlationCoeffs m (List.ofFn (coeff p l x y))) ++ S.R dst)) }) := by
  have hextract' := hextract
  regs_ne hextract'
  have hx : x.length ≤ 2 ^ l := by omega
  have hy : y.length ≤ 2 ^ l := by omega
  have hxy : x.length + y.length ≤ 2 ^ l + 1 := by omega
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := fromUnary_exec (body := body) h hT hQ hA hp hw x y hx hy hxy
    hX hY pR lR wR srcX padX srcY padY hin hreg haux hoff hpriv v S hc hsrcX hsrcY hpadX hpadY
    hwn hempty hpR hlR hwR
  set zs := List.ofFn (coeff p l x y)
  set S₁ : Stacks T A := { S with R := Function.update S.R (rg .out) (cstream A w zs) }
  rw [hout, List.append_nil] at he₁
  have e (r : Fin T) (hr : r ≠ rg .out) : S₁.R r = S.R r := by simp [S₁, hr]
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := correlationFromUnary_exec (body := body) hextract m w zs
    (by simp [zs]; omega) v₁ S₁ []
    (by rw [e _ ‹mR ≠ rg .out›]; exact hmR)
    (by rw [e _ ‹wR ≠ rg .out›]; exact hwR)
    (by simp [S₁])
    (by rw [e _ ‹triples ≠ rg .out›]; exact htriples)
    (by rw [e _ ‹skip ≠ rg .out›]; exact hskip)
    (by rw [e _ ‹savedSkip ≠ rg .out›]; exact hsavedSkip)
    (by rw [e _ ‹recordSaved ≠ rg .out›]; exact hrecordSaved)
    (by rw [e _ ‹rg .out ≠ saved›.symm]; exact hsaved)
    (by rw [e _ ‹rg .out ≠ buf›.symm]; exact hbuf)
    (by rw [e _ ‹rg .out ≠ tmp›.symm]; exact htmp)
  set S₂ : Stacks T A := { S₁ with R := (Function.update S₁.R dst
    (cstream A w (correlationCoeffs m zs) ++ S₁.R dst)) }
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body (rg .out) v₂ S₂
  refine ⟨v₃, _, hu₃.trans (hu₂.trans hu₁), ?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · have hlen : (S₂.R (rg .out)).length = 2 ^ l * w := by
      simp [S₂, S₁, ‹rg .out ≠ dst›, zs]
    rw [hlen]
    rw [hlenX, hlenY] at hn₁
    unfold chirpProductCost
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    clear he₁ he₂ he₃ hu₁ hu₂ hu₃ e
    funext r
    by_cases ho : r = rg .out
    · subst r
      simp only [S₂, S₁, Function.update_self,
        Function.update_of_ne ‹rg .out ≠ dst›, hout]
    by_cases hd : r = dst
    · subst r
      simp only [S₂, S₁, Function.update_self,
        Function.update_of_ne ‹rg .out ≠ dst›.symm]
    · simp only [S₂, S₁, Function.update_of_ne ho, Function.update_of_ne hd]

/-- The full block wrapper adds only linear tape work to one packed-product bound. -/
theorem chirpProductCost_le (p l w m : ℕ) (hm : 1 ≤ m) (hl : 7 * m ≤ 2 ^ l) :
    chirpProductCost p l w m ≤ rpRecBound p l w + rpFixCost p l w + ldrHeaderCost p l w +
      34 * (2 ^ l * w) + 52 * m * w + 56 * m + 18 * l + 8 * w +
      2 * (header p (2 ^ l) w).length + 80 := by
  have h := unaryCost_le p l w (3 * m + 1) (4 * m) (by omega) (by omega)
  unfold chirpProductCost
  omega

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
