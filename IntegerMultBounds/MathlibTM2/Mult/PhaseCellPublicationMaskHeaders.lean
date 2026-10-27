module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingSourceMaskHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationMaskHost


/-! Generate the complete interior mask from retained unary geometry headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def publicationMaskFromHeaders : Pr P₀ 117 Q A U :=
  couplingSourceMaskFromHeaders false

def publicationMaskFromHeadersCost (V s t band a b : ℕ) : ℕ :=
  couplingSourceMaskFromHeadersCost V s t band a b

theorem publicationMaskFromHeaders_exec {V s t band a b : ℕ} [NeZero s]
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (hbandSrc : (S.R 100).length = band) (haSrc : (S.R 101).length = a)
    (hbSrc : (S.R 103).length = b) (hindex : S.R 108 = [])
    (hVsrc : (S.R 115).length = V) (h106 : S.R 106 = [])
    (hblank : ∀ r : Fin 117, r.val < 31 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ publicationMaskFromHeadersCost V s t band a b ∧
      Exec body publicationMaskFromHeaders (mk v S) m
        (mk v' {S with R := Function.update S.R 109 (publicationMaskSymbols A s t band a b++S.R 109)}) := by
  simpa [publicationMaskFromHeaders,publicationMaskFromHeadersCost,publicationMaskSymbols] using
    couplingSourceMaskFromHeaders_exec false hst haS hbS hwide v S
      hsSrc htSrc hbandSrc haSrc hbSrc hindex hVsrc h106 hblank

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
