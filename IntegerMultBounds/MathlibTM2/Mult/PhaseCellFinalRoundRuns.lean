module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputRound
public import IntegerMultBounds.MathlibTM2.Fast.BandLineSpec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairComponentsAccuracy

/-! Final dyadic scaling and rounding use the linear signed word pass. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.MathlibTM2.Mult.ShortConv

/-- The final stream decodes to exactly the scaled, rounded complex field. -/
theorem finalRound_decoded {A w s : ℕ} [NeZero s] (hA : 4 ≤ A) (hw : 0 < w)
    (q p j : ℕ) (hp : p ≤ q) (G : ZMod s → GaussianInt)
    (tail : List (Fin (A+4))) (i : ZMod s) (hfit : Fits w (tdivN (q-p+j) (G i))) :
    pairedCellRead p w
      (cstream A w (chirpLine s (fun k => tdivN (q-p+j) (G k)))++tail) i =
      IntegerMultBounds.NLogN.rhoC p (((2 : ℂ)^j)⁻¹ *
        ⟨gv q (G i).re,gv q (G i).im⟩) := by
  rw [pairedCellRead_encodedField hA hw _ tail i hfit, rhoC_scale q p j hp]
  apply Complex.ext <;> simp only [value,rsbGrid,two_pow_complex,toComplex_div_re,toComplex_div_im]

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem finalRound_runs (hA : 4 ≤ A) {src dst tmp cW cS cE cD sp sg cy : Fin T}
    (hreg : [src,dst,tmp,cW,cS,cE,cD,sp,sg,cy].Nodup)
    (w q p j k : ℕ) (hw : 1 ≤ w) (hsize : q-p+j+k ≤ w)
    (xs : List GaussianInt) (hxs : ∀ z ∈ xs, Fits w z)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A w xs) (hdst : S.R dst = [])
    (hg : topShiftG tmp cW cS cE cD sp sg cy w (q-p+j) k S.R) :
    ∃ v', v'.user = v.user ∧
      Exec body (topPass src dst (topShiftWord src dst tmp cW cS cE cD sp sg cy))
        (mk v S) (1+(xs.length*(topShiftWordCost w (q-p+j) k+1)+1)+
          (2*(xs.length*k)+2))
        (mk v' {S with R := (Function.update S.R src
          (cstream A k (xs.map (tdivN (q-p+j)))))}) :=
  chirpRound_exec hA hreg w (q-p+j) k hw hsize xs hxs v S hsrc hdst hg

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
