module

public import IntegerMultBounds.MathlibTM2.Fast.BandTransposeStock

/-! Organization is native linear traffic in the factor archives and window. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {Proc U : Type} {body : Proc → Pr Proc T Q A U}
  {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

theorem bandAxisOrgP_native :
    mnNativePushBound 2 (bandAxisOrgP (P := Proc) (Q := Q) (A := A) (U := U) rg) := by
  have hempty (a : Fin T) : mnNativePushBound 2 (emptyR (P := Proc) (Q := Q) (A := A) (U := U) a) := by
    simp [emptyR, emptyStep, whileR, peekR, mnNativePushBound, mnActPush]
  have hmove (a b : Fin T) : mnNativePushBound 2 (moveR (P := Proc) (Q := Q) (A := A) (U := U) a b id) := by
    simp [moveR, moveStep, whileR, peekR, mnNativePushBound, mnActPush]
  have hrev (x y c n tn : RsbR) :
      mnNativePushBound 2 (bandRevP (P := Proc) (Q := Q) (A := A) (U := U) rg x y c n tn) :=
    rsbRep_native _ _ ⟨rsbMv_native .., hmove _ _⟩
  exact ⟨hempty _, rsbCopyTo_native .., hempty _, rsbRep_native _ _ (rsbCopyTo_native ..),
    hrev .., hrev .., rsbRep_native _ _ (rsbCopyTo_native ..),
    rsbRep_native _ _ (rsbCopyTo_native ..), hempty _, hempty _, rsbCopyTo_native ..,
    hempty _, rsbCopyTo_native .., rsbCopyTo_native ..⟩

theorem band_axisOrg_runs_within (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {w k s : ℕ}
    (σ : RsbR → List (Fin (A + 4))) (Lf : List ℤ) (hLf : Lf.length = s * (k + 1))
    (Ur : List (List ℤ)) (hUr : Ur.length = s) (hrow : ∀ row ∈ Ur, row.length = 2 * (k + 1) + 1)
    (SRC : List (Fin (A + 4)))
    (hdout : σ .dout = cstream A w ((Lf.map fun x => (⟨x, 0⟩ : GaussianInt)).reverse))
    (hhf : σ .hf = cstream A w (Ur.map colC).reverse.flatten) (hsrc : σ .src = SRC)
    (hbo : σ .bo = []) (hvk : σ .vk = []) (hxs : σ .xs = []) (hmsk : σ .msk = csyms A w 0)
    (hms : (σ .ms).length = k + 1) (hsn : (σ .sn).length = s)
    (hsmwn : (σ .smwn).length = (2 * (k + 1) + 1) * w) (hwn : (σ (.cm .wn)).length = w)
    (htK : σ .tK = []) (htL : σ .tL = []) (hsel : σ .sel = []) (htC : σ .tC = []) (hb1 : σ .b1 = [])
    (hac2 : σ .ac2 = []) {K : ℕ} (hm2n : (σ .m2n).length = 2 * (k + 1)) (hkn : (σ .kn).length = K)
    (hmwn : (σ .mwn).length = 2 * (k + 1) * w) (hm2wn : (σ .m2wn).length = k * w)
    (hdst : (σ .dst).length = k) (hw : 1 ≤ w) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι) (bandAxisOrgP rg) σ
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update σ
        .m2n (σ .ms)) .kn ((List.replicate s (σ .ms)).flatten)) .dout [])
        .bo (cstream A w (Lf.map fun x => (⟨x, 0⟩ : GaussianInt)))) .hf [])
        .src (cstream A w (Ur.map colC).flatten ++ SRC))
        .vk ((List.replicate (k + 1) ((List.replicate (k + 1) (csyms A w 0)).flatten)).flatten))
        .ms (σ .dst)) .mwn (σ (.cm .wn) ++ σ .m2wn)) (bandAxisOrgCost s k w K) (2*bandAxisOrgCost s k w K) := by
  exact (band_axisOrg_runs hrg hdisj σ Lf hLf Ur hUr hrow SRC hdout hhf hsrc hbo hvk hxs
    hmsk hms hsn hsmwn hwn htK htL hsel htC hb1 hac2 hm2n hkn hmwn hm2wn hdst hw).within_native
    bandAxisOrgP_native

end IntegerMultBounds.MathlibTM2.Fast
