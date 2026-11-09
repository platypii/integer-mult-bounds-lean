module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBandFactorRowsStock
public import IntegerMultBounds.MathlibTM2.Fast.BandNewtonStock

/-! One factor window combines shared Newton and row-scan reserves with
native traffic proportional to the active window, independently of iteration count. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {Proc U : Type} {body : Proc → Pr Proc T Q A U}
  {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

theorem band_facStep_runs_within (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w P B K : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w P) (hw : 1 ≤ w)
    (hp : P ≤ w) (c : ℤ) (tail0 next : List ℤ) (rest : List (List ℤ))
    (htl : tail0.length = 2 * B) (hnext : next.length = 2 * B + 1)
    (hrest : rest.length = B) (hrow : ∀ row ∈ rest, row.length = 2 * B + 1)
    (hfc : Fits w (⟨c, 0⟩ : GaussianInt))
    (hfit : ∀ n < K, Fits w (⟨Mult.BandFactor.newtonZ P c n, 0⟩ : GaussianInt) ∧
      Fits w (⟨(c*Mult.BandFactor.newtonZ P c n).tdiv (2^P), 0⟩ : GaussianInt))
    (hfr : Fits w (⟨Mult.BandFactor.newtonZ P c K, 0⟩ : GaussianInt))
    (hft : ∀ a ∈ tail0, Fits w (⟨a, 0⟩ : GaussianInt))
    (hfh : ∀ row ∈ rest, Fits w (⟨row.headD 0, 0⟩ : GaussianInt) ∧
      Fits w (⟨facMul P (Mult.BandFactor.newtonZ P c K) row, 0⟩ : GaussianInt))
    (SRC HF DF D : List (Fin (A + 4)))
    (hvk : σ .vk = cstream A w (colC (c :: tail0) ++ (rest.map colC).flatten))
    (hsrc : σ .src = cstream A w (colC next) ++ SRC)
    (hhf : σ .hf = HF) (hdf : σ .df = DF) (hdout : σ .dout = D)
    (hbx : σ .bx = csyms A w ⟨Mult.BandFactor.newtonZ P c 0, 0⟩) (hmsk : σ .msk = csyms A w 0)
    (hef : σ .ef = []) (htb : σ .tb = []) (hsr : σ .sr = []) (hbo : σ .bo = [])
    (hhv : σ .hv = []) (hxa : σ .xa = []) (hhc : σ .hc = []) (hya : σ .ya = []) (hxs : σ .xs = [])
    (hpr : σ .pr = []) (hac : σ .ac = []) (hac2 : σ .ac2 = []) (hnv : σ .nv = [])
    (hb1 : σ .b1 = []) (htC : σ .tC = []) (htA : σ .tA = []) (htJ : σ .tJ = [])
    (htK : σ .tK = []) (htL : σ .tL = [])
    (hkn : (σ .kn).length = K) (hms : (σ .ms).length = B) (hm2n : (σ .m2n).length = 2 * B)
    (hmwn : (σ .mwn).length = 2 * B * w) (hsmwn : (σ .smwn).length = (2 * B + 1) * w)
    (J L : ℕ)
    (hpushJ : mnProgPush (rmulOne (P := Proc) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg .hv .xa .hc)) ≤ J)
    (hpushL : mnProgPush (rmulOne (P := Proc) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg .ya .xs .pr)) ≤ L) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι) (bandFacStepP rg hι hT hQ) σ
      (Function.update (Function.update (Function.update (Function.update (Function.update σ .vk
        (cstream A w ((rest.map fun row =>
          colC (facRow P (Mult.BandFactor.newtonZ P c K) tail0 row)).flatten ++ colC next)))
        .src SRC) .hf (cstream A w (colC (c :: tail0)) ++ HF))
        .df (csyms A w ⟨Mult.BandFactor.newtonZ P c K, 0⟩ ++ DF))
        .dout (cstream A w ((rest.map fun row =>
          (⟨facMul P (Mult.BandFactor.newtonZ P c K) row, 0⟩ : GaussianInt)).reverse) ++ D))
      (bandFacStepCost w B K)
      (1000*(B+1)*(B+1)*(w+1) +
       bandNewtonStepPush (P := Proc) (A := A) (U := U) rg hι hT hQ*bandNewtonStepCost w +
       ((realWeightWorkspace J w 1+1000*(w+1))+
        (realWeightWorkspace L w (2*B)+1000*(2*B+1)*(w+1)))) := by
  have hwn := hready.wn
  set r := Mult.BandFactor.newtonZ P c K with hr
  set RS := cstream A w (rest.map colC).flatten with hRS
  have htl' : (colC tail0).length = 2 * B := by simp [colC, htl]
  -- pop the pivot
  have h₁ := band_pop_runs (body := body) (ι := ι) hrg hdisj σ ⟨c, 0⟩
    (cstream A w (colC tail0) ++ RS) (by rw [hvk]; simp [colC, hRS]) hhv hac2 htC hwn
  set σ₁ := Function.update (Function.update σ .vk (cstream A w (colC tail0) ++ RS)) .hv
    (csyms A w ⟨c, 0⟩)
  -- the pivot tail to `bo`
  have h₂ := rsb_mv_runs (body := body) (ι := ι) hrg (c := .mwn) (t := .tC) (x := .vk) (y := .ac2)
    (by decide) σ₁ (by simp [σ₁, htC]) (by simp [σ₁, hmwn, htl'])
  have hmw : (σ₁ .mwn).length=(colC tail0).length * w := by simp [σ₁, hmwn, htl']
  rw [hmw] at h₂
  simp only [σ₁, Function.update_of_ne (by decide : RsbR.vk ≠ RsbR.hv), Function.update_self,
    Function.update_of_ne (by decide : RsbR.ac2 ≠ RsbR.hv),
    Function.update_of_ne (by decide : RsbR.ac2 ≠ RsbR.vk), take_cstream _ _ le_rfl,
    drop_cstream, List.take_length, List.drop_length, Nat.sub_self, zero_mul, List.drop_zero,
    cstream_nil, List.nil_append, hac2, List.append_nil] at h₂
  have h₂' := (h₂.within_native (rsbMv_native ..)).congr_pre (σ := σ₁) rfl
  set σ₂ := Function.update (Function.update σ₁ .vk RS) .ac2 (cstream A w (colC tail0)).reverse
  have h₃ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := .bo) (by decide) σ₂
  set σ₃ := Function.update (Function.update σ₂ .ac2 []) .bo ((σ₂ .ac2).reverse ++ σ₂ .bo)
  have hready₃ : RsbReady σ₃ w P := by
    simp only [σ₃, σ₂, σ₁]
    exact (((((hready.update .vk (fun c => by simp) _).update .hv (fun c => by simp) _).update
      .vk (fun c => by simp) _).update .ac2 (fun c => by simp) _).update .ac2 (fun c => by simp)
      _).update .bo (fun c => by simp) _
  -- Newton
  have h₄ := band_newton_runs_within (body := body) (ι := ι) (K := K) hrg hdisj hι hT hQ hA σ₃ hready₃ hw hp
    c hfc hfit (by simp [σ₃, σ₂, σ₁, hbx]) (by simp [σ₃, σ₂, σ₁]) (by simp [σ₃, σ₂, σ₁, hxa])
    (by simp [σ₃, σ₂, σ₁, hhc]) (by simp [σ₃, σ₂, σ₁, hya]) (by simp [σ₃, σ₂, σ₁, hxs])
    (by simp [σ₃, σ₂, σ₁, hpr]) (by simp [σ₃, σ₂, σ₁, hac]) (by simp [σ₃, σ₂, σ₁])
    (by simp [σ₃, σ₂, σ₁, hnv]) (by simp [σ₃, σ₂, σ₁, hb1]) (by simp [σ₃, σ₂, σ₁, htC])
    (by simp [σ₃, σ₂, σ₁, htA]) (by simp [σ₃, σ₂, σ₁, htK]) (by simp [σ₃, σ₂, σ₁, hkn])
  rw [← hr] at h₄
  set σ₄ := Function.update σ₃ .xa (csyms A w ⟨r, 0⟩)
  -- outputs
  have h₅ := rsb_copyTo_runs (body := body) (ι := ι) hrg hdisj (a := .bo) (b := .hf)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) σ₄ (by simp [σ₄, σ₃, σ₂, σ₁, hb1])
    (by simp [σ₄, σ₃, σ₂, σ₁, htC])
  set σ₅ := Function.update σ₄ .hf (σ₄ .bo ++ σ₄ .hf)
  have h₆ := rsb_copyTo_runs (body := body) (ι := ι) hrg hdisj (a := .hv) (b := .hf)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) σ₅ (by simp [σ₅, σ₄, σ₃, σ₂, σ₁, hb1])
    (by simp [σ₅, σ₄, σ₃, σ₂, σ₁, htC])
  set σ₆ := Function.update σ₅ .hf (σ₅ .hv ++ σ₅ .hf)
  have h₇ := rsb_copyTo_runs (body := body) (ι := ι) hrg hdisj (a := .xa) (b := .df)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) σ₆
    (by simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hb1]) (by simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htC])
  set σ₇ := Function.update σ₆ .df (σ₆ .xa ++ σ₆ .df)
  -- copies for the rows
  have h₈ := band_copyRep_runs (body := body) (ι := ι) hrg hdisj (a := .bo) (b := .ef)
    ⟨by decide, by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide, by decide⟩
    (by decide) (B := B) σ₇ (by simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hb1])
    (by simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htC]) (by simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htL])
    (by simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hms])
  set σ₈ := Function.update σ₇ .ef ((List.replicate B (σ₇ .bo)).flatten ++ σ₇ .ef)
  have h₉ := band_copyRep_runs (body := body) (ι := ι) hrg hdisj (a := .xa) (b := .tb)
    ⟨by decide, by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide, by decide⟩
    (by decide) (B := B) σ₈ (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hb1])
    (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htC]) (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htL])
    (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hms])
  set σ₉ := Function.update σ₈ .tb ((List.replicate B (σ₈ .xa)).flatten ++ σ₈ .tb)
  have h₁₀ := rsb_emptyR_runs (body := body) (ι := ι) hrg .hv σ₉
  have h₁₁ := rsb_emptyR_runs (body := body) (ι := ι) hrg .xa (Function.update σ₉ .hv [])
  have h₁₂ := rsb_emptyR_runs (body := body) (ι := ι) hrg .bo
    (Function.update (Function.update σ₉ .hv []) .xa [])
  set σ₁₂ := Function.update (Function.update (Function.update σ₉ .hv []) .xa []) .bo []
  have hready₁₂ : RsbReady σ₁₂ w P := by
    simp only [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄]
    exact ((((((((hready₃.update .xa (fun c => by simp) _).update .hf (fun c => by simp) _).update
      .hf (fun c => by simp) _).update .df (fun c => by simp) _).update .ef (fun c => by simp)
      _).update .tb (fun c => by simp) _).update .hv (fun c => by simp) _).update .xa
      (fun c => by simp) _).update .bo (fun c => by simp) _
  -- the rows
  have h₁₃ := band_facRows_runs_within (body := body) (ι := ι) (w := w) (B := B) hrg hdisj hι hT hQ hA
    σ₁₂ hready₁₂ hw hp r tail0 rest htl hrest hrow hfr hft hfh D [] []
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hRS])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htb, flatten_replicate_csyms])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hef, hbo, flatten_replicate_cstream])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hsr])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hmsk])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hdout])
    (by simp [σ₁₂]) (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hya])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hxs])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hpr])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hnv])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hac])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htC])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htA])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htJ])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hb1]) (by simp [σ₁₂])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hhc])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htL])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hms])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hm2n])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hmwn]) J L hpushJ hpushL
  set NR := cstream A w (rest.map fun row => colC (facRow P r tail0 row)).flatten
  set σ₁₃ := Function.update (Function.update (Function.update (Function.update (Function.update
    σ₁₂ .vk []) .tb []) .ef []) .dout (cstream A w ((rest.map fun row =>
      (⟨facMul P r row, 0⟩ : GaussianInt)).reverse) ++ D)) .sr (NR.reverse ++ [])
  -- the next input row
  have hnl : (colC next).length = 2 * B + 1 := by simp [colC, hnext]
  have h₁₄ := rsb_mv_runs (body := body) (ι := ι) hrg (c := .smwn) (t := .tC) (x := .src) (y := .sr)
    (by decide) σ₁₃ (by simp [σ₁₃, σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htC])
    (by simp [σ₁₃, σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hsmwn, hsrc, hnl])
  have hsw : (σ₁₃ .smwn).length=(colC next).length * w := by
    simp [σ₁₃, σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hsmwn, hnl]
  have hsrc₁₃ : σ₁₃ .src=cstream A w (colC next) ++ SRC := by
    simp [σ₁₃, σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hsrc]
  rw [hsw, hsrc₁₃, take_cstream _ _ le_rfl, drop_cstream, List.take_length, List.drop_length,
    Nat.sub_self, zero_mul, List.drop_zero, cstream_nil, List.nil_append] at h₁₄
  set σ₁₄ := Function.update (Function.update σ₁₃ .src SRC) .sr
    ((cstream A w (colC next)).reverse ++ σ₁₃ .sr)
  have h₁₅ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .sr) (b := .vk) (by decide) σ₁₄
  have h₁w := h₁.within_native (bandPopP_native)
  have h₃w := h₃.within_native (c := 2) (by simp [moveR, moveStep, whileR, peekR, mnNativePushBound, mnActPush])
  have h₅w := h₅.within_native (rsbCopyTo_native ..)
  have h₆w := h₆.within_native (rsbCopyTo_native ..)
  have h₇w := h₇.within_native (rsbCopyTo_native ..)
  have h₈w := h₈.within_native (rsbRep_native _ _ (rsbCopyTo_native ..))
  have h₉w := h₉.within_native (rsbRep_native _ _ (rsbCopyTo_native ..))
  have h₁₀w := h₁₀.within_native (c := 2) (by simp [emptyR, emptyStep, whileR, peekR, mnNativePushBound, mnActPush])
  have h₁₁w := h₁₁.within_native (c := 2) (by simp [emptyR, emptyStep, whileR, peekR, mnNativePushBound, mnActPush])
  have h₁₂w := h₁₂.within_native (c := 2) (by simp [emptyR, emptyStep, whileR, peekR, mnNativePushBound, mnActPush])
  have h₁₄w := h₁₄.within_native (rsbMv_native ..)
  have h₁₅w := h₁₅.within_native (c := 2) (by simp [moveR, moveStep, whileR, peekR, mnNativePushBound, mnActPush])
  refine ((RsbRunsWithin.seq hdisj h₁w (RsbRunsWithin.seq hdisj h₂' (RsbRunsWithin.seq hdisj h₃w
    (RsbRunsWithin.seq hdisj h₄ (RsbRunsWithin.seq hdisj h₅w (RsbRunsWithin.seq hdisj h₆w (RsbRunsWithin.seq hdisj h₇w
    (RsbRunsWithin.seq hdisj h₈w (RsbRunsWithin.seq hdisj h₉w (RsbRunsWithin.seq hdisj h₁₀w (RsbRunsWithin.seq hdisj h₁₁w
    (RsbRunsWithin.seq hdisj h₁₂w (RsbRunsWithin.seq hdisj h₁₃ (RsbRunsWithin.seq hdisj h₁₄w
    h₁₅w)))))))))))))).congr ?_).mono ?_ ?_
  · funext x; cases x <;> simp [σ₁₄, σ₁₃, σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hef, htb, hsr,
      hbo, hhv, hxa, hac2, hhf, hdf, NR, colC, List.reverse_append]
  · simp [σ₁₄, σ₁₃, σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hef, htb, hbo, 
      hhf, hdf, bandFacStepCost, csyms, colC, htl, NR, hRS]
    have hsum : (List.map (List.length ∘ fun row => List.map (fun x => (⟨x, 0⟩ : GaussianInt))
        (facRow P r tail0 row)) rest).sum=B*(2*B+1) := by
      rw [List.map_congr_left (g := fun _ => 2*B+1) (fun row hr => by
        simp [facRow, Mult.BandFactor.subRowZ, htl, hrow row hr]), List.map_const',
        List.sum_replicate, hrest, smul_eq_mul]
    rw [hsum, hnext]
    nlinarith only [hw, Nat.zero_le (B*w), Nat.zero_le (B*B*w)]

  · simp [σ₁₄, σ₁₃, σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hef, htb, hbo, 
      hhf, hdf,  csyms, colC, htl, NR, hRS]
    have hsum : (List.map (List.length ∘ fun row => List.map (fun x => (⟨x, 0⟩ : GaussianInt))
        (facRow P r tail0 row)) rest).sum=B*(2*B+1) := by
      rw [List.map_congr_left (g := fun _ => 2*B+1) (fun row hr => by
        simp [facRow, Mult.BandFactor.subRowZ, htl, hrow row hr]), List.map_const',
        List.sum_replicate, hrest, smul_eq_mul]
    rw [hsum, hnext]
    nlinarith only [hw, Nat.zero_le (B*w), Nat.zero_le (B*B*w)]


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
