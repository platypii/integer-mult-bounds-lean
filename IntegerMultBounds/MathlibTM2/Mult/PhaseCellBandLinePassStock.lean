module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBandForwardLoopStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBandBackwardLoopStock

/-! One complete forward column shares a numerical reserve and pays only linear
native traffic around it. Numerical correctness remains the existing band contract. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

theorem band_linePass_runs_within (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w p B s : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w p) (hw : 1 ≤ w)
    (hp : p ≤ w) (Lc Uc : List (List ℤ)) (rcs : List ℤ) (hLc : Lc.length = s) (hUc : Uc.length = s)
    (hLl : ∀ c ∈ Lc, c.length = B) (hUl : ∀ c ∈ Uc, c.length = B) (hrcs : rcs.length = s)
    (b : List GaussianInt) (hb : b.length = s)
    (hfL : ∀ c ∈ Lc, ∀ x ∈ c, Fits w (⟨x, 0⟩ : GaussianInt))
    (hfU : ∀ c ∈ Uc, ∀ x ∈ c, Fits w (⟨x, 0⟩ : GaussianInt))
    (hfr : ∀ x ∈ rcs, Fits w (⟨x, 0⟩ : GaussianInt))
    (hfit₁ : ∀ j < s, Fits w ((Mult.BandList.bandPend p Lc (b ++ List.replicate B 0) j).headD 0))
    (hfit₂ : ∀ j < s, Fits w ((Mult.BandList.bandPendB p Uc rcs
      ((Mult.BandList.fwdZC p Lc (b ++ List.replicate B 0)).reverse ++ List.replicate B 0) j).headD 0))
    (hfit₃ : ∀ j < s, Fits w (tdivN p ((Mult.BandList.bandPendB p Uc rcs
      ((Mult.BandList.fwdZC p Lc (b ++ List.replicate B 0)).reverse ++ List.replicate B 0) j).headD 0 *
        ⟨rcs.getD j 0, 0⟩)))
    (hvk : σ .vk = cstream A w (b ++ List.replicate B 0))
    (hbo : σ .bo = cstream A w (Lc.map colC).flatten) (hhf : σ .hf = cstream A w (Uc.map colC).flatten)
    (hdf : σ .df = cstream A w (rcs.map fun x => (⟨x, 0⟩ : GaussianInt)))
    (hef : σ .ef = []) (htb : σ .tb = []) (hdout : σ .dout = [])
    (hhv : σ .hv = []) (hya : σ .ya = []) (hxs : σ .xs = [])
    (hpr : σ .pr = []) (hnv : σ .nv = []) (hac : σ .ac = []) (hac2 : σ .ac2 = [])
    (htC : σ .tC = []) (htA : σ .tA = []) (htJ : σ .tJ = []) (hb1 : σ .b1 = [])
    (htL : σ .tL = []) (hsn : (σ .sn).length = s) (hxa : σ .xa = []) (hhc : σ .hc = [])
    (hm2n : (σ .m2n).length = B) (hmwn : (σ .mwn).length = B * w)
    (K L : ℕ)
    (hpushK : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg .hv .xa .hc)) ≤ K)
    (hpushL : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg .ya .xs .pr)) ≤ L) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι) (bandLinePassP rg hι hT hQ) σ
      (Function.update (Function.update σ .vk []) .dout
        (cstream A w (Mult.BandList.bwdZC p Uc rcs
          ((Mult.BandList.fwdZC p Lc (b ++ List.replicate B 0)).reverse ++ List.replicate B 0)).reverse))
      (bandLinePassCost w s B)
      (2*realWeightWorkspace L w B+realWeightWorkspace K w 1+10000*(s+1)*(B+1)*(w+1)) := by
  set pend := b ++ List.replicate B (0 : GaussianInt) with hpend
  have hpl : pend.length = s + B := by simp [hpend, hb]
  have h₁ := rsb_copyTo_runs (body := body) (ι := ι) hrg hdisj (a := .bo) (b := .ef)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) σ hb1 htC
  set σ₁ := Function.update σ .ef (σ .bo ++ σ .ef)
  have hready₁ : RsbReady σ₁ w p := hready.update .ef (fun c => by simp) _
  have h₂ := band_fwdLoop_runs_within (body := body) (ι := ι) (w := w) (B := B) (s := s) hrg hdisj hι
    hT hQ hA σ₁ hready₁ hw hp Lc hLc hLl pend hpl hfit₁ hfL []
    (by simp [σ₁, hvk]) (by simp [σ₁, hbo, hef]) (by simp [σ₁, hdout]) (by simp [σ₁, hhv])
    (by simp [σ₁, hya]) (by simp [σ₁, hxs]) (by simp [σ₁, hpr]) (by simp [σ₁, hnv])
    (by simp [σ₁, hac]) (by simp [σ₁, hac2]) (by simp [σ₁, htC]) (by simp [σ₁, htA])
    (by simp [σ₁, htJ]) (by simp [σ₁, hb1]) (by simp [σ₁, htL]) (by simp [σ₁, hsn])
    (by simp [σ₁, hm2n]) (by simp [σ₁, hmwn]) L hpushL
  set σ₂ := Function.update (Function.update (Function.update σ₁ .vk
    (cstream A w (Mult.BandList.bandPend p Lc pend s))) .ef []) .dout
    (cstream A w (Mult.BandList.bandOut p Lc pend s) ++ [])
  have h₃ := rsb_emptyR_runs (body := body) (ι := ι) hrg .vk σ₂
  set σ₃ := Function.update σ₂ .vk []
  have h₄ := rsb_umulSym_runs (body := body) (ι := ι) hrg (pairSym A false false) (c := .mwn) (a := .vk)
    (t := .tC) (by decide) (by decide) (by decide) σ₃ (by simp [σ₃, σ₂, σ₁, htC])
  set σ₄ := Function.update σ₃ .vk (List.replicate (σ₃ .mwn).length (pairSym A false false) ++ σ₃ .vk)
  have h₅ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .dout) (b := .ac2) (by decide) σ₄
  set σ₅ := Function.update (Function.update σ₄ .dout []) .ac2 ((σ₄ .dout).reverse ++ σ₄ .ac2)
  have h₆ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := .vk) (by decide) σ₅
  set σ₆ := Function.update (Function.update σ₅ .ac2 []) .vk ((σ₅ .ac2).reverse ++ σ₅ .vk)
  have h₇ := rsb_copyTo_runs (body := body) (ι := ι) hrg hdisj (a := .hf) (b := .ef)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) σ₆ (by simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hb1])
    (by simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htC])
  set σ₇ := Function.update σ₆ .ef (σ₆ .hf ++ σ₆ .ef)
  have h₈ := rsb_copyTo_runs (body := body) (ι := ι) hrg hdisj (a := .df) (b := .tb)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) σ₇
    (by simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hb1]) (by simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htC])
  set σ₈ := Function.update σ₇ .tb (σ₇ .df ++ σ₇ .tb)
  have hfz : Mult.BandList.bandOut p Lc pend s = (Mult.BandList.fwdZC p Lc pend).reverse := by
    rw [Mult.BandList.fwdZC_eq_bandOut p Lc pend (by omega), hLc, List.reverse_reverse]
  set pend' := (Mult.BandList.fwdZC p Lc pend).reverse ++ List.replicate B (0 : GaussianInt)
  have hpl' : pend'.length = s + B := by
    simp [pend', length_fwdZC p Lc pend (by omega), hLc]
  have hready₈ : RsbReady σ₈ w p := by
    simp only [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂]
    exact (((((((((hready₁.update .vk (fun c => by simp) _).update .ef (fun c => by simp) _).update
      .dout (fun c => by simp) _).update .vk (fun c => by simp) _).update .vk (fun c => by simp)
      _).update .dout (fun c => by simp) _).update .ac2 (fun c => by simp) _).update .ac2
      (fun c => by simp) _).update .vk (fun c => by simp) _).update .ef (fun c => by simp) _ |>.update
      .tb (fun c => by simp) _
  have hz : List.replicate (σ .mwn).length (pairSym A false false) = cstream A w (List.replicate B 0) := by
    rw [cstream_replicate_zero, hmwn]
  have h₉ := band_bwdLoop_runs_within (body := body) (ι := ι) (w := w) (B := B) (s := s) hrg hdisj hι
    hT hQ hA σ₈ hready₈ hw hp Uc hUc hUl rcs hrcs hfr pend' hpl' hfit₂ hfit₃ hfU []
    (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hfz, hz, pend', hac2, cstream_append])
    (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hhf])
    (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁]) (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hhv])
    (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hya]) (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hxs])
    (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hpr]) (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hnv])
    (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hac]) (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hac2])
    (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htC]) (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htA])
    (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htJ]) (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hb1])
    (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htL]) (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hsn])
    (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hxa]) (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hhc])
    (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hdf, htb])
    (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hm2n]) (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hmwn]) K L hpushK hpushL
  set σ₉ := Function.update (Function.update (Function.update (Function.update σ₈ .vk
    (cstream A w (Mult.BandList.bandPendB p Uc rcs pend' s))) .tb []) .ef []) .dout
    (cstream A w (Mult.BandList.bandOutB p Uc rcs pend' s) ++ [])
  have h₁₀ := rsb_emptyR_runs (body := body) (ι := ι) hrg .vk σ₉
  have hmove (a b : RsbR) : mnNativePushBound 2
      (moveR (P := P) (Q := Q) (A := A) (U := U) (rg a) (rg b) id) := by
    simp [moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  have hempty : mnNativePushBound 2 (emptyR (P := P) (Q := Q) (A := A) (U := U) (rg .vk)) := by
    simp [emptyR,emptyStep,whileR,peekR,mnNativePushBound,mnActPush]
  have h₁ := h₁.within_native (rsbCopyTo_native .bo .ef)
  have h₃ := h₃.within_native hempty
  have h₄ := h₄.within_native (show mnNativePushBound 2
    (umulSym (P := P) (Q := Q) (A := A) (U := U) 1 (pairSym A false false) (rg .mwn) (rg .vk) (rg .tC)) by
      simp [umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush])
  have h₅ := h₅.within_native (hmove .dout .ac2)
  have h₆ := h₆.within_native (hmove .ac2 .vk)
  have h₇ := h₇.within_native (rsbCopyTo_native .hf .ef)
  have h₈ := h₈.within_native (rsbCopyTo_native .df .tb)
  have h₁₀ := h₁₀.within_native hempty
  refine ((RsbRunsWithin.seq hdisj h₁ (RsbRunsWithin.seq hdisj h₂ (RsbRunsWithin.seq hdisj h₃ (RsbRunsWithin.seq hdisj h₄
    (RsbRunsWithin.seq hdisj h₅ (RsbRunsWithin.seq hdisj h₆ (RsbRunsWithin.seq hdisj h₇ (RsbRunsWithin.seq hdisj h₈
    (RsbRunsWithin.seq hdisj h₉ h₁₀))))))))).congr ?val).mono ?time ?space
  case time =>
    simp [σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hbo, hhf, hdf, hef, htb, hac2, hmwn,
      length_bandOut, Mult.BandList.length_bandPend, Mult.BandList.length_bandPendB, hpl, hpl',
      bandLinePassCost, List.length_flatten, hrcs]
    have hsL : (List.map (List.length ∘ colC) Lc).sum = s * B := by
      rw [List.map_congr_left (g := fun _ => B) (fun c hc => by simp [colC, hLl c hc]),
        List.map_const', List.sum_replicate, hLc, smul_eq_mul]
    have hsU : (List.map (List.length ∘ colC) Uc).sum = s * B := by
      rw [List.map_congr_left (g := fun _ => B) (fun c hc => by simp [colC, hUl c hc]),
        List.map_const', List.sum_replicate, hUc, smul_eq_mul]
    rw [hsL, hsU]
    omega
  case val =>
    have hbz : Mult.BandList.bandOutB p Uc rcs pend' s = (Mult.BandList.bwdZC p Uc rcs pend').reverse := by
      rw [Mult.BandList.bwdZC_eq_bandOutB p Uc rcs pend' (by omega) (by omega), hUc, List.reverse_reverse]
    funext x; cases x <;> simp [σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hbz, hef, htb, hac2]
  case space =>
    simp [σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hbo, hhf, hdf, hef, htb, hac2, hmwn,
      length_bandOut, Mult.BandList.length_bandPend, Mult.BandList.length_bandPendB, hpl, hpl',
      List.length_flatten, hrcs]
    have hsL : (List.map (List.length ∘ colC) Lc).sum = s * B := by
      rw [List.map_congr_left (g := fun _ => B) (fun c hc => by simp [colC, hLl c hc]),
        List.map_const', List.sum_replicate, hLc, smul_eq_mul]
    have hsU : (List.map (List.length ∘ colC) Uc).sum = s * B := by
      rw [List.map_congr_left (g := fun _ => B) (fun c hc => by simp [colC, hUl c hc]),
        List.map_const', List.sum_replicate, hUc, smul_eq_mul]
    rw [hsL, hsU]
    nlinarith

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
