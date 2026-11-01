module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBandProductRunsStock

/-! One complete forward column shares a numerical reserve and pays only linear
native traffic around it. Numerical correctness remains the existing band contract. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

theorem band_fwdStep_runs_within (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w p B : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w p) (hw : 1 ≤ w)
    (hp : p ≤ w) (y : GaussianInt) (rs more col cols : List GaussianInt) (hrs : rs.length = B)
    (hcol : col.length = B) (hfy : Fits w y) (hfc : ∀ a ∈ col, Fits w a ∧ a.im = 0)
    (D : List (Fin (A + 4)))
    (hvk : σ .vk = cstream A w (y :: (rs ++ more))) (hef : σ .ef = cstream A w (col ++ cols))
    (hdout : σ .dout = D) (hhv : σ .hv = []) (hya : σ .ya = []) (hxs : σ .xs = [])
    (hpr : σ .pr = []) (hnv : σ .nv = []) (hac : σ .ac = []) (hac2 : σ .ac2 = [])
    (htC : σ .tC = []) (htA : σ .tA = []) (htJ : σ .tJ = []) (hb1 : σ .b1 = [])
    (hm2n : (σ .m2n).length = B) (hmwn : (σ .mwn).length = B * w)
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg .ya .xs .pr)) ≤ C) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι) (bandFwdStepP rg hι hT hQ) σ
      (Function.update (Function.update (Function.update σ .vk
        (cstream A w (List.zipWith (· - ·) rs
          (List.zipWith (fun a b => tdivN p (a * b)) (List.replicate B y) col) ++ more)))
        .ef (cstream A w cols)) .dout (csyms A w y ++ D))
      (bandFwdStepCost w B) (realWeightWorkspace C w B+1000*(B+1)*(w+1)) := by
  have hwn := hready.wn
  set prods := List.zipWith (fun a b => tdivN p (a * b)) (List.replicate B y) col with hprods
  have hprl : prods.length = B := by simp [hprods, hcol]
  -- pop
  have h₁ := band_pop_runs (body := body) (ι := ι) hrg hdisj σ y (cstream A w (rs ++ more))
    (by rw [hvk, cstream_cons]) hhv hac2 htC hwn
  set σ₁ := Function.update (Function.update σ .vk (cstream A w (rs ++ more))) .hv (csyms A w y)
  -- record the head
  have h₂ := rsb_copyTo_runs (body := body) (ι := ι) hrg hdisj (a := .hv) (b := .dout)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) σ₁ (by simp [σ₁, hb1])
    (by simp [σ₁, htC])
  set σ₂ := Function.update σ₁ .dout (σ₁ .hv ++ σ₁ .dout)
  -- replicate
  have h₃ := band_rep_runs (body := body) (ι := ι) hrg hdisj (w := w) (B := B) σ₂ y
    (by simp [σ₂, σ₁]) (by simp [σ₂, σ₁, hya]) (by simp [σ₂, σ₁, hb1]) (by simp [σ₂, σ₁, htC])
    (by simp [σ₂, σ₁, htJ]) (by simp [σ₂, σ₁, hm2n])
  set σ₃ := Function.update σ₂ .ya (cstream A w (List.replicate B y))
  -- the column
  have h₄ := band_col_runs (body := body) (ι := ι) hrg hdisj (w := w) (B := B) σ₃ col cols hcol
    (by simp [σ₃, σ₂, σ₁, hef]) (by simp [σ₃, σ₂, σ₁, hxs]) (by simp [σ₃, σ₂, σ₁, hac2])
    (by simp [σ₃, σ₂, σ₁, htC]) (by simp [σ₃, σ₂, σ₁, hmwn])
  set σ₄ := Function.update (Function.update σ₃ .ef (cstream A w cols)) .xs (cstream A w col)
  -- the products
  have hready₄ : RsbReady σ₄ w p := by
    simp only [σ₄, σ₃, σ₂, σ₁]
    exact (((((hready.update .vk (fun c => by simp) _).update .hv (fun c => by simp) _).update
      .dout (fun c => by simp) _).update .ya (fun c => by simp) _).update .ef (fun c => by simp)
      _).update .xs (fun c => by simp) _
  have h₅ := rsb_rmulStream_runs_within (body := body) hrg hdisj hι hT hQ hA bandFree_ya (ρ := σ₄)
    hready₄ hw hp (List.replicate B y) col (by simp [hcol])
    (by intro a ha; rw [(List.mem_replicate.mp ha).2]; exact hfy) hfc
    (by simp [σ₄, σ₃]) (by simp [σ₄]) C hpush
  set σ₅ := Function.update σ₄ .pr (cstream A w prods ++ σ₄ .pr)
  have h₆ := rsb_emptyR_runs (body := body) (ι := ι) hrg .ya σ₅
  have h₇ := rsb_emptyR_runs (body := body) (ι := ι) hrg .xs (Function.update σ₅ .ya [])
  have h₈ := rsb_emptyR_runs (body := body) (ι := ι) hrg .hv
    (Function.update (Function.update σ₅ .ya []) .xs [])
  set σ₈ := Function.update (Function.update (Function.update σ₅ .ya []) .xs []) .hv []
  -- the updates
  have h₉ := band_subLoop_runs (body := body) (ι := ι) hrg hdisj hA (w := w) (B := B) σ₈ rs prods
    hrs hprl (cstream A w more) []
    (by simp [σ₈, σ₅, σ₄, σ₃, σ₂, σ₁, cstream_append])
    (by simp [σ₈, σ₅, σ₄, σ₃, σ₂, σ₁, hpr]) (by simp [σ₈, σ₅, σ₄, σ₃, σ₂, σ₁, hnv])
    (by simp [σ₈, σ₅, σ₄, σ₃, σ₂, σ₁, hac]) (by simp [σ₈, σ₅, σ₄, σ₃, σ₂, σ₁, hac2])
    (by simp [σ₈, σ₅, σ₄, σ₃, σ₂, σ₁, htC]) (by simp [σ₈, σ₅, σ₄, σ₃, σ₂, σ₁, htA])
    (by simp [σ₈, σ₅, σ₄, σ₃, σ₂, σ₁, htJ]) (by simp [σ₈, σ₅, σ₄, σ₃, σ₂, σ₁, hwn])
    (by simp [σ₈, σ₅, σ₄, σ₃, σ₂, σ₁, hm2n])
  set σ₉ := Function.update (Function.update (Function.update σ₈ .vk (cstream A w more)) .pr [])
    .nv (cstream A w (List.zipWith (· - ·) rs prods)).reverse
  have h₁₀ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .nv) (b := .vk) (by decide) σ₉
  have h₁ := h₁.within_native (bandPopP_native (rg := rg))
  have h₂ := h₂.within_native (rsbCopyTo_native .hv .dout)
  have h₃ := h₃.within_native (rsbRep_native _ _ (rsbCopyTo_native .hv .ya))
  have h₄ := h₄.within_native (bandColP_native (rg := rg))
  have hempty (r : RsbR) : mnNativePushBound 2 (emptyR (P := P) (Q := Q) (A := A) (U := U) (rg r)) := by
    simp [emptyR,emptyStep,whileR,peekR,mnNativePushBound,mnActPush]
  have h₆ := h₆.within_native (hempty .ya)
  have h₇ := h₇.within_native (hempty .xs)
  have h₈ := h₈.within_native (hempty .hv)
  have h₉ := h₉.within_native (rsbRep_native _ _ (bandSubP_native (rg := rg)))
  have h₁₀ := h₁₀.within_native (show mnNativePushBound 2
    (moveR (P := P) (Q := Q) (A := A) (U := U) (rg .nv) (rg .vk) id) by
      simp [moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush])
  refine ((RsbRunsWithin.seq hdisj h₁ (RsbRunsWithin.seq hdisj h₂ (RsbRunsWithin.seq hdisj h₃
    (RsbRunsWithin.seq hdisj h₄ (RsbRunsWithin.seq hdisj h₅ (RsbRunsWithin.seq hdisj h₆ (RsbRunsWithin.seq hdisj h₇
    (RsbRunsWithin.seq hdisj h₈ (RsbRunsWithin.seq hdisj h₉ h₁₀))))))))).congr ?_).mono ?_ ?_
  · funext r; cases r <;> simp [σ₉, σ₈, σ₅, σ₄, σ₃, σ₂, σ₁, hhv, hya, hxs, hpr, hnv, hdout,
      cstream_append]
  · simp [σ₉, σ₈, σ₅, σ₄, σ₃, σ₂, σ₁, bandFwdStepCost, hpr, hdout,
      hcol, hprl, cstream, sum_zipWith_const, hrs]
    nlinarith

  · simp [σ₉, σ₈, σ₅, σ₄, σ₃, σ₂, σ₁, hpr, hdout,
      hcol, hprl, cstream, sum_zipWith_const, hrs, realWeightWorkspace]
    nlinarith

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
