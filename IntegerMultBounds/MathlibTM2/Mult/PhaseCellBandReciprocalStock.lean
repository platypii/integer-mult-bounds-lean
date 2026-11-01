module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBandProductRunsStock

/-! One reciprocal row shares a numerical reserve and pays linear native traffic.
Its numerical correctness remains the existing band contract. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

theorem band_recip_runs_within (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w p : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w p) (hw : 1 ≤ w)
    (hp : p ≤ w) (q : GaussianInt) (r : ℤ) (VK TB : List (Fin (A + 4))) (hfq : Fits w q)
    (hfr : Fits w (⟨r, 0⟩ : GaussianInt))
    (hvk : σ .vk = csyms A w q ++ VK) (htb : σ .tb = csyms A w ⟨r, 0⟩ ++ TB)
    (hhv : σ .hv = []) (hxa : σ .xa = []) (hhc : σ .hc = []) (hac2 : σ .ac2 = [])
    (htC : σ .tC = [])
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg .hv .xa .hc)) ≤ C) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι) (bandRecipP rg hι hT hQ) σ
      (Function.update (Function.update σ .vk (csyms A w (tdivN p (q * ⟨r, 0⟩)) ++ VK)) .tb TB)
      (rmulCost w + 30 * w + 40) (realWeightWorkspace C w 1+1000*(w+1)) := by
  have hwn := hready.wn
  have h₁ := band_pop_runs (body := body) (ι := ι) hrg hdisj σ q VK hvk hhv hac2 htC hwn
  set σ₁ := Function.update (Function.update σ .vk VK) .hv (csyms A w q)
  have h₂ := rsb_mv_runs (body := body) (ι := ι) hrg (c := .cm .wn) (t := .tC) (x := .tb)
    (y := .ac2) (by decide) σ₁ (by simp [σ₁, htC]) (by simp [σ₁, hwn, htb])
  rw [show (σ₁ (.cm .wn)).length = w by simp [σ₁, hwn]] at h₂
  simp only [σ₁, Function.update_of_ne (by decide : RsbR.tb ≠ RsbR.hv),
    Function.update_of_ne (by decide : RsbR.tb ≠ RsbR.vk),
    Function.update_of_ne (by decide : RsbR.ac2 ≠ RsbR.hv),
    Function.update_of_ne (by decide : RsbR.ac2 ≠ RsbR.vk), htb, take_csyms_append,
    drop_csyms_append, hac2, List.append_nil] at h₂
  set σ₂ := Function.update (Function.update σ₁ .tb TB) .ac2 (csyms A w ⟨r, 0⟩).reverse
  have h₃ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := .xa) (by decide) σ₂
  set σ₃ := Function.update (Function.update σ₂ .ac2 []) .xa ((σ₂ .ac2).reverse ++ σ₂ .xa)
  have hready₃ : RsbReady σ₃ w p := by
    simp only [σ₃, σ₂, σ₁]
    exact (((((hready.update .vk (fun c => by simp) _).update .hv (fun c => by simp) _).update
      .tb (fun c => by simp) _).update .ac2 (fun c => by simp) _).update .ac2 (fun c => by simp)
      _).update .xa (fun c => by simp) _
  have h₄ := rsb_rmulStream_runs_within (body := body) hrg hdisj hι hT hQ hA bandFree_hv (ρ := σ₃)
    hready₃ hw hp [q] [⟨r, 0⟩] rfl (by simpa using hfq) (by simpa using hfr)
    (by simp [σ₃, σ₂, σ₁]) (by simp [σ₃, σ₂, σ₁, hxa]) C hpush
  set σ₄ := Function.update σ₃ .hc
    (cstream A w (List.zipWith (fun a b => tdivN p (a * b)) [q] [⟨r, 0⟩]) ++ σ₃ .hc)
  have h₅ := rsb_emptyR_runs (body := body) (ι := ι) hrg .hv σ₄
  have h₆ := rsb_emptyR_runs (body := body) (ι := ι) hrg .xa (Function.update σ₄ .hv [])
  set σ₆ := Function.update (Function.update σ₄ .hv []) .xa []
  have h₇ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .hc) (b := .ac2) (by decide) σ₆
  set σ₇ := Function.update (Function.update σ₆ .hc []) .ac2 ((σ₆ .hc).reverse ++ σ₆ .ac2)
  have h₈ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := .vk) (by decide) σ₇
  have hmove (a b : RsbR) : mnNativePushBound 2
      (moveR (P := P) (Q := Q) (A := A) (U := U) (rg a) (rg b) id) := by
    simp [moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  have hempty (r : RsbR) : mnNativePushBound 2
      (emptyR (P := P) (Q := Q) (A := A) (U := U) (rg r)) := by
    simp [emptyR,emptyStep,whileR,peekR,mnNativePushBound,mnActPush]
  have h₁ := h₁.within_native (bandPopP_native (rg := rg))
  have h₂ := h₂.within_native (rsbMv_native ..)
  have h₃ := h₃.within_native (hmove .ac2 .xa)
  have h₅ := h₅.within_native (hempty .hv)
  have h₆ := h₆.within_native (hempty .xa)
  have h₇ := h₇.within_native (hmove .hc .ac2)
  have h₈ := h₈.within_native (hmove .ac2 .vk)
  refine ((RsbRunsWithin.seq hdisj h₁ (RsbRunsWithin.seq hdisj h₂ (RsbRunsWithin.seq hdisj h₃
    (RsbRunsWithin.seq hdisj h₄ (RsbRunsWithin.seq hdisj h₅ (RsbRunsWithin.seq hdisj h₆
    (RsbRunsWithin.seq hdisj h₇ h₈))))))).congr ?_).mono ?_ ?_
  · funext x; cases x <;> simp [σ₇, σ₆, σ₄, σ₃, σ₂, σ₁, hhv, hxa, hhc, hac2]
  · simp [σ₇, σ₆, σ₄, σ₃, σ₂, σ₁, hxa, hhc, cstream]
    omega

  · simp [σ₇, σ₆, σ₄, σ₃, σ₂, σ₁, hxa, hhc, cstream, realWeightWorkspace]
    omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
