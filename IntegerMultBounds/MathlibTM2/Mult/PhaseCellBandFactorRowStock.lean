module

public import IntegerMultBounds.MathlibTM2.Fast.BandFactor
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBandBackwardStepStock
public import IntegerMultBounds.MathlibTM2.Fast.ResampBScanStock

/-! Factor-row updates reuse the existing backward-step numerical reserve.
Only linear record movement is added around that arithmetic contract. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {Proc U : Type} {body : Proc → Pr Proc T Q A U}
  {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

theorem band_facRow_runs_within (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w P B : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w P) (hw : 1 ≤ w)
    (hp : P ≤ w) (q : GaussianInt) (r : ℤ) (rs more col cols : List GaussianInt)
    (hrs : rs.length = 2 * B) (hcol : col.length = 2 * B) (hfq : Fits w q)
    (hfr : Fits w (⟨r, 0⟩ : GaussianInt)) (hfx : Fits w (tdivN P (q * ⟨r, 0⟩)))
    (hfc : ∀ a ∈ col, Fits w a ∧ a.im = 0) (D TB SR : List (Fin (A + 4)))
    (hvk : σ .vk = cstream A w (q :: (rs ++ more))) (htb : σ .tb = csyms A w ⟨r, 0⟩ ++ TB)
    (hef : σ .ef = cstream A w (col ++ cols)) (hsr : σ .sr = SR)
    (hmsk : σ .msk = csyms A w 0)
    (hdout : σ .dout = D) (hhv : σ .hv = []) (hya : σ .ya = []) (hxs : σ .xs = [])
    (hpr : σ .pr = []) (hnv : σ .nv = []) (hac : σ .ac = []) (hac2 : σ .ac2 = [])
    (htC : σ .tC = []) (htA : σ .tA = []) (htJ : σ .tJ = []) (hb1 : σ .b1 = [])
    (hxa : σ .xa = []) (hhc : σ .hc = [])
    (hm2n : (σ .m2n).length = 2 * B) (hmwn : (σ .mwn).length = 2 * B * w)
    (K L : ℕ)
    (hpushK : mnProgPush (rmulOne (P := Proc) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg .hv .xa .hc)) ≤ K)
    (hpushL : mnProgPush (rmulOne (P := Proc) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg .ya .xs .pr)) ≤ L) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι) (bandFacRowP rg hι hT hQ) σ
      (Function.update (Function.update (Function.update (Function.update (Function.update σ .vk
        (cstream A w more)) .tb TB) .ef (cstream A w cols)) .dout
        (csyms A w (tdivN P (q * ⟨r, 0⟩)) ++ D)) .sr
        ((cstream A w (List.zipWith (· - ·) rs
          (List.zipWith (fun a b => tdivN P (a * b))
            (List.replicate (2 * B) (tdivN P (q * ⟨r, 0⟩))) col) ++ [0])).reverse ++ SR))
      (bandFacRowCost w B)
      (((realWeightWorkspace K w 1+1000*(w+1))+
        (realWeightWorkspace L w (2*B)+1000*(2*B+1)*(w+1)))+100*(B+1)*(w+1)) := by
  set rs' := List.zipWith (· - ·) rs (List.zipWith (fun a b => tdivN P (a * b))
    (List.replicate (2 * B) (tdivN P (q * ⟨r, 0⟩))) col) with hrs'
  have hrs'l : rs'.length = 2 * B := by simp [hrs', hrs, hcol]
  have h₁ := band_bwdStep_runs_within (body := body) (ι := ι) (w := w) (B := 2 * B) hrg hdisj hι
    hT hQ hA σ hready hw hp q r rs more col cols hrs hcol hfq hfr hfx hfc D TB hvk htb hef hdout
    hhv hya hxs hpr hnv hac hac2 htC htA htJ hb1 hxa hhc hm2n hmwn K L hpushK hpushL
  rw [← hrs'] at h₁
  set σ₁ := Function.update (Function.update (Function.update (Function.update σ .vk
    (cstream A w (rs' ++ more))) .tb TB) .ef (cstream A w cols)) .dout
    (csyms A w (tdivN P (q * ⟨r, 0⟩)) ++ D)
  have h₂ := rsb_mv_runs (body := body) (ι := ι) hrg (c := .mwn) (t := .tC) (x := .vk) (y := .sr)
    (by decide) σ₁ (by simp [σ₁, htC]) (by simp [σ₁, hmwn, hrs'l])
  have hmw : (σ₁ .mwn).length = rs'.length * w := by simp [σ₁, hmwn, hrs'l]
  rw [hmw] at h₂
  simp only [σ₁, Function.update_of_ne (by decide : RsbR.vk ≠ RsbR.dout),
    Function.update_of_ne (by decide : RsbR.vk ≠ RsbR.ef),
    Function.update_of_ne (by decide : RsbR.vk ≠ RsbR.tb), Function.update_self,
    Function.update_of_ne (by decide : RsbR.sr ≠ RsbR.dout),
    Function.update_of_ne (by decide : RsbR.sr ≠ RsbR.ef),
    Function.update_of_ne (by decide : RsbR.sr ≠ RsbR.tb),
    Function.update_of_ne (by decide : RsbR.sr ≠ RsbR.vk), hsr, cstream_append,
    take_cstream rs' rs'.length le_rfl, drop_cstream, List.take_length, List.drop_length,
    Nat.sub_self, zero_mul, List.drop_zero, cstream_nil, List.nil_append] at h₂
  set σ₂ := Function.update (Function.update σ₁ .vk (cstream A w more)) .sr
    ((cstream A w rs').reverse ++ SR)
  have h₃ := rsb_copyR_runs (body := body) (ι := ι) hrg (a := .msk) (b := .sr) (t := .tC)
    (by decide) (by decide) (by decide) σ₂ (by simp [σ₂, σ₁, htC])
  have h₂w := h₂.within_native (rsbMv_native _ _ _ _)
  have h₃w := h₃.within_native (show mnNativePushBound 2
      (copyR (P := Proc) (Q := Q) (A := A) (U := U) (rg .msk) (rg .sr) (rg .tC) id) from by
    simp [copyR,copyStep,moveR,whileR,moveStep,peekR,mnNativePushBound,mnActPush])
  have h₂' := h₂w.congr_pre (σ := σ₁) (by simp only [σ₁, cstream_append])
  refine ((RsbRunsWithin.seq hdisj h₁ (RsbRunsWithin.seq hdisj (h₂'.congr ?_) h₃w)).congr ?_).mono ?_ ?_
  · simp only [σ₂, σ₁, cstream_append]
  · funext x; cases x <;> simp [σ₂, σ₁, hmsk, cstream_append, List.reverse_append]
  · simp [σ₂, σ₁, hmsk, bandFacRowCost, hrs'l, csyms]
    nlinarith

  · simp [σ₂,σ₁,hmsk,csyms,hrs'l]
    nlinarith only [Nat.zero_le (B*w)]


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
