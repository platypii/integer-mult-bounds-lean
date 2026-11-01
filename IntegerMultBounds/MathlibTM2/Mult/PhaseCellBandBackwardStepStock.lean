module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBandForwardStepStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBandReciprocalStock

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

theorem band_bwdStep_runs_within (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w p B : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w p) (hw : 1 ≤ w)
    (hp : p ≤ w) (q : GaussianInt) (r : ℤ) (rs more col cols : List GaussianInt)
    (hrs : rs.length = B) (hcol : col.length = B) (hfq : Fits w q)
    (hfr : Fits w (⟨r, 0⟩ : GaussianInt)) (hfx : Fits w (tdivN p (q * ⟨r, 0⟩)))
    (hfc : ∀ a ∈ col, Fits w a ∧ a.im = 0) (D TB : List (Fin (A + 4)))
    (hvk : σ .vk = cstream A w (q :: (rs ++ more))) (htb : σ .tb = csyms A w ⟨r, 0⟩ ++ TB)
    (hef : σ .ef = cstream A w (col ++ cols))
    (hdout : σ .dout = D) (hhv : σ .hv = []) (hya : σ .ya = []) (hxs : σ .xs = [])
    (hpr : σ .pr = []) (hnv : σ .nv = []) (hac : σ .ac = []) (hac2 : σ .ac2 = [])
    (htC : σ .tC = []) (htA : σ .tA = []) (htJ : σ .tJ = []) (hb1 : σ .b1 = [])
    (hxa : σ .xa = []) (hhc : σ .hc = [])
    (hm2n : (σ .m2n).length = B) (hmwn : (σ .mwn).length = B * w)
    (K L : ℕ)
    (hpushK : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg .hv .xa .hc)) ≤ K)
    (hpushL : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg .ya .xs .pr)) ≤ L) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι) (bandBwdStepP rg hι hT hQ) σ
      (Function.update (Function.update (Function.update (Function.update σ .vk
        (cstream A w (List.zipWith (· - ·) rs
          (List.zipWith (fun a b => tdivN p (a * b)) (List.replicate B (tdivN p (q * ⟨r, 0⟩)))
            col) ++ more))) .tb TB) .ef (cstream A w cols)) .dout
        (csyms A w (tdivN p (q * ⟨r, 0⟩)) ++ D))
      (rmulCost w + 30 * w + 40 + bandFwdStepCost w B)
      ((realWeightWorkspace K w 1+1000*(w+1))+
        (realWeightWorkspace L w B+1000*(B+1)*(w+1))) := by
  obtain ⟨x, hx⟩ : ∃ x, x = tdivN p (q * ⟨r, 0⟩) := ⟨_, rfl⟩
  rw [← hx] at hfx ⊢
  have h₁ := band_recip_runs_within (body := body) (ι := ι) hrg hdisj hι hT hQ hA σ hready hw hp q r
    (cstream A w (rs ++ more)) TB hfq hfr (by rw [hvk, cstream_cons]) htb hhv hxa hhc hac2 htC K hpushK
  rw [← hx] at h₁
  set σ₁ := Function.update (Function.update σ .vk
    (csyms A w x ++ cstream A w (rs ++ more))) .tb TB
  have hready₁ : RsbReady σ₁ w p :=
    (hready.update .vk (fun c => by simp) _).update .tb (fun c => by simp) _
  have h₂ := band_fwdStep_runs_within (body := body) (ι := ι) (w := w) (p := p) (B := B) hrg hdisj hι hT
    hQ hA σ₁ hready₁ hw hp x rs more col cols hrs hcol hfx hfc D
    (by simp [σ₁, cstream_cons]) (by simp [σ₁, hef]) (by simp [σ₁, hdout]) (by simp [σ₁, hhv])
    (by simp [σ₁, hya]) (by simp [σ₁, hxs]) (by simp [σ₁, hpr]) (by simp [σ₁, hnv])
    (by simp [σ₁, hac]) (by simp [σ₁, hac2]) (by simp [σ₁, htC]) (by simp [σ₁, htA])
    (by simp [σ₁, htJ]) (by simp [σ₁, hb1]) (by simp [σ₁, hm2n]) (by simp [σ₁, hmwn]) L hpushL
  refine (RsbRunsWithin.seq hdisj h₁ h₂).congr ?_
  funext z; cases z <;> simp [σ₁]


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
