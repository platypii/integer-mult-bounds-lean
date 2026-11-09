module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBandFactorLoopStock
public import IntegerMultBounds.MathlibTM2.Fast.BandAxisOrganizationStock

/-! Initial-window transfer and final-window release preserve the factor scan bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {Proc U : Type} {body : Proc → Pr Proc T Q A U}
  {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

theorem band_axisFac_runs_within (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w P B K s : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w P) (hw : 1 ≤ w)
    (hp : P ≤ w) (rows inputs : List (List ℤ)) (hrows : rows.length = B + 1)
    (hrl : ∀ row ∈ rows, row.length = 2 * B + 1) (hin : ∀ row ∈ inputs, row.length = 2 * B + 1)
    (hs : inputs.length = s) (hfit : ∀ m < s, FacFits w P K (facState P K rows inputs m))
    (hr0 : ∀ m < s, σ .bx = csyms A w ⟨Mult.BandFactor.newtonZ P (facPiv (facState P K rows inputs m)) 0, 0⟩)
    (SRC : List (Fin (A + 4)))
    (hsrc : σ .src = cstream A w ((rows.map colC).flatten ++ (inputs.map colC).flatten) ++ SRC)
    (htswn : (σ .tswn).length = (B + 1) * (2 * B + 1) * w)
    (hhf : σ .hf = []) (hdf : σ .df = []) (hdout : σ .dout = []) (hmsk : σ .msk = csyms A w 0)
    (hvk : σ .vk = []) (hef : σ .ef = []) (htb : σ .tb = []) (hsr : σ .sr = []) (hbo : σ .bo = [])
    (hhv : σ .hv = []) (hxa : σ .xa = []) (hhc : σ .hc = []) (hya : σ .ya = []) (hxs : σ .xs = [])
    (hpr : σ .pr = []) (hac : σ .ac = []) (hac2 : σ .ac2 = []) (hnv : σ .nv = [])
    (hb1 : σ .b1 = []) (htC : σ .tC = []) (htA : σ .tA = []) (htJ : σ .tJ = [])
    (htK : σ .tK = []) (htL : σ .tL = []) (hsel : σ .sel = []) (hsn : (σ .sn).length = s)
    (hkn : (σ .kn).length = K) (hms : (σ .ms).length = B) (hm2n : (σ .m2n).length = 2 * B)
    (hmwn : (σ .mwn).length = 2 * B * w) (hsmwn : (σ .smwn).length = (2 * B + 1) * w)
    (J L : ℕ)
    (hpushJ : mnProgPush (rmulOne (P := Proc) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg .hv .xa .hc)) ≤ J)
    (hpushL : mnProgPush (rmulOne (P := Proc) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg .ya .xs .pr)) ≤ L) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι) (bandAxisFacP rg hι hT hQ) σ
      (Function.update (Function.update (Function.update (Function.update σ
        .src SRC)
        .hf (cstream A w ((List.range s).reverse.map fun j =>
          colC ((facState P K rows inputs j).headD [])).flatten))
        .df (cstream A w ((List.range s).reverse.map fun j =>
          (⟨Mult.BandFactor.newtonZ P (facPiv (facState P K rows inputs j)) K, 0⟩ : GaussianInt))))
        .dout (cstream A w (((List.range s).map fun j =>
          colC (Mult.BandFactor.lcolZ P K (facState P K rows inputs j))).flatten.reverse)))
      (4 * ((B + 1) * (2 * B + 1) * w) + 4 + (2 * ((B + 1) * (2 * B + 1) * w) + 2) +
        (s * (bandFacStepCost w B K + 6) + 4) + (2 * ((B + 1) * (2 * B + 1) * w) + 2))
      (2*(4*((B+1)*(2*B+1)*w)+4)+(s*((B+1)*w)+(1000*(B+1)*(B+1)*(w+1) +
       bandNewtonStepPush (P := Proc) (A := A) (U := U) rg hι hT hQ*bandNewtonStepCost w +
       ((realWeightWorkspace J w 1+1000*(w+1))+
        (realWeightWorkspace L w (2*B)+1000*(2*B+1)*(w+1)))))) := by
  have hwl : ((rows.map colC).flatten).length = (B + 1) * (2 * B + 1) := by
    rw [List.length_flatten, List.map_map]
    rw [List.map_congr_left (g := fun _ => 2 * B + 1) (fun r hr => by simp [colC, hrl r hr]),
      List.map_const', List.sum_replicate, hrows, smul_eq_mul]
  have h₁ := rsb_mv_runs (body := body) (ι := ι) hrg (c := .tswn) (t := .tC) (x := .src) (y := .ac2)
    (by decide) σ htC (by rw [htswn, hsrc]; simp [hwl])
  have hl1 : (σ .tswn).length = ((rows.map colC).flatten).length * w := by rw [htswn, hwl]
  rw [hl1, hsrc, cstream_append, List.append_assoc, take_cstream _ _ le_rfl, drop_cstream,
    List.take_length, List.drop_length, Nat.sub_self, zero_mul, List.drop_zero, cstream_nil,
    List.nil_append, hac2, List.append_nil] at h₁
  set σ₁ := Function.update (Function.update σ .src (cstream A w (inputs.map colC).flatten ++ SRC))
    .ac2 (cstream A w (rows.map colC).flatten).reverse
  have h₂ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := .vk) (by decide) σ₁
  set σ₂ := Function.update (Function.update σ₁ .ac2 []) .vk ((σ₁ .ac2).reverse ++ σ₁ .vk)
  have hready₂ : RsbReady σ₂ w P := by
    simp only [σ₂, σ₁]
    exact (((hready.update .src (fun c => by simp) _).update .ac2 (fun c => by simp) _).update .ac2
      (fun c => by simp) _).update .vk (fun c => by simp) _
  have h₃ := band_facLoop_runs_within (body := body) (ι := ι) (w := w) (B := B) (K := K) (s := s) hrg hdisj hι
    hT hQ hA σ₂ hready₂ hw hp rows inputs hrows hrl hin hs hfit
    (fun m hm => by simp [σ₂, σ₁, hr0 m hm]) SRC [] [] []
    (by simp [σ₂, σ₁, hvk]) (by simp [σ₂, σ₁]) (by simp [σ₂, σ₁, hhf]) (by simp [σ₂, σ₁, hdf])
    (by simp [σ₂, σ₁, hdout]) (by simp [σ₂, σ₁, hmsk]) (by simp [σ₂, σ₁, hef]) (by simp [σ₂, σ₁, htb])
    (by simp [σ₂, σ₁, hsr]) (by simp [σ₂, σ₁, hbo]) (by simp [σ₂, σ₁, hhv]) (by simp [σ₂, σ₁, hxa])
    (by simp [σ₂, σ₁, hhc]) (by simp [σ₂, σ₁, hya]) (by simp [σ₂, σ₁, hxs]) (by simp [σ₂, σ₁, hpr])
    (by simp [σ₂, σ₁, hac]) (by simp [σ₂, σ₁]) (by simp [σ₂, σ₁, hnv]) (by simp [σ₂, σ₁, hb1])
    (by simp [σ₂, σ₁, htC]) (by simp [σ₂, σ₁, htA]) (by simp [σ₂, σ₁, htJ]) (by simp [σ₂, σ₁, htK])
    (by simp [σ₂, σ₁, htL]) (by simp [σ₂, σ₁, hsel]) (by simp [σ₂, σ₁, hsn]) (by simp [σ₂, σ₁, hkn])
    (by simp [σ₂, σ₁, hms]) (by simp [σ₂, σ₁, hm2n]) (by simp [σ₂, σ₁, hmwn]) (by simp [σ₂, σ₁, hsmwn]) J L hpushJ hpushL
  set σ₃ := Function.update (Function.update (Function.update (Function.update (Function.update σ₂ .vk
    (cstream A w ((facState P K rows inputs s).map colC).flatten)) .src SRC)
    .hf (cstream A w ((List.range s).reverse.map fun j =>
      colC ((facState P K rows inputs j).headD [])).flatten ++ []))
    .df (cstream A w ((List.range s).reverse.map fun j =>
      (⟨Mult.BandFactor.newtonZ P (facPiv (facState P K rows inputs j)) K, 0⟩ : GaussianInt)) ++ []))
    .dout (cstream A w (((List.range s).map fun j =>
      colC (Mult.BandFactor.lcolZ P K (facState P K rows inputs j))).flatten.reverse) ++ [])
  have h₄ := rsb_emptyR_runs (body := body) (ι := ι) hrg .vk σ₃
  have hfl : (cstream A w ((facState P K rows inputs s).map colC).flatten).length =
      (B + 1) * (2 * B + 1) * w := by
    obtain ⟨hl, hrl'⟩ := facState_shape P K B rows inputs hrows hrl hin s (by omega)
    rw [length_cstream, List.length_flatten, List.map_map,
      List.map_congr_left (g := fun _ => 2 * B + 1) (fun r hr => by simp [colC, hrl' r hr]),
      List.map_const', List.sum_replicate, hl, smul_eq_mul]
  have h₁w := h₁.within_native (rsbMv_native ..)
  have h₂w := h₂.within_moveR
  have h₄w := h₄.within_native (c := 0) (by
    simp [emptyR,emptyStep,whileR,peekR,mnNativePushBound,mnActPush])
  refine ((RsbRunsWithin.seq hdisj h₁w (RsbRunsWithin.seq hdisj h₂w (RsbRunsWithin.seq hdisj h₃ h₄w))).congr ?_).mono ?_ (by rw [hwl]; omega)
  · funext x; cases x <;> simp [σ₃, σ₂, σ₁, hvk, hac2]
  · simp only [σ₃, Function.update_self, σ₁, σ₂, length_cstream, List.length_reverse, hwl]
    simp [hvk]
    have hsum : (List.map (List.length ∘ colC) (facState P K rows inputs s)).sum = (B + 1) * (2 * B + 1) := by
      obtain ⟨hl, hrl'⟩ := facState_shape P K B rows inputs hrows hrl hin s (by omega)
      rw [List.map_congr_left (g := fun _ => 2 * B + 1) (fun r hr => by simp [colC, hrl' r hr]),
        List.map_const', List.sum_replicate, hl, smul_eq_mul]
    rw [hsum]; omega


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
