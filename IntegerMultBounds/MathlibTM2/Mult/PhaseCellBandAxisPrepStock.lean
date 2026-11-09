module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBandAxisFactorStock

/-! Per-axis preparation retains the numerical factor workspace through native
organization and transpose. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {Proc U : Type} {body : Proc → Pr Proc T Q A U}
  {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

noncomputable def bandAxisPrepWorkspace {P : Type} (rg : RsbR → Fin T)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    (w k K s J L : ℕ) : ℕ :=
  (2*(4*((k+1+1)*(2*(k+1)+1)*w)+4) +
    (s*((k+1+1)*w)+(1000*(k+1+1)*(k+1+1)*(w+1) +
      bandNewtonStepPush (P := P) (A := A) (U := U) rg hι hT hQ*bandNewtonStepCost w +
      ((realWeightWorkspace J w 1+1000*(w+1))+
        (realWeightWorkspace L w (2*(k+1))+1000*(2*(k+1)+1)*(w+1)))))) +
    (2*bandAxisOrgCost s k w K + 2*bandTStepCost w k)

theorem band_axisPrep_runs_within (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w P k K s : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w P) (hw : 1 ≤ w)
    (hp : P ≤ w) (rows inputs : List (List ℤ)) (hrows : rows.length = k + 1 + 1)
    (hrl : ∀ row ∈ rows, row.length = 2 * (k + 1) + 1)
    (hin : ∀ row ∈ inputs, row.length = 2 * (k + 1) + 1)
    (hs : inputs.length = s) (hfit : ∀ m < s, FacFits w P K (facState P K rows inputs m))
    (hr0 : ∀ m < s, σ .bx = csyms A w ⟨Mult.BandFactor.newtonZ P (facPiv (facState P K rows inputs m)) 0, 0⟩)
    (SRC : List (Fin (A + 4)))
    (hsrc : σ .src = cstream A w ((rows.map colC).flatten ++ (inputs.map colC).flatten) ++ SRC)
    (htswn : (σ .tswn).length = (k + 1 + 1) * (2 * (k + 1) + 1) * w)
    (hhf : σ .hf = []) (hdf : σ .df = []) (hdout : σ .dout = []) (hmsk : σ .msk = csyms A w 0)
    (hvk : σ .vk = []) (hef : σ .ef = []) (htb : σ .tb = []) (hsr : σ .sr = []) (hbo : σ .bo = [])
    (hhv : σ .hv = []) (hxa : σ .xa = []) (hhc : σ .hc = []) (hya : σ .ya = []) (hxs : σ .xs = [])
    (hpr : σ .pr = []) (hac : σ .ac = []) (hac2 : σ .ac2 = []) (hnv : σ .nv = [])
    (hb1 : σ .b1 = []) (htC : σ .tC = []) (htA : σ .tA = []) (htJ : σ .tJ = [])
    (htK : σ .tK = []) (htL : σ .tL = []) (hsel : σ .sel = []) (hsn : (σ .sn).length = s)
    (hkn : (σ .kn).length = K) (hms : (σ .ms).length = k + 1) (hm2n : (σ .m2n).length = 2 * (k + 1))
    (hmwn : (σ .mwn).length = 2 * (k + 1) * w)
    (hsmwn : (σ .smwn).length = (2 * (k + 1) + 1) * w) (hm2wn : (σ .m2wn).length = k * w)
    (hdst : (σ .dst).length = k)
    (J L : ℕ)
    (hpushJ : mnProgPush (rmulOne (P := Proc) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg .hv .xa .hc)) ≤ J)
    (hpushL : mnProgPush (rmulOne (P := Proc) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg .ya .xs .pr)) ≤ L) :
    ∃ σ', RsbRunsWithin (body := body) (rg := rg) (ι := ι) (bandAxisPrepP rg hι hT hQ) σ σ' (bandAxisPrepCost w k K s)
      (bandAxisPrepWorkspace (P := Proc) (A := A) (U := U) rg hι hT hQ w k K s J L) ∧
      σ' .bo = cstream A w ((facLf P K rows inputs s).map fun x => (⟨x, 0⟩ : GaussianInt)) ∧
      σ' .hf = cstream A w ((List.range s).reverse.map fun m =>
        colC (Mult.BandFactor.ucolZ (k + 1) (facUr P K rows inputs s) m)).flatten ∧
      σ' .df = cstream A w ((List.range s).reverse.map fun j =>
        (⟨Mult.BandFactor.newtonZ P (facPiv (facState P K rows inputs j)) K, 0⟩ : GaussianInt)) ∧
      σ' .src = SRC ∧ (σ' .m2n).length = k + 1 ∧ (σ' .mwn).length = (k + 1) * w ∧
      (σ' .sn).length = s ∧ σ' .dout = [] ∧ σ' .vk = [] ∧ σ' .ef = [] ∧ σ' .xs = [] ∧
      (σ' .kn).length = s * (k + 1) ∧ σ' .ms = σ .dst ∧ σ' .m2n = σ .ms ∧
      σ' .kn = (List.replicate s (σ .ms)).flatten ∧ σ' .mwn = σ (.cm .wn) ++ σ .m2wn ∧
      RsbReady σ' w P ∧
      ∀ r, r ∉ ([.src, .hf, .df, .dout, .bo, .vk, .m2n, .kn, .ms, .mwn, .ef, .xs] : List RsbR) →
        σ' r = σ r := by
  have hwn := hready.wn
  set Lf := facLf P K rows inputs s with hLfdef
  set Ur := facUr P K rows inputs s with hUrdef
  have hshape := fun j (hj : j ≤ s) => facState_shape P K (k + 1) rows inputs hrows hrl hin j (by omega)
  have hLf : Lf.length = s * (k + 1) :=
    length_facLf P K (k+1) s rows inputs hrows hrl hin (by omega)
  have hUr : Ur.length = s := by simp [hUrdef, facUr]
  have hUrow : ∀ row ∈ Ur, row.length = 2 * (k + 1) + 1 := by
    intro row hrow
    simp only [hUrdef, facUr, List.mem_map, List.mem_range] at hrow
    obtain ⟨j, hj, rfl⟩ := hrow
    obtain ⟨hl, hrl'⟩ := hshape j hj.le
    cases h : facState P K rows inputs j with
    | nil => rw [h] at hl; simp at hl
    | cons a l => exact hrl' a (by rw [h]; simp)
  have h₁ := band_axisFac_runs_within (body := body) (ι := ι) (w := w) (B := k + 1) (K := K) (s := s) hrg hdisj
    hι hT hQ hA σ hready hw hp rows inputs hrows hrl hin hs hfit hr0 SRC hsrc htswn hhf hdf hdout hmsk
    hvk hef htb hsr hbo hhv hxa hhc hya hxs hpr hac hac2 hnv hb1 htC htA htJ htK htL hsel hsn hkn hms
    hm2n hmwn hsmwn J L hpushJ hpushL
  set σ₁ := Function.update (Function.update (Function.update (Function.update σ
        .src SRC)
        .hf (cstream A w ((List.range s).reverse.map fun j =>
          colC ((facState P K rows inputs j).headD [])).flatten))
        .df (cstream A w ((List.range s).reverse.map fun j =>
          (⟨Mult.BandFactor.newtonZ P (facPiv (facState P K rows inputs j)) K, 0⟩ : GaussianInt))))
        .dout (cstream A w (((List.range s).map fun j =>
          colC (Mult.BandFactor.lcolZ P K (facState P K rows inputs j))).flatten.reverse))
  have hd₁ : σ₁ .dout = cstream A w ((Lf.map fun x => (⟨x, 0⟩ : GaussianInt)).reverse) := by
    simp [σ₁, hLfdef, facLf, colC, List.map_flatten, Function.comp_def]
  have hh₁ : σ₁ .hf = cstream A w (Ur.map colC).reverse.flatten := by
    simp [σ₁, hUrdef, facUr, List.map_reverse, Function.comp_def]
  have h₂ := band_axisOrg_runs_within (body := body) (ι := ι) hrg hdisj (w := w) (k := k) (s := s) (K := K) σ₁ Lf hLf Ur
    hUr hUrow SRC hd₁ hh₁ (by simp [σ₁]) (by simp [σ₁, hbo]) (by simp [σ₁, hvk]) (by simp [σ₁, hxs])
    (by simp [σ₁, hmsk]) (by simp [σ₁, hms]) (by simp [σ₁, hsn]) (by simp [σ₁, hsmwn])
    (by simp [σ₁, hwn]) (by simp [σ₁, htK]) (by simp [σ₁, htL]) (by simp [σ₁, hsel])
    (by simp [σ₁, htC]) (by simp [σ₁, hb1]) (by simp [σ₁, hac2]) (by simp [σ₁, hm2n])
    (by simp [σ₁, hkn]) (by simp [σ₁, hmwn]) (by simp [σ₁, hm2wn]) (by simp [σ₁, hdst]) hw
  set σ₂ := Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update σ₁
        .m2n (σ₁ .ms)) .kn ((List.replicate s (σ₁ .ms)).flatten)) .dout [])
        .bo (cstream A w (Lf.map fun x => (⟨x, 0⟩ : GaussianInt)))) .hf [])
        .src (cstream A w (Ur.map colC).flatten ++ SRC))
        .vk ((List.replicate (k + 1) ((List.replicate (k + 1) (csyms A w 0)).flatten)).flatten))
        .ms (σ₁ .dst)) .mwn (σ₁ (.cm .wn) ++ σ₁ .m2wn)
  have hz : (List.replicate (k + 1) ((List.replicate (k + 1) (csyms A w 0)).flatten)).flatten =
      cstream A w ((Mult.BandFactor.tWin (k + 1) Ur 0).map colC).flatten := by
    rw [Mult.BandFactor.tWin_zero]
    simp [cstream, colC, List.flatMap, List.map_replicate, List.flatten_replicate_replicate]
    have hrep : ∀ (a b : ℕ) (x : List (Fin (A + 4))),
        (List.replicate a (List.replicate b x).flatten).flatten = (List.replicate (a * b) x).flatten := by
      intro a b x
      induction a with
      | zero => simp
      | succ a ih =>
        rw [List.replicate_succ, List.flatten_cons, ih, show (a + 1) * b = b + a * b by ring,
          List.replicate_add, List.flatten_append]
    rw [hrep]; rfl
  have h₃ := band_axisTr_runs_within (body := body) (ι := ι) hrg hdisj (w := w) (k := k) (s := s) σ₂ Ur hUr
    hUrow SRC (by simp [σ₂]) (by simp [σ₂, hz]) (by simp [σ₂, σ₁, hef]) (by simp [σ₂])
    (by simp [σ₂, σ₁, hmsk]) (by simp [σ₂, σ₁, hpr]) (by simp [σ₂, σ₁, hxs]) (by simp [σ₂, σ₁, hya])
    (by simp [σ₂, σ₁, hnv]) (by simp [σ₂, σ₁, htC]) (by simp [σ₂, σ₁, htL]) (by simp [σ₂, σ₁, hsel])
    (by simp [σ₂, σ₁, hac2]) (by simp [σ₂, σ₁, hsn]) (by simp [σ₂, σ₁, hwn])
    (by simp [σ₂, σ₁, hwn, hm2wn]; ring) (by simp [σ₂, σ₁, hm2wn]) (by simp [σ₂, σ₁, hdst])
  refine ⟨_, (RsbRunsWithin.seq hdisj h₁ (RsbRunsWithin.seq hdisj h₂ h₃)).mono (le_of_eq rfl) (le_of_eq (by unfold bandAxisPrepWorkspace; omega)), by simp [σ₂], by simp,
    by simp [σ₂, σ₁], by simp [σ₂, σ₁], by simp [σ₂, σ₁, hms], by simp [σ₂, σ₁, hwn, hm2wn]; ring,
    by simp [σ₂, σ₁, hsn], by simp [σ₂, σ₁], by simp [σ₂, σ₁], by simp [σ₂, σ₁, hef],
    by simp [σ₂, σ₁, hxs], by simp [σ₂, σ₁, hms], by simp [σ₂, σ₁], by simp [σ₂, σ₁],
    by simp [σ₂, σ₁], by simp [σ₂, σ₁], ⟨by simp [σ₂, σ₁, hwn], by simp [σ₂, σ₁, hready.pn],
      by simp [σ₂, σ₁, hready.nn], fun c h1 h2 h3 h4 h5 h6 => by
        simp [σ₂, σ₁, hready.empty c h1 h2 h3 h4 h5 h6]⟩, fun r hr => ?_⟩
  cases r <;> simp [σ₂, σ₁] at hr ⊢

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
