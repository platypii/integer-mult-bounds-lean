module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBandAxisPrepStock

/-! Actual arithmetic programs instantiate the structural factor-axis reserve.
Opaque push counts keep later callers from reducing the multiplication program. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {ι : Fin 64 → Fin T}

@[irreducible] noncomputable def factorRmulPush (cr : CR → Fin T)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) : ℕ :=
  mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U) ι hι hT hQ cr)

theorem factorRmulPush_bound (cr : CR → Fin T)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) :
    mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U) ι hι hT hQ cr) ≤
      factorRmulPush (P := P) (A := A) (U := U) cr hι hT hQ := by
  unfold factorRmulPush
  exact le_refl _

@[irreducible] noncomputable def boundaryAxisPrepWorkspace (rg : RsbR → Fin T)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    (w k K n : ℕ) : ℕ :=
  bandAxisPrepWorkspace (P := P) (A := A) (U := U) rg hι hT hQ w k K n
    (factorRmulPush (P := P) (A := A) (U := U) (rsbCr rg .hv .xa .hc) hι hT hQ)
    (factorRmulPush (P := P) (A := A) (U := U) (rsbCr rg .ya .xs .pr) hι hT hQ)

variable {Pgm : Type} {body : Pgm → Pr Pgm T Q A U} {rg : RsbR → Fin T}

theorem band_axisPrep_actual_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
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
 :
    ∃ σ', RsbRunsWithin (body := body) (rg := rg) (ι := ι) (bandAxisPrepP rg hι hT hQ) σ σ' (bandAxisPrepCost w k K s)
      (boundaryAxisPrepWorkspace (P := Pgm) (A := A) (U := U) rg hι hT hQ w k K s) ∧
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
  unfold boundaryAxisPrepWorkspace
  exact band_axisPrep_runs_within hrg hdisj hι hT hQ hA σ hready hw hp rows inputs
    hrows hrl hin hs hfit hr0 SRC hsrc htswn hhf hdf hdout hmsk hvk hef htb hsr hbo
    hhv hxa hhc hya hxs hpr hac hac2 hnv hb1 htC htA htJ htK htL hsel hsn hkn hms
    hm2n hmwn hsmwn hm2wn hdst _ _ (factorRmulPush_bound ..) (factorRmulPush_bound ..)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
