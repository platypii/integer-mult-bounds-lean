module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFoldData

/-! Reuse the existing tape fold on the generated local boundary coordinates. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}
  {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

/-- The input on `sel` is owned. Counters describe the actual boundary cardinality;
all other valuation entries and every register outside the fold bank are restored. -/
theorem boundaryFold_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    {s t : ℕ} [NeZero s] (hst : s < t) (band a b w : ℕ) (hb : b ≤ s)
    (σ : RsbR → List (Fin (A+4)))
    (hsel : σ .sel = boundaryOrderSymbols A w s t band a b)
    (htswn : (σ .tswn).length = ((haloBoundary s t band a b).card+1)/2*w)
    (hm2wn : (σ .m2wn).length = (haloBoundary s t band a b).card/2)
    (hkn : (σ .kn).length = ((haloBoundary s t band a b).card+1)/2-(haloBoundary s t band a b).card/2)
    (hsn : (σ .sn).length = (haloBoundary s t band a b).card)
    (hwn : (σ (.cm .wn)).length = w)
    (hvk : σ .vk = []) (hya : σ .ya = []) (hxs : σ .xs = [])
    (hnv : σ .nv = []) (htK : σ .tK = []) (htC : σ .tC = []) (hac2 : σ .ac2 = []) :
    RsbRuns body rg ι (bandFoldLineP rg) σ
      (Function.update (Function.update σ .sel []) .vk
        (cstream A w ((bFoldOrder s (haloBoundary s t band a b)).map
          (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))))
      (60*((haloBoundary s t band a b).card+1)*w+60*(haloBoundary s t band a b).card+60) := by
  let xs := boundaryIndexWords s t band a b
  have hlen : xs.length = (haloBoundary s t band a b).card := by
    simp only [xs,boundaryIndexWords,List.length_map,boundaryIndices_length hst band a b hb]
  have hs : σ .sel = cstream A w xs := by
    simpa only [xs,← boundaryOrderSymbols_cstream] using hsel
  have he := band_foldLine_runs (body := body) (ι := ι) hrg hdisj σ xs hs
    (by simpa only [hlen] using htswn) (by simpa only [hlen] using hm2wn)
    (by simpa only [hlen] using hkn) (by simpa only [hlen] using hsn)
    hwn hvk hya hxs hnv htK htC hac2
  simpa only [hlen,xs,boundaryIndexWords_fold hst band a b hb] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
