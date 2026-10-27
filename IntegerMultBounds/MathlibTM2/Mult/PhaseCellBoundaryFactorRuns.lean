module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorAllocatedFits

/-! Execute factorization and table preparation of the emitted boundary page, with all fit conditions derived. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

theorem boundary_axisPrep_allocated_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (p u l target rhsExp : ℕ) {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (k : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hp : 2 ≤ p) (hlen : columns.length = B.card) :
    let bits := boundaryTableBits p target rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    let rows := factorIntegerRows (factorWindowValues B (k+1) columns)
    let inputs := factorIntegerRows (factorInputValues B (k+1) B.card columns)
    ColumnFamilyFormat w columns →
    IntegerMultBounds.NLogN.SchurDominance.StageInv (factorRankMatrix A q w B (k+1) columns) (Finset.range B.card)
      (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^bits))
      (2+(B.card : ℝ)*(1/(2 : ℝ)^bits)) →
    ∀ (σ : RsbR → List (Fin (A + 4))) (_hready : RsbReady σ w q)
    (_hseed : σ .bx = csyms A w (⟨2^(q-2),0⟩ : GaussianInt))
    (SRC : List (Fin (A + 4)))
    (_hsrc : σ .src = cstream A w ((factorWindowValues B (k+1) columns).flatten ++
      (factorInputValues B (k+1) B.card columns).flatten) ++ SRC)
    (_htswn : (σ .tswn).length = (k + 1 + 1) * (2 * (k + 1) + 1) * w)
    (_hhf : σ .hf = []) (_hdf : σ .df = []) (_hdout : σ .dout = []) (_hmsk : σ .msk = csyms A w 0)
    (_hvk : σ .vk = []) (_hef : σ .ef = []) (_htb : σ .tb = []) (_hsr : σ .sr = []) (_hbo : σ .bo = [])
    (_hhv : σ .hv = []) (_hxa : σ .xa = []) (_hhc : σ .hc = []) (_hya : σ .ya = []) (_hxs : σ .xs = [])
    (_hpr : σ .pr = []) (_hac : σ .ac = []) (_hac2 : σ .ac2 = []) (_hnv : σ .nv = [])
    (_hb1 : σ .b1 = []) (_htC : σ .tC = []) (_htA : σ .tA = []) (_htJ : σ .tJ = [])
    (_htK : σ .tK = []) (_htL : σ .tL = []) (_hsel : σ .sel = []) (_hsn : (σ .sn).length = B.card)
    (_hkn : (σ .kn).length = K) (_hms : (σ .ms).length = k + 1) (_hm2n : (σ .m2n).length = 2 * (k + 1))
    (_hmwn : (σ .mwn).length = 2 * (k + 1) * w)
    (_hsmwn : (σ .smwn).length = (2 * (k + 1) + 1) * w) (_hm2wn : (σ .m2wn).length = k * w)
    (_hdst : (σ .dst).length = k),
    ∃ σ', RsbRuns body rg ι (bandAxisPrepP rg hι hT hQ) σ σ' (bandAxisPrepCost w k K B.card) ∧
      σ' .bo = cstream A w ((facLf q K rows inputs B.card).map fun x => (⟨x, 0⟩ : GaussianInt)) ∧
      σ' .hf = cstream A w ((List.range B.card).reverse.map fun m =>
        colC (Mult.BandFactor.ucolZ (k + 1) (facUr q K rows inputs B.card) m)).flatten ∧
      σ' .df = cstream A w ((List.range B.card).reverse.map fun j =>
        (⟨Mult.BandFactor.newtonZ q (facPiv (facState q K rows inputs j)) K, 0⟩ : GaussianInt)) ∧
      σ' .src = SRC ∧ (σ' .m2n).length = k + 1 ∧ (σ' .mwn).length = (k + 1) * w ∧
      (σ' .sn).length = B.card ∧ σ' .dout = [] ∧ σ' .vk = [] ∧ σ' .ef = [] ∧ σ' .xs = [] ∧
      (σ' .kn).length = B.card * (k + 1) ∧ σ' .ms = σ .dst ∧ σ' .m2n = σ .ms ∧
      σ' .kn = (List.replicate B.card (σ .ms)).flatten ∧ σ' .mwn = σ (.cm .wn) ++ σ .m2wn ∧
      RsbReady σ' w q ∧
      ∀ r, r ∉ ([.src, .hf, .df, .dout, .bo, .vk, .m2n, .kn, .ms, .mwn, .ef, .xs] : List RsbR) →
        σ' r = σ r := by
  dsimp only
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let K := factorNewtonSteps p q
  let rows := factorIntegerRows (factorWindowValues B (k+1) columns)
  let inputs := factorIntegerRows (factorInputValues B (k+1) B.card columns)
  intro hformat hstage σ hready hseed SRC hsrc
  intros
  have hfit := factorIntegerState_allocated_fits A p u l target rhsExp B (k+1) columns (by omega) hp hlen hformat hstage
  have hsrc' : σ .src = cstream A w ((rows.map colC).flatten++(inputs.map colC).flatten)++SRC := by
    simpa [rows,inputs,factorWindowIntegers_colC B (k+1) w columns hlen hformat,
      factorInputIntegers_colC B (k+1) w B.card columns hlen hformat] using hsrc
  apply band_axisPrep_runs (body := body) hrg hdisj hι hT hQ hA σ hready
    (by dsimp [w,executionWidth]; omega) (by dsimp [w,q,executionWidth,executionPrecision]; omega)
    rows inputs
    (by simp [rows])
    (factorIntegerRows_row_length _ _ (factorWindowValues_row_length B (k+1) columns))
    (factorIntegerRows_row_length _ _ (factorInputValues_row_length B (k+1) B.card columns))
    (by simp [inputs]) hfit
    (fun m hm => by simpa [IntegerMultBounds.MathlibTM2.Mult.BandFactor.newtonZ] using hseed) SRC hsrc'
  all_goals assumption

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
