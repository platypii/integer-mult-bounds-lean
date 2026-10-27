module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorWorkspace

/-! Execute the allocated boundary factorizer on its physical bank, preserving every retained legacy tape. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

noncomputable def boundaryFactorPrep (hQ : SS.states ≤ Q) : Pr P 224 Q A U :=
  bandAxisPrepP boundaryFactorReg boundaryFactorMulReg_injective (by decide) hQ

theorem boundary_axisPrep_physical_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    ∀ (v : HS 224 Q A U) (S : Stacks 224 A),
    let σ := boundaryFactorState S
    (∀ i, S.L i = []) → (∀ i : Fin 64, S.R (boundaryFactorMulReg i) = []) →
    ∀ (_hready : RsbReady σ w q)
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
    ∃ v' S' n, v'.user = v.user ∧ n ≤ bandAxisPrepCost w k K B.card ∧
      Exec body (boundaryFactorPrep hQ) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ i : Fin 154, i ≠ 140 → S'.R (boundaryFactorLegacyReg i) = S.R (boundaryFactorLegacyReg i)) ∧
      (boundaryFactorState S') .bo = cstream A w ((facLf q K rows inputs B.card).map fun x => (⟨x, 0⟩ : GaussianInt)) ∧
      (boundaryFactorState S') .hf = cstream A w ((List.range B.card).reverse.map fun m =>
        colC (Mult.BandFactor.ucolZ (k + 1) (facUr q K rows inputs B.card) m)).flatten ∧
      (boundaryFactorState S') .df = cstream A w ((List.range B.card).reverse.map fun j =>
        (⟨Mult.BandFactor.newtonZ q (facPiv (facState q K rows inputs j)) K, 0⟩ : GaussianInt)) ∧
      (boundaryFactorState S') .src = SRC ∧ ((boundaryFactorState S') .m2n).length = k + 1 ∧ ((boundaryFactorState S') .mwn).length = (k + 1) * w ∧
      ((boundaryFactorState S') .sn).length = B.card ∧ (boundaryFactorState S') .dout = [] ∧ (boundaryFactorState S') .vk = [] ∧ (boundaryFactorState S') .ef = [] ∧ (boundaryFactorState S') .xs = [] ∧
      ((boundaryFactorState S') .kn).length = B.card * (k + 1) ∧ (boundaryFactorState S') .ms = σ .dst ∧ (boundaryFactorState S') .m2n = σ .ms ∧
      (boundaryFactorState S') .kn = (List.replicate B.card (σ .ms)).flatten ∧ (boundaryFactorState S') .mwn = σ (.cm .wn) ++ σ .m2wn ∧
      RsbReady (boundaryFactorState S') w q ∧
      ∀ r, r ∉ ([.src, .hf, .df, .dout, .bo, .vk, .m2n, .kn, .ms, .mwn, .ef, .xs] : List RsbR) →
        (boundaryFactorState S') r = σ r := by
  dsimp only
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let K := factorNewtonSteps p q
  let rows := factorIntegerRows (factorWindowValues B (k+1) columns)
  let inputs := factorIntegerRows (factorInputValues B (k+1) B.card columns)
  intro hformat hstage v S hleft hmul hready hseed SRC hsrc htswn hhf hdf hdout hmsk hvk hef htb hsr hbo hhv hxa hhc hya hxs hpr hac hac2 hnv hb1 htC htA htJ htK htL hsel hsn hkn hms hm2n hmwn hsmwn hm2wn hdst
  obtain ⟨σ',hrun,hpost⟩ := boundary_axisPrep_allocated_runs (body := body)
    boundaryFactorReg_injective boundaryFactorReg_disjoint boundaryFactorMulReg_injective (by decide) hQ hA
    p u l target rhsExp B k columns hp hlen hformat hstage (boundaryFactorState S) hready hseed SRC
    hsrc htswn hhf hdf hdout hmsk hvk hef htb hsr hbo hhv hxa hhc hya hxs hpr hac hac2 hnv hb1 htC htA htJ htK htL hsel hsn hkn hms hm2n hmwn hsmwn hm2wn hdst
  obtain ⟨v',S',n,hu,hn,he,hholds,hframe⟩ := hrun v S ⟨hleft,hmul⟩ (fun _ => rfl)
  have hstate : boundaryFactorState S' = σ' := funext hholds
  rw [←hstate] at hpost
  obtain ⟨hinp,hout,hL,hlegacy⟩ := boundaryFactorFr_legacy hframe
  exact ⟨v',S',n,hu,hn,he,hinp,hout,hL,hlegacy,hpost⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
