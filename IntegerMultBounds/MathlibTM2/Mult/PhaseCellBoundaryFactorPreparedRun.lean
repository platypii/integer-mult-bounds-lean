module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorPrepared
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorPhysical

/-! Execute factorization using the complete precondition proved for generated setup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

theorem boundary_factorPrepared_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (p u l target rhsExp : ℕ) {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (band : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hp : 2 ≤ p) (hlen : columns.length = B.card) :
    let bits := boundaryTableBits p target rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    let rows := factorIntegerRows (factorWindowValues B ((12*band)+1) columns)
    let inputs := factorIntegerRows (factorInputValues B ((12*band)+1) B.card columns)
    ColumnFamilyFormat w columns →
    IntegerMultBounds.NLogN.SchurDominance.StageInv (factorRankMatrix A q w B ((12*band)+1) columns) (Finset.range B.card)
      (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^bits))
      (2+(B.card : ℝ)*(1/(2 : ℝ)^bits)) →
    ∀ (v : HS 224 Q A U) (S : Stacks 224 A),
    let σ := boundaryFactorState S
    (∀ i, S.L i = []) → (∀ i : Fin 64, S.R (boundaryFactorMulReg i) = []) →
    BoundaryFactorPrepared σ p q band B.card →
    ∀ (SRC : List (Fin (A+4)))
    (_hsrc : σ .src = cstream A w ((factorWindowValues B (12*band+1) columns).flatten++
      (factorInputValues B (12*band+1) B.card columns).flatten)++SRC),
    ∃ v' S' n, v'.user = v.user ∧ n ≤ bandAxisPrepCost w (12*band) K B.card ∧
      Exec body (boundaryFactorPrep hQ) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ i : Fin 154, i ≠ 140 → S'.R (boundaryFactorLegacyReg i) = S.R (boundaryFactorLegacyReg i)) ∧
      (boundaryFactorState S') .bo = cstream A w ((facLf q K rows inputs B.card).map fun x => (⟨x, 0⟩ : GaussianInt)) ∧
      (boundaryFactorState S') .hf = cstream A w ((List.range B.card).reverse.map fun m =>
        colC (Mult.BandFactor.ucolZ ((12*band) + 1) (facUr q K rows inputs B.card) m)).flatten ∧
      (boundaryFactorState S') .df = cstream A w ((List.range B.card).reverse.map fun j =>
        (⟨Mult.BandFactor.newtonZ q (facPiv (facState q K rows inputs j)) K, 0⟩ : GaussianInt)) ∧
      (boundaryFactorState S') .src = SRC ∧ ((boundaryFactorState S') .m2n).length = (12*band) + 1 ∧ ((boundaryFactorState S') .mwn).length = ((12*band) + 1) * w ∧
      ((boundaryFactorState S') .sn).length = B.card ∧ (boundaryFactorState S') .dout = [] ∧ (boundaryFactorState S') .vk = [] ∧ (boundaryFactorState S') .ef = [] ∧ (boundaryFactorState S') .xs = [] ∧
      ((boundaryFactorState S') .kn).length = B.card * ((12*band) + 1) ∧ (boundaryFactorState S') .ms = σ .dst ∧ (boundaryFactorState S') .m2n = σ .ms ∧
      (boundaryFactorState S') .kn = (List.replicate B.card (σ .ms)).flatten ∧ (boundaryFactorState S') .mwn = σ (.cm .wn) ++ σ .m2wn ∧
      RsbReady (boundaryFactorState S') w q ∧
      ∀ r, r ∉ ([.src, .hf, .df, .dout, .bo, .vk, .m2n, .kn, .ms, .mwn, .ef, .xs] : List RsbR) →
        (boundaryFactorState S') r = σ r := by
  dsimp only
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  intro hformat hstage v S hleft hmul hprepared SRC hsrc
  have hw : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  obtain ⟨hready,hseed,hmask,htswn,hmwn,hsmwn,hm2wn⟩ := hprepared.at_width w hw
  exact boundary_axisPrep_physical_exec (body := body) hQ hA p u l target rhsExp B (12*band) columns hp hlen
    hformat hstage v S hleft hmul hready
    hseed SRC hsrc
    htswn
    (hprepared.empty .hf (by simp [boundaryFactorScratch]))
    (hprepared.empty .df (by simp [boundaryFactorScratch]))
    (hprepared.empty .dout (by simp [boundaryFactorScratch]))
    hmask
    (hprepared.empty .vk (by simp [boundaryFactorScratch]))
    (hprepared.empty .ef (by simp [boundaryFactorScratch]))
    (hprepared.empty .tb (by simp [boundaryFactorScratch]))
    (hprepared.empty .sr (by simp [boundaryFactorScratch]))
    (hprepared.empty .bo (by simp [boundaryFactorScratch]))
    (hprepared.empty .hv (by simp [boundaryFactorScratch]))
    (hprepared.empty .xa (by simp [boundaryFactorScratch]))
    (hprepared.empty .hc (by simp [boundaryFactorScratch]))
    (hprepared.empty .ya (by simp [boundaryFactorScratch]))
    (hprepared.empty .xs (by simp [boundaryFactorScratch]))
    (hprepared.empty .pr (by simp [boundaryFactorScratch]))
    (hprepared.empty .ac (by simp [boundaryFactorScratch]))
    (hprepared.empty .ac2 (by simp [boundaryFactorScratch]))
    (hprepared.empty .nv (by simp [boundaryFactorScratch]))
    (hprepared.empty .b1 (by simp [boundaryFactorScratch]))
    (hprepared.empty .tC (by simp [boundaryFactorScratch]))
    (hprepared.empty .tA (by simp [boundaryFactorScratch]))
    (hprepared.empty .tJ (by simp [boundaryFactorScratch]))
    (hprepared.empty .tK (by simp [boundaryFactorScratch]))
    (hprepared.empty .tL (by simp [boundaryFactorScratch]))
    (hprepared.empty .sel (by simp [boundaryFactorScratch]))
    hprepared.sn hprepared.kn hprepared.ms hprepared.m2n
    hmwn hsmwn
    hm2wn hprepared.dst

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
