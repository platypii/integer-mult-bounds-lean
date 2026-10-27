module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorPreparedRun

/-! Generate all setup and execute boundary factorization from retained masters and the emitted input page. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

noncomputable def initializedBoundaryFactor (hQ : SS.states ≤ Q) : Pr P 224 Q A U :=
  .seq boundaryFactorSetup (boundaryFactorPrep hQ)

theorem initializedBoundaryFactor_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    let σ := boundaryFactorState {S with R := boundaryFactorSetupR p q S.R}
    (∀ i, S.L i = []) →
    (∀ i : Fin 224, i.val < 64 → S.R i = []) →
    (∀ i : Fin 224, 154 ≤ i.val → S.R i = []) →
    (S.R 117).length = 2^15*p → (S.R 119).length = q →
    (S.R 124).length = band → (S.R 116).length = B.card →
    ∀ (SRC : List (Fin (A+4)))
    (_hsrc : S.R 140 = cstream A w ((factorWindowValues B (12*band+1) columns).flatten++
      (factorInputValues B (12*band+1) B.card columns).flatten)++SRC),
    ∃ v' S' n, v'.user = v.user ∧ n ≤ boundaryFactorSetupCost p q band B.card+bandAxisPrepCost w (12*band) K B.card ∧
      Exec body (initializedBoundaryFactor hQ) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ i : Fin 154, i ≠ 140 → S'.R (boundaryFactorLegacyReg i) = S.R (boundaryFactorLegacyReg i)) ∧
      S'.R 184 = [] ∧ S'.R 223 = [] ∧ S'.R 220 = [] ∧ S'.R 221 = [] ∧
      (S'.R 119).length = q ∧
      BoundarySolveReady (boundaryFactorState S') q w (12*band+1) B.card ∧
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
  intro hformat hstage v S hleft hclean hnew hmasterP hmasterQ hmasterBand hmasterCard SRC hsrc
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hprepared⟩ := boundaryFactorSetup_prepared_exec (body := body) p q band B.card v S
    hmasterP hmasterQ hmasterBand hmasterCard (fun i hi => hclean i (by omega)) hnew
  let S₁ : Stacks 224 A := {S with R := boundaryFactorSetupR p q S.R}
  have hmul (i : Fin 64) : S₁.R (boundaryFactorMulReg i) = [] := by
    let j : Fin 154 := ⟨i.val,by omega⟩
    have hj : boundaryFactorLegacyReg j = boundaryFactorMulReg i := Fin.ext rfl
    have hh := boundaryFactorSetupR_legacy p q S.R j
    rw [hj] at hh
    exact hh.trans (hclean (boundaryFactorMulReg i) i.isLt)
  have hsrc₁ : (boundaryFactorState S₁) .src = cstream A w
      ((factorWindowValues B (12*band+1) columns).flatten++(factorInputValues B (12*band+1) B.card columns).flatten)++SRC := by
    have hh : S₁.R 140 = S.R 140 := boundaryFactorSetupR_legacy p q S.R 140
    exact hh.trans hsrc
  obtain ⟨v₂,S₂,n₂,hu₂,hn₂,he₂,hinp,hout,hL,hlegacy,hframe,hpost⟩ := boundary_factorPrepared_exec (body := body)
    hQ hA p u l target rhsExp B band columns hp hlen hformat hstage v₁ S₁ hleft hmul hprepared SRC hsrc₁
  obtain ⟨hsolve,hbo,hhf,hdf,hsrc',hm2n',hmwn',hsn,hdout,hvk,hef,hxs,hkn,hms,hm2n,hkn',hmwnControl,hready',hframe'⟩ := hpost
  have h184 : S₁.R 184 = [] := by
    rw [show S₁.R 184 = S.R 184 from boundaryFactorSetupR_off p q S.R 184 (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hnew 184 (by decide)
  have h223 : S₁.R 223 = [] := by
    obtain ⟨_,_,_,_,_,_,_,_,h⟩ := boundaryFactorSetupR_dimensions p q band B.card S.R hmasterBand hmasterCard hnew
    exact h
  have h184' : S₂.R 184 = [] := (hframe.2.2.2 184 (fun r => (boundaryFactorReg_private r).1)).trans h184
  have h223' : S₂.R 223 = [] := (hframe.2.2.2 223 (fun r => (boundaryFactorReg_private r).2)).trans h223
  have h220 : S₁.R 220 = [] := by
    rw [show S₁.R 220 = S.R 220 from boundaryFactorSetupR_off p q S.R 220 (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hnew 220 (by decide)
  have h221 : S₁.R 221 = [] := by
    rw [show S₁.R 221 = S.R 221 from boundaryFactorSetupR_off p q S.R 221 (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hnew 221 (by decide)
  have h220' : S₂.R 220 = [] := (hframe' .dtab (by decide)).trans h220
  have h221' : S₂.R 221 = [] := (hframe' .padc (by decide)).trans h221
  have h119 : (S₂.R 119).length = q := by
    rw [show S₂.R 119 = S₁.R 119 from hlegacy 119 (by decide),
      show S₁.R 119 = S.R 119 from boundaryFactorSetupR_legacy p q S.R 119]
    exact hmasterQ
  refine ⟨v₂,S₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂,hinp,hout,hL,?_,h184',h223',h220',h221',h119,hsolve,hbo,hhf,hdf,hsrc',hm2n',hmwn',hsn,
    hdout,hvk,hef,hxs,hkn,hms,hm2n,hkn',hmwnControl,hready',hframe'⟩
  intro i hi
  exact (hlegacy i hi).trans (boundaryFactorSetupR_legacy p q S.R i)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
