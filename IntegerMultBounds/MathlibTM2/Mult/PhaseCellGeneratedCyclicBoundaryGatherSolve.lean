module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicBoundaryRhsPhysical
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBoundaryGatherSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBoundaryNormalizeSolve

/-! Gather the joint RHS from two retained physical residuals, normalize it and execute one boundary solve. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.Sizes

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

noncomputable def generatedCyclicBoundaryGatherSolve (hQ : SS.states ≤ Q) : Pr P 224 Q A U :=
  .seq cyclicBoundaryRhsPhysical (generatedBoundaryNormalizeSolve hQ)

theorem generatedCyclicBoundaryGatherSolve_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (p u l target rhsExp : ℕ) {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (W V a b : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hp : 2 ≤ p) (hlen : columns.length = B.card)
    (hs : s+s ≤ 2^V) (ha : a ≤ s) (hb : b ≤ s) :
    let bits := boundaryTableBits p target rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    let AZ := factorRankIntegerMatrix B W columns
    let Lc := naturalLineLc q K W B.card AZ
    let Uc := naturalLineUc q K W B.card AZ
    let rcs := naturalLineRcs q K W B.card AZ
    ColumnFamilyFormat w columns →
    StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card)
      (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^bits))
      (2+(B.card : ℝ)*(1/(2 : ℝ)^bits)) →
    ∀ (C D : ZMod s → GaussianInt), (∀ i ∈ B, |gv q (if a ≤ i.val ∧ i.val < b then C i else D i).re| ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u) ∧ |gv q (if a ≤ i.val ∧ i.val < b then C i else D i).im| ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u)) →
    ∀ (coordinateTail rhsTail : List (Fin (A+4))) (v : HS 224 Q A U) (S : Stacks 224 A),
    let σ := boundaryFactorState S
    (∀ i, S.L i = []) → (∀ i : Fin 64, S.R (boundaryFactorMulReg i) = []) →
    BoundarySolveReady σ q w W B.card →
    (S.R 119).length = q → S.R 223 = [] → S.R 184 = [] → S.R 220 = [] → S.R 221 = [] →
    (S.R 116).length = B.card → (S.R 115).length = V →
    S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++coordinateTail →
    (S.R 121).length = s → (S.R 144).length = a → (S.R 145).length = b →
    S.R 132 = cstream A w (chirpLine s D)++(cstream A w (chirpLine s C)++rhsTail) →
    S.R 206 = [] →
    (∀ k ∈ [(94 : Fin 224),106,134,135,136,137,138,139,140,150], S.R k = []) →
    σ .bo = cstream A w (Lc.map colC).flatten →
    σ .hf = cstream A w (Uc.map colC).flatten →
    σ .df = cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt)) →
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ cyclicBoundaryRhsPrepareCost B q V a b+generatedBoundaryNormalizeCost q B.card+4*B.card*w+4*W*w+8+bandLinePassCost w B.card W ∧
      Exec body (generatedCyclicBoundaryGatherSolve hQ) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ i : Fin 154, S'.R (boundaryFactorLegacyReg i) = S.R (boundaryFactorLegacyReg i)) ∧
      RsbFr boundaryFactorReg S S' ∧
      boundaryFactorState S' = Function.update (Function.update σ .vk []) .dout
        (cstream A w (bandSolveVec q W Lc Uc rcs
          (((List.range B.card).map (fun j => (if a ≤ (bFoldAt s B j).val ∧ (bFoldAt s B j).val < b then C (bFoldAt s B j) else D (bFoldAt s B j)))).map (normalizeBoundaryWord q (q/2-1))))) := by
  dsimp only
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  intro hformat hstage C D hC coordinateTail rhsTail v S hleft hmul hready hmaster h223 h184 h220 h221 hN hV hcoordinates hsize haSrc hbSrc hrhs hvk hfresh hbo hhf hdf
  have hw : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  change S.R 132 = cstream A w (chirpLine s D)++(cstream A w (chirpLine s C)++rhsTail) at hrhs
  rw [hw] at hrhs
  have hblank (k : Fin 224) (hk : k.val < 31) (_hk0 : k ≠ 0) : S.R k = [] :=
    hmul (⟨k.val,by omega⟩ : Fin 64)
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := cyclicBoundaryRhsPhysical_exec (body := body) B q V a b (by omega) hs ha hb
    C D coordinateTail rhsTail v S hN hV hcoordinates hmaster hsize haSrc hbSrc
    hrhs (hmul 0) hfresh hblank
  let rhs := (List.range B.card).map (fun j => (if a ≤ (bFoldAt s B j).val ∧ (bFoldAt s B j).val < b then C (bFoldAt s B j) else D (bFoldAt s B j)))
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 206 (cstream A w rhs)}
  have he₁' : Exec body cyclicBoundaryRhsPhysical (mk v S) n₁ (mk v₁ S₁) := by simpa [S₁,rhs,hvk,hw] using he₁
  have hstate : boundaryFactorState S₁ = Function.update (boundaryFactorState S) .vk (cstream A w rhs) :=
    boundaryFactorState_update_rhs S _
  obtain ⟨v₂,S₂,n₂,hu₂,hn₂,he₂,hinp,hout,hL,hlegacy,hframe,hpost⟩ := generatedBoundaryNormalizeSolve_exec (body := body)
    hQ hA p u l target rhsExp B W columns hp hlen hformat hstage v₁ S₁ hleft
    (by
      intro i
      have hi206 : boundaryFactorMulReg i ≠ 206 := by
        intro heq
        have hv := congrArg (fun k : Fin 224 => k.val) heq
        have hi := i.isLt
        change i.val = 206 at hv
        omega
      simpa only [S₁,Function.update_of_ne hi206] using hmul i)
    (by rw [hstate]; exact hready.update_vk _)
    (by simpa [S₁] using hmaster) (by simpa [S₁] using h223) (by simpa [S₁] using h184)
    (by simpa [S₁] using h220) (by simpa [S₁] using h221) rhs (by simp [rhs]) (by
      intro a ha
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
      exact hC _ (bFoldAt_mem s B j (List.mem_range.mp hj)))
    (by rw [hstate]; rfl) (by rw [hstate]; simpa using hbo)
    (by rw [hstate]; simpa using hhf) (by rw [hstate]; simpa using hdf)
  change n₂ ≤ generatedBoundaryNormalizeCost q B.card+4*B.card*w+4*W*w+8+bandLinePassCost w B.card W at hn₂
  have hcost : n₁+n₂ ≤ cyclicBoundaryRhsPrepareCost B q V a b+generatedBoundaryNormalizeCost q B.card+4*B.card*w+4*W*w+8+
      bandLinePassCost w B.card W := by omega
  have hframe₁ : RsbFr boundaryFactorReg S S₁ :=
    ⟨rfl,rfl,rfl,fun i hi => Function.update_of_ne (hi .vk).symm _ _⟩
  refine ⟨v₂,S₂,n₁+n₂,hu₂.trans hu₁,hcost,Exec.seq he₁' he₂,hinp,hout,hL,?_,hframe₁.trans hframe,?_⟩
  · intro i
    have hi206 : boundaryFactorLegacyReg i ≠ 206 := by
      intro heq
      have hv := congrArg (fun k : Fin 224 => k.val) heq
      have hi := i.isLt
      change i.val = 206 at hv
      omega
    exact (hlegacy i).trans (by simp only [S₁,Function.update_of_ne hi206])
  · rw [hstate] at hpost
    simpa only [Function.update_idem] using hpost

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
