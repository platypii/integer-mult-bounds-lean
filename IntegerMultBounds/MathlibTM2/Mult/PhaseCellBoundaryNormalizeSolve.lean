module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryNormalizePhysical
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySolvePhysical

/-! Normalize and solve a gathered residual with its actual magnitude bound. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.MathlibTM2.Mult.Sizes

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

noncomputable def boundaryNormalizeSolve (hQ : SS.states ≤ Q) : Pr P 224 Q A U :=
  .seq (boundaryNormalizePhysical hQ) (boundaryFoldedSolve hQ)

theorem boundaryNormalizeSolve_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (p u l target rhsExp E e : ℕ) {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hp : 2 ≤ p) (hlen : columns.length = B.card) :
    let bits := boundaryTableBits p target rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    let AZ := factorRankIntegerMatrix B W columns
    let Lc := naturalLineLc q K W B.card AZ
    let Uc := naturalLineUc q K W B.card AZ
    let rcs := naturalLineRcs q K W B.card AZ
    q = E+e+1 → ColumnFamilyFormat w columns →
    StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card)
      (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^bits))
      (2+(B.card : ℝ)*(1/(2 : ℝ)^bits)) →
    ∀ (v : HS 224 Q A U) (S : Stacks 224 A),
    let σ := boundaryFactorState S
    (∀ i, S.L i = []) → (∀ i : Fin 64, S.R (boundaryFactorMulReg i) = []) →
    BoundarySolveReady σ q w W B.card →
    (S.R 223).length = e → S.R 184 = [] → S.R 220 = [] → S.R 221 = [] →
    ∀ (xs : List GaussianInt), xs.length = B.card →
    (∀ z ∈ xs, |gv q z.re| ≤ (2 : ℝ)^E ∧ |gv q z.im| ≤ (2 : ℝ)^E) →
    σ .vk = cstream A w xs →
    σ .bo = cstream A w (Lc.map colC).flatten →
    σ .hf = cstream A w (Uc.map colC).flatten →
    σ .df = cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt)) →
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ boundaryNormalizePhysicalCost q e B.card+4*B.card*w+4*W*w+8+bandLinePassCost w B.card W ∧
      Exec body (boundaryNormalizeSolve hQ) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ i : Fin 154, S'.R (boundaryFactorLegacyReg i) = S.R (boundaryFactorLegacyReg i)) ∧
      boundaryFactorState S' = Function.update (Function.update σ .vk []) .dout
        (cstream A w (bandSolveVec q W Lc Uc rcs (xs.map (normalizeBoundaryWord q e)))) := by
  dsimp only
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  intro hqe hformat hstage v S hleft hmul hready he h184 h220 h221 xs hlenxs hbound hsrc hbo hhf hdf
  have hw : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  have hready' : RsbReady (boundaryFactorState S) (2*q+8) q := hw ▸ hready.ready
  have hsrc' : S.R 206 = cstream A (2*q+8) xs := by
    change S.R 206 = cstream A w xs at hsrc
    rw [hw] at hsrc
    exact hsrc
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := boundaryNormalizePhysical_exec (body := body) hQ hA q E e hqe xs hbound v S
    hleft hmul hready' he hsrc' h184 h220 h221
    (hready.empty .ya (by simp [boundarySolveScratch])) (hready.empty .ac2 (by simp [boundarySolveScratch]))
  let ys := xs.map (normalizeBoundaryWord q e)
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 206 (cstream A w ys)}
  have he₁' : Exec body (boundaryNormalizePhysical hQ) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [S₁,ys,hw] using he₁
  have hstate : boundaryFactorState S₁ = Function.update (boundaryFactorState S) .vk (cstream A w ys) :=
    boundaryFactorState_update S .vk _
  obtain ⟨v₂,S₂,n₂,hu₂,hn₂,he₂,hinp,hout,hL,hlegacy,_hframe,hpost⟩ := boundary_foldedSolve_physical_exec (body := body)
    hQ hA p u l target rhsExp B W columns hp hlen hformat hstage v₁ S₁ hleft (by
      intro i
      have hi206 : boundaryFactorMulReg i ≠ 206 := by
        intro hi
        have hv := congrArg (fun k : Fin 224 => k.val) hi
        have hi' := i.isLt
        change i.val = 206 at hv
        omega
      simpa only [S₁,Function.update_of_ne hi206] using hmul i)
    (by rw [hstate]; exact hready.update_vk _) ys (by simp [ys,hlenxs]) (by
      intro z hz
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
      exact normalizeBoundaryWord_bound q E e hqe x (hbound x hx))
    (by rw [hstate]; rfl) (by rw [hstate]; simpa using hbo)
    (by rw [hstate]; simpa using hhf) (by rw [hstate]; simpa using hdf)
  change n₂ ≤ 4*B.card*w+4*W*w+8+bandLinePassCost w B.card W at hn₂
  rw [hlenxs] at hn₁
  have hcost : n₁+n₂ ≤ boundaryNormalizePhysicalCost q e B.card+4*B.card*w+4*W*w+8+
      bandLinePassCost w B.card W := by omega
  refine ⟨v₂,S₂,n₁+n₂,hu₂.trans hu₁,hcost,Exec.seq he₁' he₂,hinp,hout,hL,?_,?_⟩
  · intro i
    have hi206 : boundaryFactorLegacyReg i ≠ 206 := by
      intro hi
      have hv := congrArg (fun k : Fin 224 => k.val) hi
      have hi' := i.isLt
      change i.val = 206 at hv
      omega
    exact (hlegacy i).trans (by simp only [S₁,Function.update_of_ne hi206])
  · rw [hstate] at hpost
    simpa only [Function.update_idem] using hpost

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
