module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRhsPhysical
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySolvePhysical

/-! Gather and solve a bounded ambient boundary RHS using retained factor tables. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.Sizes

/-- The gather destination is exactly the triangular solver's RHS port. -/
theorem boundaryFactorState_update_rhs {A : ℕ} (S : Stacks 224 A) (xs : List (Fin (A+4))) :
    boundaryFactorState {S with R := Function.update S.R 206 xs} =
      Function.update (boundaryFactorState S) .vk xs := by
  funext r
  by_cases hr : r = .vk
  · subst r; rfl
  · have hreg : boundaryFactorReg r ≠ 206 := boundaryFactorReg_injective.ne hr
    simp [boundaryFactorState,Function.update_of_ne hreg,Function.update_of_ne hr]

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

noncomputable def boundaryGatherSolve (hQ : SS.states ≤ Q) : Pr P 224 Q A U :=
  .seq boundaryRhsPhysical (boundaryFoldedSolve hQ)

theorem boundaryGatherSolve_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (p u l target rhsExp : ℕ) {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (W V : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hp : 2 ≤ p) (hlen : columns.length = B.card)
    (hs : s ≤ 2^V) :
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
    ∀ (C : ZMod s → GaussianInt), (∀ i ∈ B, |gv q (C i).re| ≤ 1/2 ∧ |gv q (C i).im| ≤ 1/2) →
    ∀ (coordinateTail rhsTail : List (Fin (A+4))) (v : HS 224 Q A U) (S : Stacks 224 A),
    let σ := boundaryFactorState S
    (∀ i, S.L i = []) → (∀ i : Fin 64, S.R (boundaryFactorMulReg i) = []) →
    BoundarySolveReady σ q w W B.card →
    (S.R 116).length = B.card → (S.R 115).length = V →
    S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++coordinateTail →
    S.R 110 = cstream A w (chirpLine s C)++rhsTail →
    S.R 106 = [] → S.R 139 = [] → S.R 206 = [] →
    σ .bo = cstream A w (Lc.map colC).flatten →
    σ .hf = cstream A w (Uc.map colC).flatten →
    σ .df = cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt)) →
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ boundaryRhsPrepareCost V w B.card s+4*B.card*w+4*W*w+8+bandLinePassCost w B.card W ∧
      Exec body (boundaryGatherSolve hQ) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ i : Fin 154, S'.R (boundaryFactorLegacyReg i) = S.R (boundaryFactorLegacyReg i)) ∧
      boundaryFactorState S' = Function.update (Function.update σ .vk []) .dout
        (cstream A w (bandSolveVec q W Lc Uc rcs
          ((List.range B.card).map (fun j => C (bFoldAt s B j))))) := by
  dsimp only
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  intro hformat hstage C hC coordinateTail rhsTail v S hleft hmul hready hN hV hcoordinates hrhs h106 h139 hvk hbo hhf hdf
  have hwidth : (S.R 160).length = w := hready.ready.wn
  have h0 : S.R 0 = [] := hmul 0
  have hblank (r : Fin 224) (_hr1 : 1 ≤ r.val) (hr7 : r.val < 7) : S.R r = [] := by
    exact hmul (⟨r.val,by omega⟩ : Fin 64)
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := boundaryRhsPhysical_exec (body := body) B V w (by omega) hs C C (by intro i hi; rfl)
    coordinateTail rhsTail v S hN hV hwidth hcoordinates hrhs h0 h106 h139 hblank
  let b := (List.range B.card).map (fun j => C (bFoldAt s B j))
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 206 (cstream A w b)}
  have he₁' : Exec body boundaryRhsPhysical (mk v S) n₁ (mk v₁ S₁) := by simpa [S₁,b,hvk] using he₁
  have hstate : boundaryFactorState S₁ = Function.update (boundaryFactorState S) .vk (cstream A w b) :=
    boundaryFactorState_update_rhs S _
  obtain ⟨v₂,S₂,n₂,hu₂,hn₂,he₂,hinp,hout,hL,hlegacy,_hframe,hpost⟩ := boundary_foldedSolve_physical_exec (body := body)
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
    (by rw [hstate]; exact hready.update_vk _) b (by simp [b]) (by
      intro a ha
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
      exact hC _ (bFoldAt_mem s B j (List.mem_range.mp hj)))
    (by rw [hstate]; rfl) (by rw [hstate]; simpa using hbo)
    (by rw [hstate]; simpa using hhf) (by rw [hstate]; simpa using hdf)
  change n₂ ≤ 4*B.card*w+4*W*w+8+bandLinePassCost w B.card W at hn₂
  have hcost : n₁+n₂ ≤ boundaryRhsPrepareCost V w B.card s+4*B.card*w+4*W*w+8+
      bandLinePassCost w B.card W := by omega
  refine ⟨v₂,S₂,n₁+n₂,hu₂.trans hu₁,hcost,Exec.seq he₁' he₂,hinp,hout,hL,?_,?_⟩
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
