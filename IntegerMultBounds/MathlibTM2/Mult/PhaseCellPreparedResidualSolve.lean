module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryReuse
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryUnscale
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBoundaryNormalizeSolve

/-! Normalize an actual residual, solve with a retained factor page, and publish at the original scale. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.BandFactor

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

noncomputable def preparedResidualSolve (hQ : SS.states ≤ Q) : Pr P 226 Q A U :=
  .seq (embProg preparedBoundaryCoreReg id (generatedBoundaryNormalizeSolve hQ))
    (preparedBoundaryUnscale hQ)

def preparedResidualSolveCost (q w N W : ℕ) : ℕ :=
  (generatedBoundaryNormalizeCost q N+4*N*w+4*W*w+8+bandLinePassCost w N W)+
    preparedBoundaryUnscaleCost q N

theorem preparedResidualSolve_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (p u l target rhsExp : ℕ) {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hp : 2 ≤ p) (hlen : columns.length = B.card) :
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
    ∀ (b : List GaussianInt), b.length = B.card →
    (∀ x ∈ b, |gv q x.re| ≤ (2 : ℝ)^couplingRowExponent rhsExp
      (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u) ∧
      |gv q x.im| ≤ (2 : ℝ)^couplingRowExponent rhsExp
      (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u)) →
    ∀ (v : HS 226 Q A U) (S : Stacks 226 A),
    let T := embStk preparedBoundaryCoreReg S
    let σ := boundaryFactorState T
    (∀ i, T.L i = []) → (∀ i : Fin 64, T.R (boundaryFactorMulReg i) = []) →
    BoundarySolveReady σ q w W B.card →
    σ .vk = cstream A w b →
    σ .bo = cstream A w (Lc.map colC).flatten →
    σ .hf = cstream A w (Uc.map colC).flatten →
    σ .df = cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt)) →
    (S.R 119).length = q → S.R 223 = [] → S.R 184 = [] →
    S.R 220 = [] → S.R 221 = [] → S.R 225 = [] →
    ∃ v' n, v'.user = v.user ∧ n ≤ preparedResidualSolveCost q w B.card W ∧
      Exec (embTab preparedBoundaryCoreReg body) (preparedResidualSolve hQ) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 206 []) 224
          (cstream A w ((bandSolveVec q W Lc Uc rcs (b.map (normalizeBoundaryWord q (q/2-1)))).map
            (unscaleBoundaryWord q))++S.R 224))}) := by
  dsimp only
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let K := factorNewtonSteps p q
  let AZ := factorRankIntegerMatrix B W columns
  let Lc := naturalLineLc q K W B.card AZ
  let Uc := naturalLineUc q K W B.card AZ
  let rcs := naturalLineRcs q K W B.card AZ
  intro hformat hstage b hb hbound v S hleft hmul hready hvk hbo hhf hdf hmaster h223 h184 h220 h221 h225
  let T := embStk preparedBoundaryCoreReg S
  let bs := b.map (normalizeBoundaryWord q (q/2-1))
  let ys := bandSolveVec q W Lc Uc rcs bs
  have hys : ys.length = B.card := naturalLineSolve_length q K W B.card AZ bs (by simp [bs,hb])
  obtain ⟨v₁,T₁,n₁,hu₁,hn₁,he₁,hinp,hout,hL,hlegacy,hframe,hpost⟩ :=
    generatedBoundaryNormalizeSolve_exec (body := body) hQ hA p u l target rhsExp B W columns hp hlen
      hformat hstage (embDn preparedBoundaryCoreReg v) T hleft hmul hready hmaster h223 h184 h220 h221 b hb hbound hvk hbo hhf hdf
  have hT₁ : T₁ = {T with R := Function.update (Function.update T.R 206 []) 217 (cstream A w ys)} :=
    boundarySolve_frame_exact T T₁ _ hframe hlegacy hpost
  rw [hT₁] at he₁
  obtain ⟨v₁',hv₁',hu₁',he₁'⟩ := exec_emb_ovr (ι := id) (body' := embTab preparedBoundaryCoreReg body)
    preparedBoundaryCoreReg_injective (fun _ => rfl) he₁ v rfl S rfl
  let S₁ : Stacks 226 A := {S with R := Function.update (Function.update S.R 206 []) 217 (cstream A w ys)}
  have he₁'' : Exec (embTab preparedBoundaryCoreReg body) (embProg preparedBoundaryCoreReg id (generatedBoundaryNormalizeSolve hQ))
      (mk v S) n₁ (mk v₁' S₁) := by
    convert he₁' using 1
    apply congrArg (mk v₁')
    symm
    let T₀ : Stacks 224 A := {T with R := Function.update T.R 206 []}
    change embOvr preparedBoundaryCoreReg ({T₀ with R := Function.update T₀.R 217 (cstream A w ys)} : Stacks 224 A).get S = S₁
    rw [embOvr_updR preparedBoundaryCoreReg_injective]
    dsimp only [T₀]
    rw [embOvr_updR preparedBoundaryCoreReg_injective,embOvr_stk]
    rfl
  have hw : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  have hbits : 4*p+2*Nat.size B.card+36 ≤ q := factor_execution_bits p u l target rhsExp B.card
  have hpq : p ≤ q/2 := by omega
  have hbs : ∀ z ∈ bs, |gv q z.re| ≤ 1/2 ∧ |gv q z.im| ≤ 1/2 := by
    obtain ⟨hq,heven,_,_⟩ := boundary_normalization_precision p u l target rhsExp B.card
    change 2 ≤ q at hq
    change q%2 = 0 at heven
    intro z hz
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
    exact normalizeBoundaryWord_bound q (q/2) (q/2-1) (by omega) x
      (boundary_residual_normalization_bound p u l target rhsExp B.card x (hbound x hx))
  have hsol := boundary_line_allocated_solution_bounds A p u l target rhsExp B W columns
    hp (by omega) hlen hformat hstage bs (by simp [bs,hb]) hbs
  have hstate : boundaryFactorState (embStk preparedBoundaryCoreReg S₁) =
      Function.update (Function.update (boundaryFactorState T) .vk []) .dout (cstream A w ys) := by
    have heq : embStk preparedBoundaryCoreReg S₁ =
        {T with R := Function.update (Function.update T.R 206 []) 217 (cstream A w ys)} := by
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      by_cases hi206 : i = 206
      · subst i; rfl
      by_cases hi217 : i = 217
      · subst i; rfl
      have he206 : preparedBoundaryCoreReg i ≠ 206 := preparedBoundaryCoreReg_injective.ne hi206
      have he217 : preparedBoundaryCoreReg i ≠ 217 := preparedBoundaryCoreReg_injective.ne hi217
      simp only [S₁,T,embStk,Function.comp_def,Function.update_of_ne he206,
        Function.update_of_ne he217,Function.update_of_ne hi206,Function.update_of_ne hi217]
    rw [heq, ← hT₁]
    exact hpost
  have hr : RsbReady (boundaryFactorState (embStk preparedBoundaryCoreReg S₁)) (2*q+8) q := by
    rw [hstate, ← hw]
    exact (hready.ready.update .vk (fun _ => by simp) []).update .dout (fun _ => by simp) _
  have hmul₁ : ∀ i : Fin 64, (embStk preparedBoundaryCoreReg S₁).R (boundaryFactorMulReg i) = [] := by
    intro i
    have hi206 : preparedBoundaryCoreReg (boundaryFactorMulReg i) ≠ 206 := by
      intro hh
      have hh' := congrArg (fun k : Fin 226 => k.val) hh
      change i.val = 206 at hh'
      have hi := i.isLt
      omega
    have hi217 : preparedBoundaryCoreReg (boundaryFactorMulReg i) ≠ 217 := by
      intro hh
      have hh' := congrArg (fun k : Fin 226 => k.val) hh
      change i.val = 217 at hh'
      have hi := i.isLt
      omega
    simpa only [embStk,Function.comp_def,S₁,Function.update_of_ne hi217,
      Function.update_of_ne hi206] using hmul i
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := preparedBoundaryUnscale_exec (body := body) hQ hA q p hpq ys hsol
    v₁' S₁ hleft hmul₁ hr (by simpa [S₁] using hmaster)
    (by simpa [S₁] using h184) (by simpa [S₁] using h220)
    (by simpa [S₁] using h221) (by simpa [S₁] using h223)
    (by
      have hy : S.R 208 = [] := hready.empty .ya (by simp [boundarySolveScratch])
      simpa [S₁] using hy)
    (by
      have hy : S.R 215 = [] := hready.empty .ac2 (by simp [boundarySolveScratch])
      simpa [S₁] using hy)
    (by simp [S₁,hw]) (by simpa [S₁] using h225)
  have h217 : S.R 217 = [] := hready.empty .dout (by simp [boundarySolveScratch])
  refine ⟨v₂,n₁+n₂,hu₂.trans (hu₁'.trans hu₁),?_,(Exec.seq he₁'' he₂).cast rfl ?_⟩
  · rw [hys] at hn₂
    exact Nat.add_le_add hn₁ hn₂
  · apply congrArg (mk v₂)
    change {S₁ with R := (Function.update (Function.update S₁.R 217 []) 224
      (cstream A (2*q+8) (ys.map (unscaleBoundaryWord q))++S₁.R 224))} =
      {S with R := (Function.update (Function.update S.R 206 []) 224
      (cstream A w (ys.map (unscaleBoundaryWord q))++S.R 224))}
    rw [hw]
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi206 : i = 206 <;> by_cases hi217 : i = 217 <;> by_cases hi224 : i = 224 <;>
      simp [S₁,hi206,hi217,hi224,h217]

/-- A consumed residual can be replaced immediately without rebuilding its factor page. -/
theorem preparedResidualSolve_ready {A q w W N : ℕ} (S : Stacks 226 A)
    (output : List (Fin (A+4)))
    (hready : BoundarySolveReady (boundaryFactorState (embStk preparedBoundaryCoreReg S)) q w W N) :
    BoundarySolveReady (boundaryFactorState (embStk preparedBoundaryCoreReg
      {S with R := Function.update (Function.update S.R 206 []) 224 (output++S.R 224)})) q w W N :=
  preparedBoundarySolve_ready S output hready

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
