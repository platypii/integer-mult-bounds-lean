module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedResidualSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryUnscaleStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBoundaryNormalizeSolveStock

/-! The retained-factor residual solve executes normalization, both triangular
passes, unscaling and publication within shared numerical workspace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def preparedResidualSolveWorkspace (D E R C q w N W : ℕ) : ℕ :=
  realScalarWorkspace D w N+realScalarWorkspace E w N+2000*(q+1)+boundarySolveWorkspace R C w N W

theorem preparedResidualSolve_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (p u l target rhsExp : ℕ) {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hp : 2 ≤ p) (hlen : columns.length = B.card)
    (D E R C : ℕ)
    (hpushD : mnProgPush (cmulBlock (rsbCr boundaryFactorReg .vk .dtab .ya)
      (rmulOne (P := P) (Q := Q) (A := A) (U := U) boundaryFactorMulReg
        boundaryFactorMulReg_injective (by decide) hQ (rsbCr boundaryFactorReg .vk .dtab .ya))) ≤ D)
    (hpushE : mnProgPush (cmulBlock (rsbCr boundaryFactorReg .dout .dtab .ya)
      (rmulOne (P := P) (Q := Q) (A := A) (U := U) boundaryFactorMulReg
        boundaryFactorMulReg_injective (by decide) hQ (rsbCr boundaryFactorReg .dout .dtab .ya))) ≤ E)
    (hpushR : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U) boundaryFactorMulReg
      boundaryFactorMulReg_injective (by decide) hQ (rsbCr boundaryFactorReg .hv .xa .hc)) ≤ R)
    (hpushC : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U) boundaryFactorMulReg
      boundaryFactorMulReg_injective (by decide) hQ (rsbCr boundaryFactorReg .ya .xs .pr)) ≤ C) :
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
      ∀ depth, ExecWithin (embTab preparedBoundaryCoreReg body)
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          preparedResidualSolveWorkspace D E R C q w B.card W) depth
        (preparedResidualSolve hQ) (mk v S) n
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
    generatedBoundaryNormalizeSolve_exec_within (body := body) hQ hA p u l target rhsExp B W columns hp hlen D R C hpushD hpushR hpushC
      hformat hstage (embDn preparedBoundaryCoreReg v) T hleft hmul hready hmaster h223 h184 h220 h221 b hb hbound hvk hbo hhf hdf
  have hT₁ : T₁ = {T with R := Function.update (Function.update T.R 206 []) 217 (cstream A w ys)} :=
    boundarySolve_frame_exact T T₁ _ hframe hlegacy hpost
  rw [hT₁] at he₁
  obtain ⟨v₁',hv₁',hu₁',he₁'⟩ := exec_emb_ovr (ι := id) (body' := embTab preparedBoundaryCoreReg body)
    preparedBoundaryCoreReg_injective (fun _ => rfl) (he₁ 0).toExec v rfl S rfl
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
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := preparedBoundaryUnscale_exec_within (body := body) hQ hA q p hpq ys hsol E hpushE
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
  refine ⟨v₂,n₁+n₂,hu₂.trans (hu₁'.trans hu₁),?_,?_⟩
  · rw [hys] at hn₂
    exact Nat.add_le_add hn₁ hn₂
  · intro depth
    have ht₁ := exec_emb_within_stock_of_exec (ι := id) (body' := embTab preparedBoundaryCoreReg body) preparedBoundaryCoreReg_injective
      (fun _ => rfl) (he₁ depth) v rfl S rfl he₁''
    have ht₂ := he₂ depth
    rw [hys,←hw] at ht₂
    have ht := mn_seq_within_add ht₁ ht₂
    refine (ht.mono (by
      intro d z hz
      change mnSize z+d ≤ mnSize (mk v S)+depth+
        ((realScalarWorkspace D w B.card+1000*(q+1)+boundarySolveWorkspace R C w B.card W)+
          (realScalarWorkspace E w B.card+1000*(q+1))) at hz
      change mnSize z+d ≤ mnSize (mk v S)+depth+preparedResidualSolveWorkspace D E R C q w B.card W
      unfold preparedResidualSolveWorkspace
      omega)).cast rfl ?_
    apply congrArg (mk v₂)
    change {S₁ with R := (Function.update (Function.update S₁.R 217 []) 224
      (cstream A w (ys.map (unscaleBoundaryWord q))++S₁.R 224))} =
      {S with R := (Function.update (Function.update S.R 206 []) 224
      (cstream A w (ys.map (unscaleBoundaryWord q))++S.R 224))}
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi206 : i = 206 <;> by_cases hi217 : i = 217 <;> by_cases hi224 : i = 224 <;>
      simp [S₁,hi206,hi217,hi224,h217]


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
