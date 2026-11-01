module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySolvePhysicalStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBoundaryScalingStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBoundaryNormalizeSolve

/-! Compose generated normalization with the allocated bounded physical solve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.Sizes
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

theorem generatedBoundaryNormalizeSolve_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (p u l target rhsExp : ℕ) {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hp : 2 ≤ p) (hlen : columns.length = B.card)
    (D R C : ℕ)
    (hpushD : mnProgPush (cmulBlock (rsbCr boundaryFactorReg .vk .dtab .ya)
      (rmulOne (P := P) (Q := Q) (A := A) (U := U) boundaryFactorMulReg
        boundaryFactorMulReg_injective (by decide) hQ (rsbCr boundaryFactorReg .vk .dtab .ya))) ≤ D)
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
    ∀ (v : HS 224 Q A U) (S : Stacks 224 A),
    let σ := boundaryFactorState S
    (∀ i, S.L i = []) → (∀ i : Fin 64, S.R (boundaryFactorMulReg i) = []) →
    BoundarySolveReady σ q w W B.card →
    (S.R 119).length = q → S.R 223 = [] → S.R 184 = [] → S.R 220 = [] → S.R 221 = [] →
    ∀ (xs : List GaussianInt), xs.length = B.card →
    (∀ z ∈ xs, |gv q z.re| ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u) ∧ |gv q z.im| ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u)) →
    σ .vk = cstream A w xs →
    σ .bo = cstream A w (Lc.map colC).flatten →
    σ .hf = cstream A w (Uc.map colC).flatten →
    σ .df = cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt)) →
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ generatedBoundaryNormalizeCost q B.card+4*B.card*w+4*W*w+8+bandLinePassCost w B.card W ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (realScalarWorkspace D w B.card+1000*(q+1)+boundarySolveWorkspace R C w B.card W)) depth
        (generatedBoundaryNormalizeSolve hQ) (mk v S) n (mk v' S')) ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ i : Fin 154, S'.R (boundaryFactorLegacyReg i) = S.R (boundaryFactorLegacyReg i)) ∧
      RsbFr boundaryFactorReg S S' ∧
      boundaryFactorState S' = Function.update (Function.update σ .vk []) .dout
        (cstream A w (bandSolveVec q W Lc Uc rcs (xs.map (normalizeBoundaryWord q (q/2-1))))) := by
  dsimp only
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  intro hformat hstage v S hleft hmul hready hmaster h223 h184 h220 h221 xs hlenxs hbound hsrc hbo hhf hdf
  have hw : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  have hready' : RsbReady (boundaryFactorState S) (2*q+8) q := hw ▸ hready.ready
  have hsrc' : S.R 206 = cstream A (2*q+8) xs := by
    change S.R 206 = cstream A w xs at hsrc
    rw [hw] at hsrc
    exact hsrc
  obtain ⟨hq,heven,hmag,hguard⟩ := boundary_normalization_precision p u l target rhsExp B.card
  change 2 ≤ q at hq
  change q%2 = 0 at heven
  have hsplit : q = q/2+(q/2-1)+1 := by omega
  have hbound' : ∀ z ∈ xs, |gv q z.re| ≤ (2 : ℝ)^(q/2) ∧ |gv q z.im| ≤ (2 : ℝ)^(q/2) := by
    intro z hz
    exact boundary_residual_normalization_bound p u l target rhsExp B.card z (hbound z hz)
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := generatedBoundaryNormalize_exec_within (body := body) hQ hA q hq heven xs hbound' D hpushD v S
    hleft hmul hready' hmaster h184 h220 h221 h223
    (hready.empty .ya (by simp [boundarySolveScratch])) (hready.empty .ac2 (by simp [boundarySolveScratch])) hsrc'
  let ys := xs.map (normalizeBoundaryWord q (q/2-1))
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 206 (cstream A w ys)}
  have he₁' : ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
      (realScalarWorkspace D w B.card+1000*(q+1))) depth
      (generatedBoundaryNormalize hQ) (mk v S) n₁ (mk v₁ S₁) := by
    intro depth
    have ht := he₁ depth
    simpa only [S₁,ys,hw,hlenxs] using ht
  have hstate : boundaryFactorState S₁ = Function.update (boundaryFactorState S) .vk (cstream A w ys) :=
    boundaryFactorState_update S .vk _
  obtain ⟨v₂,S₂,n₂,hu₂,hn₂,he₂,hinp,hout,hL,hlegacy,hframe,hpost⟩ := boundary_foldedSolve_physical_exec_within (body := body)
    hQ hA p u l target rhsExp B W columns hp hlen R C hpushR hpushC hformat hstage v₁ S₁ hleft (by
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
      exact normalizeBoundaryWord_bound q (q/2) (q/2-1) hsplit x (hbound' x hx))
    (by rw [hstate]; rfl) (by rw [hstate]; simpa using hbo)
    (by rw [hstate]; simpa using hhf) (by rw [hstate]; simpa using hdf)
  change n₂ ≤ 4*B.card*w+4*W*w+8+bandLinePassCost w B.card W at hn₂
  rw [hlenxs] at hn₁
  have hcost : n₁+n₂ ≤ generatedBoundaryNormalizeCost q B.card+4*B.card*w+4*W*w+8+
      bandLinePassCost w B.card W := by omega
  have hframe₁ : RsbFr boundaryFactorReg S S₁ :=
    ⟨rfl,rfl,rfl,fun i hi => Function.update_of_ne (hi .vk).symm _ _⟩
  refine ⟨v₂,S₂,n₁+n₂,hu₂.trans hu₁,hcost,(fun depth => mn_seq_within_add (he₁' depth) (he₂ depth)),hinp,hout,hL,?_,hframe₁.trans hframe,?_⟩
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
