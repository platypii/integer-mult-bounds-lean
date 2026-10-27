module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyComputedBoundaryRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyBoundaryResidualSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResidualBoundaryAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResidualBoundaryFormat
public import IntegerMultBounds.NLogN.PhaseCellBoundary

/-! Generate the actual residual and solve it on an existing computed boundary page. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 263 Q A U}

noncomputable def familyComputedBoundarySolve (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 263 Q A U :=
  .seq (familyComputedBoundaryRhs recovery hR hQ) (familyBoundaryResidualSolve hQ)

theorem familyComputedBoundarySolve_spec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let band := PhaseCellBand.width p u
    let W := 12*band+1
    let bits := boundaryTableBits p target 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    ∀ (columns : List (ZMod s → GaussianInt)),
    let AZ := factorRankIntegerMatrix B W columns
    let Lc := naturalLineLc q K W B.card AZ
    let Uc := naturalLineUc q K W B.card AZ
    let rcs := naturalLineRcs q K W B.card AZ
    columns.length = B.card → ColumnFamilyFormat w columns →
    StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card)
      (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^bits)) (2+(B.card : ℝ)*(1/(2 : ℝ)^bits)) →
    (∀ i ∈ B, ∀ j ∈ B, |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j-
      (SchurDominance.run (realMatrix s t p u) (haloVertices s a b) (haloInterior s t band a b).toList).1 i j| ≤ 1/(2 : ℝ)^bits) →
    ∀ (F : ZMod s → GaussianInt), (∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2) →
    ∀ (v : HS 263 Q A U) (S : Stacks 263 A) (tail coordinateTail pageTail familyTail : List (Fin (A+4))) (V : ℕ),
    let σ := boundaryFactorState (embStk sharedPageRecoveryReg (embStk familyBoundaryReg S))
    LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u band 0 0 (cstream A w (chirpLine s F)++tail)
      (embStk familyCouplingSourceReg S) →
    CouplingPageCacheReady recovery (2^15*p) q w s t u band a b pageTail (embStk familyInverseLegacyReg S) →
    S.R 260 = weightKeyFamily (haloWeightKeyPages A w q (2^15*p) s t u band a b (haloLengthKeys s t band a b))++familyTail →
    (∀ i ∈ ([(256 : Fin 263),257,258,259,261,262] : List (Fin 263)), S.R i = []) →
    (S.R 141).length = a → (S.R 142).length = b →
    (∀ i : Fin 240, (embStk familyBoundaryReg S).L i = []) → (∀ i : Fin 64, S.R ⟨i.val,by omega⟩ = []) →
    BoundarySolveReady σ q w W B.card →
    σ .bo = cstream A w (Lc.map colC).flatten →
    σ .hf = cstream A w (Uc.map colC).flatten →
    σ .df = cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt)) →
    s ≤ 2^V → (S.R 116).length = B.card → (S.R 115).length = V → (S.R 160).length = w →
    S.R 109 = cstream A V ((bFoldOrder s B).map (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++coordinateTail →
    (S.R 119).length = q →
    (∀ i ∈ ([127,138,143,106,139,206,223,184,220,221,225] : List (Fin 263)), S.R i = []) →
    ∃ v' n, ∃ D C : ZMod s → GaussianInt, ∃ solution : List GaussianInt,

      let S' : Stacks 263 A := {S with R := (Function.update
        (Function.update (Function.update S.R 110 (cstream A w (chirpLine s C)++S.R 110)) 132
          (cstream A w (chirpLine s D)++S.R 132)) 224 (cstream A w solution++S.R 224))}
      v'.user = v.user ∧
      n ≤ familyRealInteriorResidualCost A p l s t u (initialSchurTarget p u bits 2) 2 a b+
        boundaryRhsPrepareCost V w B.card s+preparedResidualSolveCost q w B.card W ∧
      Exec body (familyComputedBoundarySolve recovery hR hQ) (mk v S) n (mk v' S') ∧
      solution.length = B.card ∧ (∀ z ∈ solution, Fits w z) ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
        q l s t u band 0 0 (cstream A w (chirpLine s C)++S.R 110)
        (embStk familyCouplingSourceReg S') ∧
      ∀ x : ZMod s → ℝ, Solves (realMatrix s t p u) (haloVertices s a b) x (fun i => (value q (F i)).re) →
        ∀ i < B.card, ‖value q (solution.getD i 0) - (x (bFoldAt s B i) : ℂ)‖ ≤ 3/(2 : ℝ)^target ∧
          ‖value q (solution.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p 2 := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let band := PhaseCellBand.width p u
  let W := 12*band+1
  let bits := boundaryTableBits p target 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let K := factorNewtonSteps p q
  intro columns hlen hformat hstage htable F hF v S tail coordinateTail pageTail familyTail V hready hcache hfamily hfamilyFresh ha hb hleft hmul
    hsolve hbo hhf hdf hsV hN hV hw hcoordinates hmaster hclean
  let AZ := factorRankIntegerMatrix B W columns
  let Lc := naturalLineLc q K W B.card AZ
  let Uc := naturalLineUc q K W B.card AZ
  let rcs := naturalLineRcs q K W B.card AZ
  have hblank : ∀ r : Fin 263, 1 ≤ r.val → r.val < 7 → S.R r = [] := by
    intro r hr1 hr7
    exact hmul ⟨r.val,by omega⟩
  obtain ⟨v₁,n₁,D,C,R,hRsolve,hu₁,hn₁,he₁,hreal,hmag,herr,hread,hready₁⟩ := familyComputedBoundaryRhs_spec
    (body := body) (target := bits) (rhsExp := 2) recovery hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad
    F hF v S tail pageTail familyTail (hclean _ (by simp)) (hclean _ (by simp)) (hclean _ (by simp)) ha hb hready hcache hfamily hfamilyFresh
    V hsV coordinateTail hN hV hw hcoordinates (hmul 0) (hclean _ (by simp)) (hclean _ (by simp)) hblank
  let rhs := (List.range B.card).map (fun j => C (bFoldAt s B j))
  have hrhs : rhs.length = B.card := by simp [rhs]
  have hbound : ∀ z ∈ rhs, |gv q z.re| ≤ (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2)
      (8*p+1) (couplingCountExponent p u) ∧ |gv q z.im| ≤
      (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2) (8*p+1) (couplingCountExponent p u) := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hz
    exact ⟨(Complex.abs_re_le_norm (value q (C (bFoldAt s B i)))).trans (hmag _),
      (Complex.abs_im_le_norm (value q (C (bFoldAt s B i)))).trans (hmag _)⟩
  let raw := cstream A w rhs
  let S₁ : Stacks 263 A := {S with R := (Function.update
    (Function.update (Function.update S.R 110 (cstream A w (chirpLine s C)++S.R 110)) 132
      (cstream A w (chirpLine s D)++S.R 132)) 206 raw)}
  have h206 := hclean 206 (by simp)
  have he₁' : Exec body (familyComputedBoundaryRhs recovery hR hQ) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [S₁,raw,rhs,h206,List.append_nil] using he₁
  have hstate : boundaryFactorState (embStk preparedBoundaryCoreReg (embStk sharedPageSolveReg (embStk familyBoundaryReg S₁))) =
      Function.update (boundaryFactorState (embStk sharedPageRecoveryReg (embStk familyBoundaryReg S))) .vk raw := by
    funext r
    cases r <;> first | rfl | (rename_i c; cases c <;> rfl)
  have hm : ∀ i : Fin 64, (embStk preparedBoundaryCoreReg (embStk sharedPageSolveReg (embStk familyBoundaryReg S₁))).R
      (boundaryFactorMulReg i) = [] := by
    intro i
    have hn (k : Fin 263) (hk : 64 ≤ k.val) : (⟨i.val,by omega⟩ : Fin 263) ≠ k := by
      intro he
      have hh := congrArg (fun j : Fin 263 => j.val) he
      have hi := i.isLt
      change i.val = k.val at hh
      omega
    change S₁.R ⟨i.val,by omega⟩ = []
    simpa only [S₁,Function.update_of_ne (hn 206 (by decide)),
      Function.update_of_ne (hn 132 (by decide)),Function.update_of_ne (hn 110 (by decide))] using hmul i
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := familyBoundaryResidualSolve_exec (body := body) hQ hA p u l target 2 B W columns hp hlen
    hformat hstage rhs hrhs hbound v₁ S₁ (fun i => hleft _) hm (by rw [hstate]; exact hsolve.update_vk raw)
    (by rw [hstate]; rfl) (by rw [hstate]; exact hbo) (by rw [hstate]; exact hhf) (by rw [hstate]; exact hdf)
    (by simpa [S₁] using hmaster) (by simpa [S₁] using hclean 223 (by simp))
    (by simpa [S₁] using hclean 184 (by simp)) (by simpa [S₁] using hclean 220 (by simp))
    (by simpa [S₁] using hclean 221 (by simp)) (by simpa [S₁] using hclean 225 (by simp))
  let solution := (bandSolveVec q W Lc Uc rcs (rhs.map (normalizeBoundaryWord q (q/2-1)))).map (unscaleBoundaryWord q)
  have hfit := boundary_residual_solution_format A p u l target 2 B W columns hp
    (Nat.le_trans (by decide : 4 ≤ 96) hA) hlen hformat hstage rhs hrhs hbound
  refine ⟨v₂,n₁+n₂,D,C,solution,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,(Exec.seq he₁' he₂).cast rfl ?_,
    hfit.1,hfit.2,?_,?_⟩
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi206 : i = 206 <;> by_cases hi224 : i = 224 <;>
      simp [S₁,hi206,hi224,h206] <;> rfl
  · let S₀ : Stacks 263 A := {S with R := (Function.update
      (Function.update S.R 110 (cstream A w (chirpLine s C)++S.R 110)) 132
        (cstream A w (chirpLine s D)++S.R 132))}
    change LengthKeyReady _ _ _ _ _ _ _ _ _ _ _
      (embStk familyCouplingSourceReg {S₀ with R := Function.update S₀.R 224 (cstream A w solution++S.R 224)})
    rw [familyCouplingSource_high_update S₀ 224 (by decide)]
    change LengthKeyReady _ _ _ _ _ _ _ _ _ _ _
      (embStk familyCouplingSourceReg {S₀ with R := Function.update S₀.R 206 (raw++S.R 206)}) at hready₁
    rw [familyCouplingSource_high_update S₀ 206 (by decide)] at hready₁
    exact hready₁
  · intro x hx
    let I := haloInterior s t band a b
    let M := realMatrix s t p u
    have hU : I ∪ B = haloVertices s a b := haloInterior_union_boundary s t band a b
    let : NeZero t := ⟨by omega⟩
    have hM : DominatesOn M (I ∪ B) (1/(8*(p : ℝ))) := by
      rw [hU]
      exact dominates_mono M Finset.univ (haloVertices s a b) _ (Finset.subset_univ _)
        (matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget)
    have hmagC : ∀ j ∈ B, |gv q (C j).re| ≤ (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2)
        (8*p+1) (couplingCountExponent p u) ∧ |gv q (C j).im| ≤
        (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2) (8*p+1) (couplingCountExponent p u) := by
      intro j hj
      exact ⟨(Complex.abs_re_le_norm (value q (C j))).trans (hmag _),
        (Complex.abs_im_le_norm (value q (C j))).trans (hmag _)⟩
    exact (boundary_residual_solution_accuracy A p u l target 2 B W columns hp
      (Nat.le_trans (by decide : 4 ≤ 96) hA) hlen C hformat hstage M I
      (haloInterior_disjoint_boundary s t band a b) hM R hRsolve x (fun i => (value q (F i)).re)
      (by rw [hU]; exact hx) (by
        intro j hj
        exact (Complex.abs_re_le_norm (value q (F j))).trans (hF j))
      (by rw [hU]; exact htable) hmagC (fun j _ => hreal j) herr).2

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
