module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageBoundaryAmbient
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageRetireResidual
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRecoveryBudget

/-! Recover a full halo from a borrowed boundary batch row while retaining the factor page and scatter setup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 240 Q A U}

noncomputable def sharedPageBoundaryRecovered (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 240 Q A U :=
  .seq sharedPageBoundaryAmbient (.seq (sharedPageRecoveryPublishedHalo hR hQ) sharedPageRetireResidual)

theorem sharedPageBoundaryRecovered_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let solveTarget := boundaryRecoveryTarget p target
    let bits := boundaryTableBits p solveTarget 2 B.card
    let band := PhaseCellBand.width p u
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ∀ (F : ZMod s → GaussianInt) (solution : List GaussianInt) (x : ZMod s → ℝ),
    solution.length = B.card → (∀ z ∈ solution, Fits w z) →
    (∀ i < B.card, ‖value q (solution.getD i 0) - (x (bFoldAt s B i) : ℂ)‖ ≤ 3/(2 : ℝ)^solveTarget) →
    (∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2) →
    SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x (fun i => (value q (F i)).re) →
    ∀ (v : HS 240 Q A U) (S : Stacks 240 A) (residual tail batchTail borrowed : List (Fin (A+4))),
    residual.length = s*w →
    LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u band 0 0 (residual++(cstream A w (chirpLine s F)++tail))
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg (embStk sharedPageRecoveryReg S))))) →
    (S.R 141).length = a → (S.R 142).length = b →
    (∀ i, S.L i = []) → (∀ i : Fin 64, S.R ⟨i.val,by omega⟩ = []) →
    S.R 116 = List.replicate B.card tick → (S.R 192).length = B.card →
    (S.R 160).length = w → (S.R 121).length = s →
    S.R 239 = gatherControls A (originAdvances w 0 (boundaryScatterOrigins s B)++[0])++borrowed →
    S.R 224 = cstream A w solution++batchTail →
    (∀ i ∈ ([184,217,223,201,208,211,215,220,231,232,233,234,235,236,237,127,138,143] : List (Fin 240)), S.R i = []) →
    ∃ v' n, ∃ E : ZMod s → GaussianInt,
      let G := boundarySolutionField B solution
      let Y := fun i => realPartWord (publicationField t band a b E G i)
      let S' : Stacks 240 A := {S with R := (Function.update
        (Function.update S.R 110 (cstream A w (chirpLine s F)++tail))
        132 (cstream A w (chirpLine s Y)++S.R 132))}
      v'.user = v.user ∧
      n ≤ sharedPageBoundaryAmbientCost B.card w s+recoveryToleranceCost p l s t u bits 2 a b+
        sharedPageRetireResidualCost s w ∧
      Exec body (sharedPageBoundaryRecovered hR hQ) (mk v S) n (mk v' S') ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b)
        (fun i => publishedCellRead q w (0 : ZMod s) (S'.R 132) i) x (1/(2 : ℝ)^target) := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let solveTarget := boundaryRecoveryTarget p target
  let bits := boundaryTableBits p solveTarget 2 B.card
  let band := PhaseCellBand.width p u
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  intro F solution x hlen hfit herror hF hx v S residual tail batchTail borrowed hresidual hready
    ha hb hleft hmul hc hrows hwidth' hs hadv hsource hclean
  have hw : 1 ≤ w := by dsimp [w,executionWidth]; omega
  have hz : ∀ i ∈ ([184,217,223,201,208,211,215,220,231,232,233,234,235,236,237] : List (Fin 240)), S.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hclean _ (by simp)
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hbytes⟩ := sharedPageBoundaryAmbient_exec (body := body) (Nat.le_trans (by decide : 4 ≤ 96) hA)
    s B w hw solution hlen v S batchTail borrowed hleft hmul hc hrows hwidth' hs hadv hsource hz
  let G := boundarySolutionField B solution
  let S₁ : Stacks 240 A := {S with R := Function.update S.R 132 (cstream A w (chirpLine s G)++S.R 132)}
  have hproject : embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
      (embStk boundaryFactorLegacyReg (embStk sharedPageRecoveryReg S₁)))) =
      {embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg (embStk sharedPageRecoveryReg S)))) with R :=
        (Function.update (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
          (embStk boundaryFactorLegacyReg (embStk sharedPageRecoveryReg S))))).R 132
          (cstream A w (chirpLine s G)++S.R 132))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    let e := fun j : Fin 144 => sharedPageRecoveryReg (boundaryFactorLegacyReg
      (tableReg (boundaryArithmeticReg (componentReg j))))
    have hinj : Function.Injective e := sharedPageRecoveryReg_injective.comp
      (boundaryFactorLegacyReg_injective.comp (tableReg_injective.comp
        (boundaryArithmeticReg_injective.comp componentReg_injective)))
    have h132 : e 132 = 132 := rfl
    by_cases hi : i = 132
    · subst i; rfl
    have he : e i ≠ 132 := by rw [← h132]; exact hinj.ne hi
    change (Function.update S.R 132 (cstream A w (chirpLine s G)++S.R 132)) (e i) =
      Function.update (fun j => S.R (e j)) 132 (cstream A w (chirpLine s G)++S.R 132) i
    rw [Function.update_of_ne he,Function.update_of_ne hi]
  have hready₁ : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u band 0 0 (residual++(cstream A w (chirpLine s F)++tail))
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg (embStk sharedPageRecoveryReg S₁))))) := by
    rw [hproject]
    exact hready.update_output _
  have hboundary : ∀ i ∈ B, |(value q (G i)).re-x i| ≤ 3/(2 : ℝ)^solveTarget := by
    intro i hi
    have hh := hbytes q x (3/(2 : ℝ)^solveTarget) hfit herror i hi
    dsimp only at hh
    rw [boundarySolutionField_published_read A q w (Nat.le_trans (by decide : 4 ≤ 96) hA)
      hw B solution hlen hfit (S.R 132) i] at hh
    simpa only [Real.norm_eq_abs] using hh
  obtain ⟨v₂,n₂,E,hu₂,hn₂,he₂,hfinal⟩ := sharedPageRecoveryPublishedHalo_at_precision (body := body)
    (target := target) (workingTarget := bits) (rhsExp := 2)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad G F x
    (3/(2 : ℝ)^solveTarget) (by positivity) (boundaryRecovery_workingTarget p target B.card)
    (boundaryRecovery_error_budget p target) hF (fun i _ => boundarySolutionField_im B solution i) hboundary hx
    v₁ S₁ residual tail (S.R 132) hresidual hready₁ (by simpa [S₁] using ha) (by simpa [S₁] using hb)
    (by change S₁.R 132 = cstream A w (chirpLine s G)++S.R 132; rfl)
    (by simpa [S₁] using hclean 127 (by simp))
    (by simpa [S₁] using hclean 138 (by simp)) (by simpa [S₁] using hclean 143 (by simp))
  let R := couplingRowField (2^15*p) q t u band a b true G F
  let Y := fun i => realPartWord (publicationField t band a b E G i)
  let S₂ : Stacks 240 A := {S₁ with R := (Function.update
    (Function.update S₁.R 110 (cstream A w (chirpLine s R)++(cstream A w (chirpLine s F)++tail)))
    132 (cstream A w (chirpLine s Y)++S.R 132))}
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := sharedPageRetireResidual_exec (body := body) s w
    (cstream A w (chirpLine s R)) (cstream A w (chirpLine s F)++tail)
    (by simp [chirpLine]) v₂ S₂ (by simpa [S₂,S₁] using hs) (by simpa [S₂,S₁] using hwidth')
    (by rfl) (by simpa [S₂,S₁] using hclean 231 (by simp))
    (by simpa [S₂,S₁] using hclean 232 (by simp)) (by simpa [S₂,S₁] using hclean 233 (by simp))
  refine ⟨v₃,n₁+(n₂+n₃),E,hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_,?_⟩
  · change n₁+(n₂+n₃) ≤ sharedPageBoundaryAmbientCost B.card w s+
      recoveryToleranceCost p l s t u bits 2 a b+sharedPageRetireResidualCost s w
    have hn₁' : n₁ ≤ sharedPageBoundaryAmbientCost B.card w s := hn₁
    have hn₂' : n₂ ≤ recoveryToleranceCost p l s t u bits 2 a b := hn₂
    have hn₃' : n₃ ≤ sharedPageRetireResidualCost s w := hn₃
    exact (Nat.add_le_add hn₁' (Nat.add_le_add hn₂' hn₃')).trans_eq (Nat.add_assoc _ _ _).symm
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi110 : i = 110 <;> by_cases hi132 : i = 132 <;>
      simp [S₂,S₁,hi110,hi132] <;> rfl
  · exact hfinal

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
