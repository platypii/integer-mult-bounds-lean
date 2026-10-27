module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedBoundaryRecovered
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCleanFinishComponents
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairedPhysicalRead
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPhysicalRecoveryPublishedHalo
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRecoveryBudget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetirePublishedBoundary
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseBoundaryWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryPublish
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRecoveryReady

/-! Execute the second generated solve, publish the paired halo and restore the original source. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.BandFactor

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def retainedBoundaryFinish (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 224 Q A U :=
  .seq (retainedBoundaryRecovered hR hQ) cleanFinishComponents

theorem retainedBoundaryFinish_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (F : ZMod s → GaussianInt) (hF : ∀ i, ‖value (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) (F i)‖ ≤ (2 : ℝ)^2)
    (v : HS 224 Q A U) (S : Stacks 224 A) (tail : List (Fin (A+4)))
    (h109 : S.R 109 = []) (h115 : S.R 115 = []) (h116 : S.R 116 = [])
    (hleft : ∀ i : Fin 224, S.L i = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) l s t u (PhaseCellBand.width p u) 0 0 (cstream A (executionWidth p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) (chirpLine s F)++tail) (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S)))))
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (h0 : S.R 0 = [])
    (h139 : S.R 139 = [])
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = []) (h147 : S.R 147 = []) 
    (h151 : S.R 151 = []) (h153 : S.R 153 = [])
    (h152 : S.R 152 = []) (hnew : ∀ i : Fin 224, 154 ≤ i.val → S.R i = [])
    (X : ZMod s → GaussianInt) (realTarget : ZMod s → ℝ)
    (savedTail original originalTail : List (Fin (A+4)))
    (hX : PhaseCellInterface.ErrorOn (haloVertices s a b)
      (fun i => publishedCellRead (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
        (executionWidth p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) (0 : ZMod s) (S.R 145) i) realTarget (1/(2 : ℝ)^(target+1)))
    (h145 : S.R 145 = cstream A (executionWidth p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) (chirpLine s X)++savedTail)
    (horiginal : original.length = s*(executionWidth p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)) (h146 : S.R 146 = original++originalTail) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let solveTarget := boundaryRecoveryTarget p (target+1)
    let bits := boundaryTableBits p solveTarget 2 B.card
    let band := PhaseCellBand.width p u
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ∃ solution : List GaussianInt,
      let G := boundarySolutionField B solution
      ∀ x : ZMod s → ℝ,
      SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x (fun i => (value q (F i)).re) →
      ∃ v' n, ∃ E : ZMod s → GaussianInt,
        let Y := fun i => realPartWord (publicationField t band a b E G i)
        let Z := cstream A w (chirpLine s (fun i => pairComponentWord (X i) (Y i)))++S.R 132
        let S' : Stacks 224 A := {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          110 (original++tail)) 145 savedTail) 146 originalTail) 132 Z)}
        v'.user = v.user ∧ n ≤ retainedBoundaryRecoveredCost p u l s t a b (target+1)+cleanFinishComponentsCost q s ∧
        Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
          (embTab componentReg (embTab groupReg body))))) (retainedBoundaryFinish hR hQ)
          (mk v S) n (mk v' S') ∧
        PhaseCellInterface.ErrorOn (haloVertices s a b) (pairedCellRead q w (S'.R 132))
          (fun i => (⟨realTarget i,x i⟩ : ℂ)) (1/(2 : ℝ)^target) := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
  let band := PhaseCellBand.width p u
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  obtain ⟨solution,hrec⟩ := retainedBoundaryRecovered_spec (body := body) (target := target+1)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad F hF v S tail
    h109 h115 h116 hleft hready haMaster hbMaster h0 h139 h127 h138 h143 h147 h151 h153 h152 hnew
  refine ⟨solution,?_⟩
  intro x hx
  obtain ⟨v₁,n₁,E,hu₁,hn₁,he₁,herror⟩ := hrec x hx
  let G := boundarySolutionField B solution
  let Y := fun i => realPartWord (publicationField t band a b E G i)
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 132 (cstream A w (chirpLine s Y)++S.R 132)}
  have hwq : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  have hq : (S.R 119).length = q := by
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,groupHeaderValue]
      using hready.masters (119,112) (by simp [groupHeaderCopies])
  have hs : (S.R 121).length = s := by
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,groupHeaderValue]
      using hready.masters (121,97) (by simp [groupHeaderCopies])
  have h94 : S.R 94 = [] := by
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg]
      using hready.blank 94 (by decide) (by decide) (by decide)
  have hfresh (i : Fin 224) (hi : i ∈ ([131,134,135,136,140] : List (Fin 224))) : S.R i = [] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg]
        using hready.fresh 131 (by simp)
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg]
        using hready.fresh 134 (by simp)
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg]
        using hready.fresh 135 (by simp)
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg]
        using hready.fresh 136 (by simp)
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg]
        using hready.fresh 140 (by simp)
  have hsource : S.R 110 = cstream A w (chirpLine s F)++tail := hready.source
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := cleanFinishComponents_exec
    (body := embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
      (embTab componentReg (embTab groupReg body))))) (by omega : 4 ≤ A) q s (chirpLine s X) (chirpLine s Y)
    (by simp [chirpLine]) (by simp [chirpLine]) (cstream A w (chirpLine s F)) tail savedTail (S.R 132)
    original originalTail (by simp [hwq,chirpLine]) (by simpa only [← hwq] using horiginal)
    v₁ S₁ (by simpa [S₁] using hq) (by simpa [S₁] using hs)
    (by simpa [S₁] using hsource) (by simpa [S₁,← hwq] using h145) (by simp [S₁,hwq])
    (by simpa [S₁] using h146) (by simpa [S₁] using h94)
    (by simpa [S₁] using hfresh 131 (by simp)) (by simpa [S₁] using hfresh 134 (by simp))
    (by simpa [S₁] using hfresh 135 (by simp)) (by simpa [S₁] using hfresh 136 (by simp))
    (by simpa [S₁] using hfresh 140 (by simp)) (by simpa [S₁] using h147)
  simp only [← hwq,pairComponentWords_chirpLine] at he₂
  refine ⟨v₂,n₁+n₂,E,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,(Exec.seq he₁ he₂).cast rfl ?_,?_⟩
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h110 : i = 110 <;> by_cases h132 : i = 132 <;> by_cases h145' : i = 145 <;> by_cases h146' : i = 146 <;>
      simp [S₁,h110,h132,h145',h146'] <;> rfl
  · have hX' : PhaseCellInterface.ErrorOn (haloVertices s a b)
        (fun i => publishedCellRead q w (0 : ZMod s) (cstream A w (chirpLine s X)++savedTail) i)
        realTarget (1/(2 : ℝ)^(target+1)) := by
      simpa only [h145] using hX
    have hY' : PhaseCellInterface.ErrorOn (haloVertices s a b)
        (fun i => publishedCellRead q w (0 : ZMod s) (cstream A w (chirpLine s Y)++S.R 132) i)
        x (1/(2 : ℝ)^(target+1)) := herror
    have hh := pairedComponents_physical_accuracy (q := q) (w := w) (by omega : 4 ≤ A) X Y
      (haloVertices s a b) (fun i => (⟨realTarget i,x i⟩ : ℂ))
      (1/(2 : ℝ)^(target+1)) (1/(2 : ℝ)^(target+1)) (S.R 132) savedTail (S.R 132) hX' hY'
    rw [component_error_budget] at hh
    exact hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
