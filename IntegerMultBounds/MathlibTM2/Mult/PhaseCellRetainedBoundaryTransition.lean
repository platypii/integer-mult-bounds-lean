module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedBoundaryRecovered
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCleanComponentTransition
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPhysicalRecoveryPublishedHalo
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRecoveryBudget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetirePublishedBoundary
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseBoundaryWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryPublish
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRecoveryReady

/-! Recover a real halo line and restore the entire borrowed boundary workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.BandFactor

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def retainedBoundaryTransition (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 224 Q A U :=
  .seq (retainedBoundaryRecovered hR hQ) cleanComponentTransition

theorem retainedBoundaryTransition_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (F : ZMod s → GaussianInt) (hF : ∀ i, ‖value (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p target) 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) (F i)‖ ≤ (2 : ℝ)^2)
    (v : HS 224 Q A U) (S : Stacks 224 A) (tail : List (Fin (A+4)))
    (h109 : S.R 109 = []) (h115 : S.R 115 = []) (h116 : S.R 116 = [])
    (hleft : ∀ i : Fin 224, S.L i = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p target) 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p target) 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) l s t u (PhaseCellBand.width p u) 0 0 (cstream A (executionWidth p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p target) 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) (chirpLine s F)++tail) (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S)))))
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (h0 : S.R 0 = [])
    (h139 : S.R 139 = [])
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = []) (h147 : S.R 147 = []) 
    (h151 : S.R 151 = []) (h153 : S.R 153 = [])
    (h152 : S.R 152 = []) (hnew : ∀ i : Fin 224, 154 ≤ i.val → S.R i = [])
    (next parkedTail : List (Fin (A+4)))
    (hnext : next.length = s*executionWidth p l (initialSchurTarget p u
      (boundaryTableBits p (boundaryRecoveryTarget p target) 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
    (hparked : S.R 144 = next++parkedTail) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let solveTarget := boundaryRecoveryTarget p target
    let bits := boundaryTableBits p solveTarget 2 B.card
    let band := PhaseCellBand.width p u
    let V := publicationGeometryWidth t band
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ∃ vsolve Ssolve nsolve vunfold Sunfold nunfold v₀ S₀ n₀, ∃ solution : List GaussianInt,
      let G := boundarySolutionField B solution
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) (retainedBoundarySolve hR hQ)
        (mk v S) nsolve (mk vsolve Ssolve) ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) (retainedBoundaryRealUnfold hR hQ)
        (mk v S) nunfold (mk vunfold Sunfold) ∧
      n₀ ≤ retainedBoundarySolveCost p u l s t a b solveTarget+
        (2*(([189,191,198,204] : List (Fin 224)).map fun i => (Ssolve.R i).length).sum+9)+
        generatedBoundaryUnfoldCost B.card w+(B.card*(12*w+9)+12)+
        (2*(([189,191,198,206] : List (Fin 224)).map fun i => (Sunfold.R i).length).sum+9)+
        generatedBoundaryUnfoldCost B.card V+(4*(B.card*V)+4)+
        generateBoundaryAdvancesCost B.card V w s+93*s*w+45 ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) (retainedBoundaryPublished hR hQ)
        (mk v S) n₀ (mk v₀ S₀) ∧
      ∀ x : ZMod s → ℝ,
      SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x (fun i => (value q (F i)).re) →
      ∃ v' n, ∃ E : ZMod s → GaussianInt,
        let Y := fun i => realPartWord (publicationField t band a b E G i)
        let S' : Stacks 224 A := {S with R := Function.update (Function.update (Function.update S.R
          110 (next++tail)) 144 parkedTail) 145 (cstream A w (chirpLine s Y)++S.R 145)}
        v'.user = v.user ∧ n ≤ n₀+recoveryToleranceCost p l s t u bits 2 a b+
          haloBoundaryRetirementCostBound s t band a b w+releaseBoundaryWorkspaceCost s w S₀+cleanComponentTransitionCost q s ∧
        Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
          (embTab componentReg (embTab groupReg body))))) (retainedBoundaryTransition hR hQ)
          (mk v S) n (mk v' S') ∧
        PhaseCellInterface.ErrorOn (haloVertices s a b)
          (fun i => publishedCellRead q w (0 : ZMod s) (S'.R 145) i) x (1/(2 : ℝ)^target) ∧
        LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
          q l s t u band 0 0 (next++tail)
          (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S')))) := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let bits := boundaryTableBits p (boundaryRecoveryTarget p target) 2 B.card
  let band := PhaseCellBand.width p u
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  obtain ⟨vsolve,Ssolve,nsolve,vunfold,Sunfold,nunfold,v₀,S₀,n₀,solution,
    hesolve,heunfold,hn₀,he₀,hrec⟩ := retainedBoundaryRecovered_spec (body := body)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad F hF v S tail
    h109 h115 h116 hleft hready haMaster hbMaster h0 h139 h127 h138 h143 h147 h151 h153 h152 hnew
  refine ⟨vsolve,Ssolve,nsolve,vunfold,Sunfold,nunfold,v₀,S₀,n₀,solution,hesolve,heunfold,hn₀,he₀,?_⟩
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
  have hfresh (i : Fin 224) (hi : i ∈ ([131,134,135,136] : List (Fin 224))) : S.R i = [] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg]
        using hready.fresh 131 (by simp)
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg]
        using hready.fresh 134 (by simp)
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg]
        using hready.fresh 135 (by simp)
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg]
        using hready.fresh 136 (by simp)
  have hsource : S.R 110 = cstream A w (chirpLine s F)++tail := hready.source
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := cleanComponentTransition_exec
    (body := embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
      (embTab componentReg (embTab groupReg body))))) q s
    (cstream A w (chirpLine s F)) (cstream A w (chirpLine s Y)) next tail (S.R 132) parkedTail
    (by simp [hwq,chirpLine]) (by simp [hwq,chirpLine]) (by simpa only [← hwq] using hnext)
    v₁ S₁ (by simpa [S₁] using hq) (by simpa [S₁] using hs)
    (by simpa [S₁] using hsource) (by simp [S₁]) (by simpa [S₁] using hparked)
    (by simpa [S₁] using h94) (by simpa [S₁] using hfresh 131 (by simp))
    (by simpa [S₁] using hfresh 134 (by simp)) (by simpa [S₁] using hfresh 135 (by simp))
    (by simpa [S₁] using hfresh 136 (by simp)) (by simpa [S₁] using h147)
  let S₂ : Stacks 224 A := {S with R := Function.update (Function.update (Function.update S.R
    110 (next++tail)) 144 parkedTail) 145 (cstream A w (chirpLine s Y)++S.R 145)}
  refine ⟨v₂,n₁+n₂,E,hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl ?_,?_,?_⟩
  · exact Nat.add_le_add hn₁ hn₂
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h110 : i = 110 <;> by_cases h132 : i = 132 <;> by_cases h144 : i = 144 <;> by_cases h145 : i = 145 <;>
      simp [S₂,S₁,h110,h132,h144,h145] <;> rfl
  · intro i hi
    have hh := herror i hi
    change ‖publishedCellRead q w (0 : ZMod s) (cstream A w (chirpLine s Y)++S.R 145) i-x i‖ ≤ _
    change ‖publishedCellRead q w (0 : ZMod s) (cstream A w (chirpLine s Y)++S.R 132) i-x i‖ ≤ _ at hh
    simpa only [publishedCellRead,ZMod.val_zero,Nat.sub_zero,
      cstream_word w (chirpLine s Y) (S.R 145) i.val (by simpa using i.val_lt),
      cstream_word w (chirpLine s Y) (S.R 132) i.val (by simpa using i.val_lt)] using hh
  · change LengthKeyReady _ _ _ _ _ _ _ _ _ _ _
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S₂))))
    rw [boundaryRecoveryProject_transition]
    exact hready.update_source (next++tail)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
