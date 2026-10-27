module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedBoundaryTransition
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedBoundaryFinish
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPhysicalRecoveryPublishedHalo
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRecoveryBudget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetirePublishedBoundary
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseBoundaryWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryPublish
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRecoveryReady

/-! Execute both generated real solves and restore ownership around a complex halo result. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.BandFactor

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def retainedBoundaryPair (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 224 Q A U :=
  .seq (retainedBoundaryTransition hR hQ) (retainedBoundaryFinish hR hQ)

noncomputable def retainedBoundaryPairCost (p u l s t a b target : ℕ) [NeZero s] : ℕ :=
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  2*retainedBoundaryRecoveredCost p u l s t a b (target+1)+
    cleanComponentTransitionCost q s+cleanFinishComponentsCost q s

theorem retainedBoundaryPair_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (H : ZMod s → GaussianInt) (hH : ∀ i, ‖value (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) (H i)‖ ≤ (2 : ℝ)^2)
    (parkedTail original originalTail : List (Fin (A+4)))
    (h144 : S.R 144 = cstream A (executionWidth p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) (chirpLine s H)++parkedTail)
    (horiginal : original.length = s*(executionWidth p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)) (h146 : S.R 146 = original++originalTail)
    (x y : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x
      (fun i => (value (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) (F i)).re))
    (hy : SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) y
      (fun i => (value (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) (H i)).re)) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ∃ v' n, ∃ X Y : ZMod s → GaussianInt,
      let Z := cstream A w (chirpLine s (fun i => pairComponentWord (X i) (Y i)))++S.R 132
      let S' : Stacks 224 A := {S with R := (Function.update (Function.update (Function.update (Function.update S.R
        110 (original++tail)) 144 parkedTail) 146 originalTail) 132 Z)}
      v'.user = v.user ∧ n ≤ retainedBoundaryPairCost p u l s t a b target ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) (retainedBoundaryPair hR hQ) (mk v S) n (mk v' S') ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b) (pairedCellRead q w (S'.R 132))
        (fun i => (⟨x i,y i⟩ : ℂ)) (1/(2 : ℝ)^target) := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
  let band := PhaseCellBand.width p u
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  obtain ⟨solution,hstep⟩ :=
    retainedBoundaryTransition_spec (body := body) (target := target+1)
      hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad F hF v S tail
      h109 h115 h116 hleft hready haMaster hbMaster h0 h139 h127 h138 h143 h147 h151 h153 h152 hnew
      (cstream A w (chirpLine s H)) parkedTail (by change (cstream A w (chirpLine s H)).length = s*w; simp [chirpLine]) h144
  obtain ⟨v₁,n₁,E,hu₁,hn₁,he₁,herror₁,hready₁⟩ := hstep x hx
  let X := fun i => realPartWord (publicationField t band a b E (boundarySolutionField B solution) i)
  let M : Stacks 224 A := {S with R := Function.update (Function.update (Function.update S.R
    110 (cstream A w (chirpLine s H)++tail)) 144 parkedTail) 145 (cstream A w (chirpLine s X)++S.R 145)}
  have hnewM : ∀ i : Fin 224, 154 ≤ i.val → M.R i = [] := by
    intro i hi
    have h110 : i ≠ 110 := by intro h; subst i; norm_num at hi
    have h144' : i ≠ 144 := by intro h; subst i; norm_num at hi
    have h145' : i ≠ 145 := by intro h; subst i; norm_num at hi
    simpa [M,h110,h144',h145'] using hnew i hi
  obtain ⟨solution₂,hfinish⟩ :=
    retainedBoundaryFinish_spec (body := body) (target := target)
      hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad H hH v₁ M tail
      (by simpa [M] using h109) (by simpa [M] using h115) (by simpa [M] using h116) hleft hready₁
      (by simpa [M] using haMaster) (by simpa [M] using hbMaster)
      (by simpa [M] using h0) (by simpa [M] using h139) (by simpa [M] using h127)
      (by simpa [M] using h138) (by simpa [M] using h143) (by simpa [M] using h147)
      (by simpa [M] using h151) (by simpa [M] using h153) (by simpa [M] using h152) hnewM
      X x (S.R 145) original originalTail herror₁ (by simp [M]; rfl) horiginal (by simpa [M] using h146)
  obtain ⟨v₂,n₂,E₂,hu₂,hn₂,he₂,herror₂⟩ := hfinish y hy
  let Y := fun i => realPartWord (publicationField t band a b E₂ (boundarySolutionField B solution₂) i)
  refine ⟨v₂,n₁+n₂,X,Y,hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl ?_,?_⟩
  · simpa only [retainedBoundaryPairCost,two_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
      using Nat.add_le_add hn₁ hn₂
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h110 : i = 110 <;> by_cases h132 : i = 132 <;> by_cases h144' : i = 144 <;>
      by_cases h145' : i = 145 <;> by_cases h146' : i = 146 <;>
      simp [M,h110,h132,h144',h145',h146'] <;> rfl
  · exact herror₂

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
