module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedBoundaryPair
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPhysicalOriginalComponentInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedBoundaryFinish
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPhysicalRecoveryPublishedHalo
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRecoveryBudget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetirePublishedBoundary
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseBoundaryWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryPublish
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRecoveryReady

/-! Execute a complex halo solve from its original input and restore the complete borrowed stack bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.BandFactor

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def retainedComplexBoundary (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 224 Q A U :=
  .seq physicalOriginalComponentInputs (retainedBoundaryPair hR hQ)

noncomputable def retainedComplexBoundaryCost (p u l s t a b target : ℕ) [NeZero s] : ℕ :=
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  originalComponentInputsCost q s+retainedBoundaryPairCost p u l s t a b target

theorem retainedComplexBoundary_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (h152 : S.R 152 = []) (hnew : ∀ i : Fin 224, 154 ≤ i.val → S.R i = []) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ∀ x y : ZMod s → ℝ,
      SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x (fun i => (value q (F i)).re) →
      SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) y (fun i => (value q (F i)).im) →
      ∃ v' n, ∃ G : ZMod s → GaussianInt,
        let S' : Stacks 224 A := {S with R := Function.update S.R 132 (cstream A w (chirpLine s G)++S.R 132)}
        v'.user = v.user ∧ n ≤ retainedComplexBoundaryCost p u l s t a b target ∧
        Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
          (embTab componentReg (embTab groupReg body))))) (retainedComplexBoundary hR hQ) (mk v S) n (mk v' S') ∧
        PhaseCellInterface.ErrorOn (haloVertices s a b) (pairedCellRead q w (S'.R 132))
          (fun i => (⟨x i,y i⟩ : ℂ)) (1/(2 : ℝ)^target) := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
  let band := PhaseCellBand.width p u
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let FRe := fun i => realPartWord (F i)
  let FIm := fun i => imagPartWord (F i)
  have hwq : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  have hreadyq : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u band 0 0 (cstream A w (chirpLine s F)++tail)
      (embStk componentReg (embStk boundaryComponentReg S)) := hready
  rw [hwq] at hreadyq
  obtain ⟨v₀,n₀,hu₀,hn₀,he₀,hready₀⟩ := physicalOriginalComponentInputs_exec
    (body := embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
      (embTab componentReg (embTab groupReg body))))) (q := q)
    (by omega : 4 ≤ A) F tail v S hreadyq h147
  simp only [← hwq] at he₀ hready₀
  let M : Stacks 224 A := {S with R := Function.update (Function.update (Function.update S.R
    146 (cstream A w (chirpLine s F)++S.R 146))
    110 (cstream A w (chirpLine s FRe)++tail)) 144 (cstream A w (chirpLine s FIm)++S.R 144)}
  have hnewM : ∀ i : Fin 224, 154 ≤ i.val → M.R i = [] := by
    intro i hi
    have h110 : i ≠ 110 := by intro h; subst i; norm_num at hi
    have h144 : i ≠ 144 := by intro h; subst i; norm_num at hi
    have h146 : i ≠ 146 := by intro h; subst i; norm_num at hi
    simpa [M,h110,h144,h146] using hnew i hi
  have hRe : ∀ i, ‖value q (FRe i)‖ ≤ (2 : ℝ)^2 := by
    intro i
    exact (componentWords_norm_le q (F i)).1.trans (hF i)
  have hIm : ∀ i, ‖value q (FIm i)‖ ≤ (2 : ℝ)^2 := by
    intro i
    exact (componentWords_norm_le q (F i)).2.trans (hF i)
  intro x y hx hy
  obtain ⟨v₁,n₁,X,Y,hu₁,hn₁,he₁,herror⟩ := retainedBoundaryPair_spec (body := body) (target := target)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad FRe hRe v₀ M tail
    (by simpa [M] using h109) (by simpa [M] using h115) (by simpa [M] using h116) hleft hready₀
    (by simpa [M] using haMaster) (by simpa [M] using hbMaster)
    (by simpa [M] using h0) (by simpa [M] using h139) (by simpa [M] using h127)
    (by simpa [M] using h138) (by simpa [M] using h143) (by simpa [M] using h147)
    (by simpa [M] using h151) (by simpa [M] using h153) (by simpa [M] using h152) hnewM
    FIm hIm (S.R 144) (cstream A w (chirpLine s F)) (S.R 146)
    (by simp [M]; rfl) (by change (cstream A w (chirpLine s F)).length = s*w; simp [chirpLine])
    (by simp [M]) x y
    (by simpa only [FRe,value_realPartWord_re] using hx) (by simpa only [FIm,value_imagPartWord_re] using hy)
  let G := fun i => pairComponentWord (X i) (Y i)
  refine ⟨v₁,n₀+n₁,G,hu₁.trans hu₀,?_,(Exec.seq he₀ he₁).cast rfl ?_,?_⟩
  · exact Nat.add_le_add hn₀ hn₁
  · apply congrArg (mk v₁)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    have hsource : S.R 110 = cstream A w (chirpLine s F)++tail := hready.source
    by_cases h110 : i = 110 <;> by_cases h132 : i = 132 <;> by_cases h144 : i = 144 <;> by_cases h146 : i = 146 <;>
      simp [M,h110,h132,h144,h146,hsource,G]
  · exact herror

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
