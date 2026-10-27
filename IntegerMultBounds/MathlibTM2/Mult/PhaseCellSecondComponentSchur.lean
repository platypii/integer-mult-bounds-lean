module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedRecoveryTransition
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleasedSchurResidual

/-! Retain the first result and execute the initial Schur pass on the second component. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def secondComponentSchur (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 148 Q A U :=
  .seq (retainedRecoveryTransition hR hQ) (releasedSchurResidual hR hQ)

theorem secondComponentSchur_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (C B : ZMod s → GaussianInt) (x : ZMod s → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hεtarget : ε ≤ 1/(2 : ℝ)^recoveryTarget p target)
    (hB : ∀ i, ‖value (executionPrecision p l
      (recoveryFirstTarget p (recoveryTarget p target) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp) (B i)‖ ≤ (2 : ℝ)^rhsExp)
    (hCreal : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b, (C i).im = 0)
    (hxB : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b,
      |(value (executionPrecision p l (recoveryFirstTarget p (recoveryTarget p target) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp)
        (C i)).re-x i| ≤ ε)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x
      (fun i => (value (executionPrecision p l
        (recoveryFirstTarget p (recoveryTarget p target) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp) (B i)).re))
    (v : HS 148 Q A U) (S : Stacks 148 A) (residual tail sourceTail parkedTail : List (Fin (A+4)))
    (hresidual : residual.length = s*executionWidth p l
      (recoveryFirstTarget p (recoveryTarget p target) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp)
    (hready : LengthKeyReady (2^15*p)
      (executionStagePrecision p l (recoveryFirstTarget p (recoveryTarget p target) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp+1)
      (executionPrecision p l (recoveryFirstTarget p (recoveryTarget p target) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp)
      l s t u (PhaseCellBand.width p u) 0 0
      (residual++(cstream A (executionWidth p l
        (recoveryFirstTarget p (recoveryTarget p target) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp) (chirpLine s B)++tail)) (embStk componentReg S))
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hsource : S.R 132 = cstream A
      (executionWidth p l (recoveryFirstTarget p (recoveryTarget p target) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp)
      (chirpLine s C)++sourceTail)
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = [])
    (Next : ZMod s → GaussianInt)
    (hNext : ∀ i, ‖value (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp) (Next i)‖ ≤ (2 : ℝ)^rhsExp)
    (hparked : S.R 144 = cstream A (executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp)
      (chirpLine s Next)++parkedTail) (h147 : S.R 147 = []) :
    let q := executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp
    let w := executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp
    let band := PhaseCellBand.width p u
    let I := haloInterior s t band a b
    let boundary := haloBoundary s t band a b
    ∃ v' n, ∃ D E : ZMod s → GaussianInt, ∃ R : (ZMod s → ℝ) → ZMod s → ℝ,
      let G := fun i => realPartWord (publicationField t band a b D C i)
      let H := guardedCouplingRowField (2^15*p) q t u band a b false E (fun i => realPartWord (Next i))
      let input := cstream A w (chirpLine s H)++(cstream A w (chirpLine s Next)++tail)
      let S' : Stacks 148 A := {S with R := (Function.update (Function.update (Function.update
        (Function.update S.R 110 input) 132 sourceTail) 144 parkedTail)
        145 (cstream A w (chirpLine s G)++S.R 145))}
      (∀ c, SchurDominance.Solves (realMatrix s t p u) I (R c) c) ∧
      v'.user = v.user ∧ n ≤ (recoveryToleranceCost p l s t u target rhsExp a b+
        componentTransitionCost q s)+releasedSchurResidualCost p l s t u target rhsExp a b ∧
      Exec (embTab componentReg (embTab groupReg body)) (secondComponentSchur hR hQ)
        (mk v S) n (mk v' S') ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b)
        (fun i => publishedCellRead q w (0 : ZMod s) (S'.R 145) i) x (1/(2 : ℝ)^target) ∧
      (∀ i, (H i).im = 0) ∧
      (∀ i, ‖value q (H i)‖ ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp)
        (8*p+1) (couplingCountExponent p u)) ∧
      (∀ i ∈ boundary, 8*p*|(value q (H i)).re-SchurDominance.residual (realMatrix s t p u) I R
        (fun i => (value q (Next i)).re) i| ≤ 1/(2 : ℝ)^(recoveryTarget p target+2)) ∧
      (∀ i, publishedCellRead q w (0 : ZMod s) (S'.R 110) i = (value q (H i)).re) ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1)
        q l s t u band 0 0 input (embStk componentReg S') := by
  dsimp only
  let q := executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp
  let w := executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp
  let band := PhaseCellBand.width p u
  let next := cstream A w (chirpLine s Next)
  obtain ⟨v₁,n₁,D,hu₁,hn₁,he₁,herror,hready₁⟩ := retainedRecoveryTransition_spec (body := body)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad C B x ε hε hεtarget
    hB hCreal hxB hx v S residual tail sourceTail next parkedTail hresidual hready haMaster hbMaster hsource
    h127 h138 h143 (by simp [next,w,chirpLine,initialSchurTarget]) hparked h147
  let G := fun i => realPartWord (publicationField t band a b D C i)
  let S₁ : Stacks 148 A := {S with R := (Function.update (Function.update (Function.update
    (Function.update S.R 110 (next++tail)) 132 sourceTail) 144 parkedTail)
    145 (cstream A w (chirpLine s G)++S.R 145))}
  have hready₁' : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1)
      q l s t u band 0 0 (next++tail) (embStk componentReg S₁) := hready₁
  obtain ⟨v₂,n₂,E,R,hRsolve,hu₂,hn₂,he₂,hHreal,hHnorm,hHerror,hread,hready₂⟩ := releasedSchurResidual_spec (body := body)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad Next hNext v₁ S₁ tail
    (by simpa [S₁] using h127) (by simpa [S₁] using h138) (by simpa [S₁] using h143)
    (by simpa [S₁] using haMaster) (by simpa [S₁] using hbMaster) hready₁'
    (by simpa [S₁] using h147)
  let H := guardedCouplingRowField (2^15*p) q t u band a b false E (fun i => realPartWord (Next i))
  let input := cstream A w (chirpLine s H)++(next++tail)
  let S₂ : Stacks 148 A := {S₁ with R := Function.update S₁.R 110 input}
  let Sfinal : Stacks 148 A := {S with R := (Function.update (Function.update (Function.update
    (Function.update S.R 110 input) 132 sourceTail) 144 parkedTail)
    145 (cstream A w (chirpLine s G)++S.R 145))}
  have hframe : S₂ = Sfinal := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h110 : k = 110 <;> by_cases h132 : k = 132 <;>
      by_cases h144 : k = 144 <;> by_cases h145 : k = 145 <;>
      simp [S₂,S₁,Sfinal,h110,h132,h144,h145]
  have he₂' : Exec (embTab componentReg (embTab groupReg body)) (releasedSchurResidual hR hQ)
      (mk v₁ S₁) n₂ (mk v₂ S₂) := by simpa [S₂,S₁,input,next,H,q,w,band] using he₂
  rw [hframe] at he₂'
  have hread' : ∀ i, publishedCellRead q w (0 : ZMod s) (S₂.R 110) i = (value q (H i)).re := by
    simpa [S₂,S₁,input,next,H,q,w,band] using hread
  rw [hframe] at hread'
  have hready₂' : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1)
      q l s t u band 0 0 input (embStk componentReg S₂) := by
    simpa [S₂,S₁,input,next,H,q,w,band] using hready₂
  rw [hframe] at hready₂'
  refine ⟨v₂,n₁+n₂,D,E,R,hRsolve,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,
    Exec.seq he₁ he₂',?_,hHreal,hHnorm,hHerror,hread',hready₂'⟩
  simpa [Sfinal,S₁,G,w,q,band,initialSchurTarget] using herror

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
