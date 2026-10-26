module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleasedSchurResidual
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginalInputReady

/-! Prepare a complex RHS and execute the first real Schur-residual pass with its allocated budget. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def preparedSchurResidual (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 148 Q A U :=
  .seq saveOriginalInput (.seq preparedComponentInputs (releasedSchurResidual hR hQ))

def preparedSchurResidualCost (p l s t u target rhsExp a b : ℕ) : ℕ :=
  let firstTarget := initialSchurTarget p u target rhsExp
  let q := executionPrecision p l firstTarget rhsExp
  saveOriginalInputCost q s+(preparedComponentInputsCost q s+
    releasedSchurResidualCost p l s t u target rhsExp a b)

theorem preparedSchurResidual_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (B : ZMod s → GaussianInt)
    (hB : ∀ i, ‖value (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp) (B i)‖ ≤ (2 : ℝ)^rhsExp)
    (v : HS 148 Q A U) (S : Stacks 148 A) (tail : List (Fin (A+4)))
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = [])
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1)
      (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp) (chirpLine s B)++tail) (embStk componentReg S)) (h147 : S.R 147 = []) :
    let q := executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp
    let w := executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp
    let band := PhaseCellBand.width p u
    let I := haloInterior s t band a b
    let boundary := haloBoundary s t band a b
    ∃ v' n, ∃ D : ZMod s → GaussianInt, ∃ R : (ZMod s → ℝ) → ZMod s → ℝ,
      let C := couplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (B i))
      let input := cstream A w (chirpLine s C)++(cstream A w ((chirpLine s B).map realPartWord)++tail)
      let S' : Stacks 148 A := {S with R := (Function.update (Function.update (Function.update S.R 110 input)
        144 (cstream A w ((chirpLine s B).map imagPartWord)++S.R 144))
        146 (cstream A w (chirpLine s B)++S.R 146))}
      (∀ c, SchurDominance.Solves (realMatrix s t p u) I (R c) c) ∧
      v'.user = v.user ∧ n ≤ preparedSchurResidualCost p l s t u target rhsExp a b ∧
      Exec (embTab componentReg (embTab groupReg body)) (preparedSchurResidual hR hQ) (mk v S) n (mk v' S') ∧
      (∀ i, (C i).im = 0) ∧
      (∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp)
        (8*p+1) (couplingCountExponent p u)) ∧
      (∀ i ∈ boundary, 8*p*|(value q (C i)).re-SchurDominance.residual (realMatrix s t p u) I R
          (fun i => (value q (B i)).re) i| ≤ 1/(2 : ℝ)^(recoveryTarget p target+2)) ∧
      (∀ i, publishedCellRead q w (0 : ZMod s) (S'.R 110) i = (value q (C i)).re) ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1) q l s t u band 0 0 input
        (embStk componentReg S') := by
  dsimp only
  let firstTarget := initialSchurTarget p u target rhsExp
  let q := executionPrecision p l firstTarget rhsExp
  let w := executionWidth p l firstTarget rhsExp
  let band := PhaseCellBand.width p u
  let B₁ := fun i => realPartWord (B i)
  let X := cstream A w ((chirpLine s B).map realPartWord)++tail
  let Y := cstream A w ((chirpLine s B).map imagPartWord)++S.R 144
  let original := cstream A w (chirpLine s B)
  let S₀ : Stacks 148 A := {S with R := Function.update S.R 146 (original++S.R 146)}
  let S₁ : Stacks 148 A := {S₀ with R := Function.update (Function.update S₀.R 110 X) 144 Y}
  have hwq : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  have hreadyq : LengthKeyReady (2^15*p) (executionStagePrecision p l firstTarget rhsExp+1)
      q l s t u band 0 0 (cstream A (2*q+8) (chirpLine s B)++tail) (embStk componentReg S) := by
    rw [← hwq]
    exact hready
  obtain ⟨v₀,n₀,hu₀,hn₀,he₀,hready₀⟩ := saveOriginalInput_ready (body := embTab groupReg body)
    (cstream A (2*q+8) (chirpLine s B)) tail (by simp [chirpLine]) v S hreadyq h147
  have he₀' : Exec (embTab componentReg (embTab groupReg body)) saveOriginalInput
      (mk v S) n₀ (mk v₀ S₀) := by simpa only [← hwq] using he₀
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hready₁⟩ := preparedComponentInputs_exec (body := embTab groupReg body) (q := q)
    (by omega) B tail v₀ S₀ (by simpa only [S₀,original,hwq] using hready₀) (by simpa [S₀] using h147)
  have he₁' : Exec (embTab componentReg (embTab groupReg body)) preparedComponentInputs (mk v₀ S₀) n₁ (mk v₁ S₁) := by
    simpa [← hwq,S₁,S₀,X,Y] using he₁
  have hready₁' : LengthKeyReady (2^15*p) (executionStagePrecision p l firstTarget rhsExp+1)
      q l s t u band 0 0 (cstream A w (chirpLine s B₁)++tail) (embStk componentReg S₁) := by
    simpa [← hwq,S₁,S₀,X,Y,B₁,chirpLine,List.map_map,Function.comp_def] using hready₁
  have hB₁ : ∀ i, ‖value q (B₁ i)‖ ≤ (2 : ℝ)^rhsExp := fun i =>
    (componentWords_norm_le q (B i)).1.trans (hB i)
  obtain ⟨v₂,n₂,D,R,hRsolve,hu₂,hn₂,he₂,hCreal,hCnorm,hCerror,hread,hready₂⟩ := releasedSchurResidual_spec (body := body)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad B₁ hB₁ v₁ S₁ tail
    (by simpa [S₁,S₀] using h127) (by simpa [S₁,S₀] using h138) (by simpa [S₁,S₀] using h143)
    (by simpa [S₁,S₀] using haMaster) (by simpa [S₁,S₀] using hbMaster) hready₁' (by simpa [S₁,S₀] using h147)
  let C := couplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (B i))
  let input := cstream A w (chirpLine s C)++X
  let S₂ : Stacks 148 A := {S₁ with R := Function.update S₁.R 110 input}
  let Sfinal : Stacks 148 A := {S with R := (Function.update (Function.update (Function.update S.R 110 input) 144 Y) 146 (original++S.R 146))}
  have he₂' : Exec (embTab componentReg (embTab groupReg body)) (releasedSchurResidual hR hQ)
      (mk v₁ S₁) n₂ (mk v₂ S₂) := he₂
  have hframe : S₂ = Sfinal := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h110 : k = 110 <;> by_cases h132 : k = 132 <;> by_cases h144 : k = 144 <;> by_cases h146 : k = 146 <;>
      simp [S₂,Sfinal,S₁,S₀,input,h110,h132,h144,h146]
  rw [hframe] at he₂'
  have hread' : ∀ i, publishedCellRead q w (0 : ZMod s) (S₂.R 110) i = (value q (C i)).re := hread
  rw [hframe] at hread'
  have hready₂' : LengthKeyReady (2^15*p) (executionStagePrecision p l firstTarget rhsExp+1)
      q l s t u band 0 0 input (embStk componentReg S₂) := hready₂
  rw [hframe] at hready₂'
  refine ⟨v₂,n₀+(n₁+n₂),D,R,hRsolve,hu₂.trans (hu₁.trans hu₀),
    Nat.add_le_add hn₀ (Nat.add_le_add hn₁ hn₂),
    Exec.seq he₀' (Exec.seq he₁' he₂'),hCreal,hCnorm,?_,hread',hready₂'⟩
  · intro i hi
    have hid (z : GaussianInt) : realPartWord (realPartWord z) = realPartWord z := rfl
    simpa only [B₁,hid,value_realPartWord_re] using hCerror i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
