module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleasedSchurResidual
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedSchurResidualStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResidualPrefixNativeStock

/-! Retire the executed initial interior line while retaining the residual resources. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

@[irreducible] def releasedSchurResidualWorkspace
    (J ringPush batchPush rowPush p l s t u target rhsExp a b : ℕ) : ℕ :=
  realInteriorResidualWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
    J ringPush batchPush rowPush p l s t u (initialSchurTarget p u target rhsExp) rhsExp a b+
  8*retireInitialInteriorCost (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp) s

theorem releasedSchurResidual_spec_within (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (B : ZMod s → GaussianInt)
    (hB : ∀ i, ‖value (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp) (B i)‖ ≤ (2 : ℝ)^rhsExp)
    (J ringPush batchPush : ℕ)
    (hpushJ : mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ J)
    (hpushR : mnProgPush (rpProg (P := P₀) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ ringPush)
    (hpushK : mnProgPush (cmulBlock cr
      (rmulOne (P := P₀) (Q := Q) (A := A) (U := U) mul mul_injective (by decide) hQ cr)) ≤ batchPush)
    (rowPush : ℕ) (hrowPush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ rowPush)
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
      let C := guardedCouplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (B i))
      let input := cstream A w (chirpLine s C)++S.R 110
      let S' : Stacks 148 A := {S with R := Function.update S.R 110 input}
      (∀ c, SchurDominance.Solves (realMatrix s t p u) I (R c) c) ∧
      v'.user = v.user ∧ n ≤ releasedSchurResidualCost p l s t u target rhsExp a b ∧
      ExecWithin (embTab componentReg (embTab groupReg body))
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
          releasedSchurResidualWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
            J ringPush batchPush rowPush p l s t u target rhsExp a b)
        0 (releasedSchurResidual hR hQ) (mk v S) n (mk v' S') ∧
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
  have hwq : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  obtain ⟨v₁,n₁,D,R,hRsolve,hu₁,hn₁,he₁,hCreal,hCnorm,hCerror,hread,hready₁⟩ := retainedSchurResidual_spec_within (body := body)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad B hB J ringPush batchPush hpushJ hpushR hpushK rowPush hrowPush v S tail
    h127 h138 h143 haMaster hbMaster hready
  let C := guardedCouplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (B i))
  let input := cstream A w (chirpLine s C)++S.R 110
  let output := cstream A w (chirpLine s D)++S.R 132
  let S₁ : Stacks 148 A := {S with R := Function.update (Function.update S.R 110 input) 132 output}
  have hready₁' : LengthKeyReady (2^15*p) (executionStagePrecision p l firstTarget rhsExp+1)
      q l s t u band 0 0 input (embStk componentReg S₁) := hready₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂,hready₂⟩ := retireInitialInterior_ready (body := embTab groupReg body)
    (cstream A w (chirpLine s D)) (S.R 132) input (by simp [chirpLine,hwq]) v₁ S₁ hready₁'
    (by simp [S₁,output]) (by simpa [S₁] using h147)
  let S₂ : Stacks 148 A := {S₁ with R := Function.update S₁.R 132 (S.R 132)}
  let Sfinal : Stacks 148 A := {S with R := Function.update S.R 110 input}
  have hframe : S₂ = Sfinal := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h110 : k = 110 <;> by_cases h132 : k = 132 <;>
      simp [S₂,S₁,Sfinal,h110,h132]
  have he₂' : Exec (embTab componentReg (embTab groupReg body)) retireInitialInterior
      (mk v₁ S₁) n₂ (mk v₂ S₂) := he₂
  rw [hframe] at he₂'
  have hready₂' : LengthKeyReady (2^15*p) (executionStagePrecision p l firstTarget rhsExp+1)
      q l s t u band 0 0 input (embStk componentReg S₂) := hready₂
  rw [hframe] at hready₂'
  have ht₂ := mn_native_exec_within he₂' 8 retireInitialInterior_native 0
    (mnSize (mk v₁ S₁)+0+8*retireInitialInteriorCost q s) (by omega)
  have ht := (mn_seq_within_add he₁ ht₂).mono (J := fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
      releasedSchurResidualWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
        J ringPush batchPush rowPush p l s t u target rhsExp a b) (by
    intro d z hz
    unfold releasedSchurResidualWorkspace
    exact hz)
  refine ⟨v₂,n₁+n₂,D,R,hRsolve,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,
    ht,hCreal,hCnorm,hCerror,?_,hready₂'⟩
  simpa [Sfinal,S₁,input,C,q,w,band,firstTarget] using hread

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
