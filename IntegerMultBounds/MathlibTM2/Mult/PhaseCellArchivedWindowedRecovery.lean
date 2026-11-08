module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWindowedRecoveryInteriorCore
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinishRecoveryPass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedRecoveryInteriorCore
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWindowedSchurResidual
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedComponentInputs
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedInterior
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoredCouplingPass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoverySizing
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireAmbientSource
public import IntegerMultBounds.NLogN.PhaseCellBoundary
public import IntegerMultBounds.NLogN.SchurRecoveryError
public import IntegerMultBounds.NLogN.SchurPerturbSolve
public import IntegerMultBounds.NLogN.PhaseCellCouplingMass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupportBudget

/-! Execute the recovery coupling and interior solve independently of the surrounding principal system. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def archivedWindowedRecovery (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (lower upper : Fin 148) : Pr P₀ 148 Q A U :=
  .seq (windowedRecoveryInteriorCore hR hQ lower upper) finishRecoveryPass

theorem archivedWindowedRecovery_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (lower upper : Fin 148) (hports : [lower,upper,141,142,143].Nodup)
    {p l s t u target rhsExp boundaryExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (C B : ZMod s → GaussianInt)
    (hB : ∀ i, ‖value (executionPrecision p l
      (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp) (B i)‖ ≤ (2 : ℝ)^rhsExp)
    (hC : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b,
      ‖value (executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
        (C i)‖ ≤ (2 : ℝ)^boundaryExp)
    (v : HS 148 Q A U) (S : Stacks 148 A) (tail sourceTail : List (Fin (A+4)))
    (hready : LengthKeyReady (2^15*p)
      (executionStagePrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp+1)
      (executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
      l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l
        (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp) (chirpLine s B)++tail) (embStk componentReg S))
    (haSrc : (S.R lower).length = a) (hbSrc : (S.R upper).length = b)
    (h141 : S.R 141 = []) (h142 : S.R 142 = [])
    (hsource : S.R 132 = cstream A
      (executionWidth p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
      (chirpLine s C)++sourceTail)
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = []) :
    let q := executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp
    let w := executionWidth p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp
    let cExp := recoveryRhsExponent p rhsExp boundaryExp (couplingCountExponent p u)
    let R := couplingRowField (2^15*p) q t u (PhaseCellBand.width p u) a b true C B
    ∃ v' n, ∃ D : ZMod s → GaussianInt, ∃ xI : ZMod s → ℝ,
      v'.user = v.user ∧ n ≤ (4*a+4)+((4*b+4)+(recoveryInteriorCoreCost p l s t u target rhsExp boundaryExp (couplingCountExponent p u) a b+(2*(a+b)+5)))+
        (archiveResidualPrefixCost q s+retireAmbientSourceCost q s) ∧
      Exec (embTab componentReg (embTab groupReg body)) (archivedWindowedRecovery hR hQ lower upper) (mk v S) n
        (mk v' {S with R := Function.update S.R 147 (cstream A w (chirpLine s D)++S.R 147)}) ∧
      (∀ i, ‖value q (R i)‖ ≤ (2 : ℝ)^cExp) ∧
      (∀ i, ‖value q (D i)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target cExp) ∧
      SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) xI
        (fun i => (value q (R i)).re) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t (PhaseCellBand.width p u) a b)
        (fun i => (value q (D i)).re) xI (1/(2 : ℝ)^target) := by
  dsimp only
  let q := executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp
  let w := executionWidth p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp
  let R := couplingRowField (2^15*p) q t u (PhaseCellBand.width p u) a b true C B
  obtain ⟨v₁,m₁,D,xI,hv₁,hm₁,he₁,hnorm,hDnorm,hxI,herror⟩ := windowedRecoveryInteriorCore_spec (body := body)
    hR hQ hA lower upper hports hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad
    C B hB hC v S tail sourceTail hready haSrc hbSrc h141 h142 hsource h127 h138 h143
  let F : Stacks 148 A := {S with R := (Function.update
    (Function.update S.R 110 (cstream A w (chirpLine s R)++S.R 110))
    132 (cstream A w (chirpLine s D)++S.R 132))}
  have hw : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  have hq : (S.R 119).length = q := by
    simpa [embStk,componentReg,groupHeaderValue,q] using hready.masters (119,112) (by simp [groupHeaderCopies])
  have hs : (S.R 121).length = s := by
    simpa [embStk,componentReg,groupHeaderValue] using hready.masters (121,97) (by simp [groupHeaderCopies])
  have hclean : ∀ k ∈ ([(94 : Fin 148),131,134,135,143]), F.R k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · simpa [F,embStk,componentReg] using hready.blank 94 (by decide) (by decide) (by decide)
    · simpa [F,embStk,componentReg] using hready.fresh 131 (by simp)
    · simpa [F,embStk,componentReg] using hready.fresh 134 (by simp)
    · simpa [F,embStk,componentReg] using hready.fresh 135 (by simp)
    · simpa [F] using h143
  obtain ⟨v₂,m₂,hv₂,hm₂,he₂⟩ := finishRecoveryPass_exec (body := embTab groupReg body)
    q s (cstream A w (chirpLine s D)) (S.R 132) (cstream A w (chirpLine s R)) (S.R 110)
    (by simp [length_cstream,length_chirpLine,hw]) (by simp [length_cstream,length_chirpLine,hw])
    v₁ F (by simpa [F] using hq) (by simpa [F] using hs) (by simp [F]) (by simp [F]) hclean
  refine ⟨v₂,m₁+m₂,D,xI,hv₂.trans hv₁,Nat.add_le_add hm₁ hm₂,
    (Exec.seq he₁ he₂).cast rfl ?_,hnorm,hDnorm,hxI,herror⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h110 : k = 110 <;> by_cases h132 : k = 132 <;> by_cases h147 : k = 147 <;>
    simp [F,w,h110,h132,h147]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
