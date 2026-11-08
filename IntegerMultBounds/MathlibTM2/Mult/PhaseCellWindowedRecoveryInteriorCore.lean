module

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

noncomputable def windowedRecoveryInteriorCore (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (lower upper : Fin 148) : Pr P₀ 148 Q A U :=
  .seq (ucopy lower 141 143) (.seq (ucopy upper 142 143)
    (.seq (retainedRecoveryInteriorCore hR hQ) (clearWords [141,142])))

theorem windowedRecoveryInteriorCore_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
      v'.user = v.user ∧ n ≤ (4*a+4)+((4*b+4)+(recoveryInteriorCoreCost p l s t u target rhsExp boundaryExp (couplingCountExponent p u) a b+(2*(a+b)+5))) ∧
      Exec (embTab componentReg (embTab groupReg body)) (windowedRecoveryInteriorCore hR hQ lower upper) (mk v S) n
        (mk v' {S with R := (Function.update
          (Function.update S.R 110 (cstream A w (chirpLine s R)++S.R 110))
          132 (cstream A w (chirpLine s D)++S.R 132))}) ∧
      (∀ i, ‖value q (R i)‖ ≤ (2 : ℝ)^cExp) ∧
      (∀ i, ‖value q (D i)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target cExp) ∧
      SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) xI
        (fun i => (value q (R i)).re) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t (PhaseCellBand.width p u) a b)
        (fun i => (value q (D i)).re) xI (1/(2 : ℝ)^target) := by
  dsimp only
  have hlow141 : lower ≠ 141 := by intro he; subst lower; simp at hports
  have hupp141 : upper ≠ 141 := by intro he; subst upper; simp at hports
  have hlow143 : lower ≠ 143 := by intro he; subst lower; simp at hports
  have hupp142 : upper ≠ 142 := by intro he; subst upper; simp at hports
  have hupp143 : upper ≠ 143 := by intro he; subst upper; simp at hports
  let S₁ : Stacks 148 A := {S with R := Function.update S.R 141 (List.replicate a tick)}
  let S₂ : Stacks 148 A := {S₁ with R := Function.update S₁.R 142 (List.replicate b tick)}
  obtain ⟨v₁,hv₁,he₁⟩ := ucopy_exec (embTab componentReg (embTab groupReg body))
    (a := lower) (b := 141) (t := 143) hlow141 hlow143 (by decide) v S h143
  have he₁' : Exec (embTab componentReg (embTab groupReg body)) (ucopy lower 141 143)
      (mk v S) (4*a+4) (mk v₁ S₁) := by simpa only [haSrc,h141,List.append_nil] using he₁
  obtain ⟨v₂,hv₂,he₂⟩ := ucopy_exec (embTab componentReg (embTab groupReg body))
    (a := upper) (b := 142) (t := 143) hupp142 hupp143 (by decide) v₁ S₁
    (by simpa [S₁] using h143)
  have he₂' : Exec (embTab componentReg (embTab groupReg body)) (ucopy upper 142 143)
      (mk v₁ S₁) (4*b+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,hupp141,hbSrc,h142] using he₂
  have hready₂ : LengthKeyReady (2^15*p) (executionStagePrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp+1)
      (executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp) (chirpLine s B)++tail) (embStk componentReg S₂) := by
    have hproj142 := componentProject_updateR_inner S₁ (142 : Fin 144) (List.replicate b tick)
    have hc142 : componentReg (142 : Fin 144) = (142 : Fin 148) := by decide
    rw [hc142] at hproj142
    have hproj141 := componentProject_updateR_inner S (141 : Fin 144) (List.replicate a tick)
    have hc141 : componentReg (141 : Fin 144) = (141 : Fin 148) := by decide
    rw [hc141] at hproj141
    dsimp only [S₂]
    rw [hproj142]
    dsimp only [S₁]
    rw [hproj141]
    exact (hready.update_window 141 (Or.inl rfl) _).update_window 142 (Or.inr rfl) _
  obtain ⟨v₃,m₃,D,xI,hv₃,hm₃,he₃,hnorm,hDnorm,hxI,herror⟩ := retainedRecoveryInteriorCore_spec (body := body)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad C B hB hC
    v₂ S₂ tail sourceTail hready₂ (by simp [S₂,S₁]) (by simp [S₂])
    (by simpa [S₂,S₁] using hsource) (by simpa [S₂,S₁] using h127)
    (by simpa [S₂,S₁] using h138) (by simpa [S₂,S₁] using h143)
  let q := executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp
  let w := executionWidth p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp
  let R := couplingRowField (2^15*p) q t u (PhaseCellBand.width p u) a b true C B
  let input := cstream A w (chirpLine s R)++S.R 110
  let output := cstream A w (chirpLine s D)++S.R 132
  let F : Stacks 148 A := {S₂ with R := (Function.update (Function.update S₂.R 110 input) 132 output)}
  have he₃' : Exec (embTab componentReg (embTab groupReg body)) (retainedRecoveryInteriorCore hR hQ)
      (mk v₂ S₂) m₃ (mk v₃ F) := by simpa [F,S₂,S₁,input,output,w,q,R] using he₃
  obtain ⟨v₄,hv₄,he₄⟩ := clearWords_exec (body := embTab componentReg (embTab groupReg body))
    [(141 : Fin 148),142] (by decide) v₃ F
  have hlen : ([(141 : Fin 148),142].map (fun k => (F.R k).length)).sum = a+b := by simp [F,S₂,S₁]
  have hfinal : {F with R := fun k => if k ∈ [(141 : Fin 148),142] then [] else F.R k} =
      {S with R := (Function.update (Function.update S.R 110 input) 132 output)} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h141' : k = 141
    · subst k; simp [h141]
    by_cases h142' : k = 142
    · subst k; simp [h142]
    simp [F,S₂,S₁,h141',h142',Function.update_apply]
  refine ⟨v₄,(4*a+4)+((4*b+4)+(m₃+(2*(a+b)+5))),D,xI,
    hv₄.trans (hv₃.trans (hv₂.trans hv₁)),by omega,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' he₄))).cast (by rw [hlen]; rfl)
      (congrArg (mk v₄) hfinal),hnorm,hDnorm,hxI,herror⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
